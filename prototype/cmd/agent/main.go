// agent is a Go-based AgentFS executor with deterministic rewriting.
//
// It takes a task, queries the LLM for commands, and executes them against
// the mounted 9P filesystem with automatic format canonicalization and
// single-retry error recovery.
//
// Usage:
//
//	agent -osm localhost:5640 "Find restaurants near the Eiffel Tower"
package main

import (
	"context"
	"encoding/json"
	"flag"
	"fmt"
	"io"
	"log"
	"os"
	"regexp"
	"strings"

	"9fans.net/go/plan9"
	"9fans.net/go/plan9/client"
	"github.com/NERVsystems/nerva-9p-paper/prototype/pkg/nerv9p"
	"github.com/anthropics/anthropic-sdk-go"
	"github.com/anthropics/anthropic-sdk-go/option"
)

var (
	osmAddr     = flag.String("osm", "localhost:5640", "OSM 9P server address")
	maxIters    = flag.Int("max-iters", 3, "Maximum iterations")
	verbose     = flag.Bool("v", false, "Verbose output")
	minPrompt   = flag.Bool("min-prompt", false, "Use minimal prompt (rely on runtime canonicalization)")
	noSynonyms  = flag.Bool("no-synonyms", false, "Disable synonym table in rewriter")
	logRewrites = flag.Bool("log-rewrites", false, "Log canonicalizer before/after")
	noCanon     = flag.Bool("no-canon", false, "Bypass pre-write canonicalization (for negative testing)")
)

func main() {
	flag.Parse()

	if flag.NArg() < 1 {
		fmt.Fprintln(os.Stderr, "Usage: agent [flags] <task>")
		os.Exit(1)
	}

	task := strings.Join(flag.Args(), " ")

	// Connect to OSM server via 9P
	fsys, err := client.Mount("tcp", *osmAddr)
	if err != nil {
		log.Fatalf("Failed to mount OSM: %v", err)
	}

	// Get namespace listing
	namespace := listNamespace(fsys, "/")

	// Create rewriter registry
	registry := nerv9p.NewRewriterRegistry()

	// Run agent loop
	result, err := runAgent(context.Background(), task, namespace, fsys, registry, *maxIters)
	if err != nil {
		log.Fatalf("Agent failed: %v", err)
	}

	fmt.Println(result)
}

// AgentResult contains the outcome of running the agent
type AgentResult struct {
	Success    bool   `json:"success"`
	Output     string `json:"output,omitempty"`
	Iterations int    `json:"iterations"`
	Rewrites   int    `json:"rewrites"`
	Error      string `json:"error,omitempty"`
}

func (r AgentResult) String() string {
	data, _ := json.MarshalIndent(r, "", "  ")
	return string(data)
}

func runAgent(ctx context.Context, task, namespace string, fsys *client.Fsys, registry *nerv9p.RewriterRegistry, maxIters int) (*AgentResult, error) {
	result := &AgentResult{}

	// Build prompt - minimal relies on runtime canonicalization, verbose guides LLM
	var systemPrompt string
	if *minPrompt {
		// Minimal prompt: let canonicalizer/rewriter do the work
		systemPrompt = `You are an agent. Execute tasks by writing to and reading from a 9P filesystem.
Each tool directory has a query file. Write parameters, then read the result.

Output ONLY shell commands, one per line. No explanations.
Example: echo '48.85 2.29' > /nearby/query && cat /nearby/query`
	} else {
		// Verbose prompt: guide LLM to correct format
		systemPrompt = `You are an agent that executes tasks by writing to and reading from a 9P filesystem.
The namespace shows available tools as directories. Each tool has a query file.

For simple tools (geocode, reverse, polyline_decode), write input directly:
  echo 'Eiffel Tower, Paris' > /geocode/query
  cat /geocode/query

For multi-parameter tools (nearby, distance, etc), use key=value pairs:
  echo 'lat=48.85 lon=2.29 radius=500 category=restaurant' > /nearby/query
  cat /nearby/query

For list parameters (points in centroid/bbox), use semicolon separator:
  echo 'points=48.85,2.29;48.86,2.34;48.87,2.30' > /centroid/query
  cat /centroid/query

Output ONLY shell commands, one per line. No explanations.`
	}

	userPrompt := fmt.Sprintf("Namespace:\n%s\n\nTask: %s", namespace, task)

	// Query LLM for commands
	llmClient := anthropic.NewClient(option.WithAPIKey(os.Getenv("ANTHROPIC_API_KEY")))

	for iter := 1; iter <= maxIters; iter++ {
		result.Iterations = iter

		if *verbose {
			log.Printf("=== Iteration %d/%d ===", iter, maxIters)
		}

		// Get commands from LLM
		resp, err := llmClient.Messages.New(ctx, anthropic.MessageNewParams{
			Model:     "claude-sonnet-4-20250514",
			MaxTokens: 1024,
			System: []anthropic.TextBlockParam{
				{Text: systemPrompt},
			},
			Messages: []anthropic.MessageParam{
				anthropic.NewUserMessage(anthropic.NewTextBlock(userPrompt)),
			},
		})
		if err != nil {
			result.Error = fmt.Sprintf("LLM error: %v", err)
			return result, nil
		}

		// Extract commands from response
		var commands string
		for _, block := range resp.Content {
			if block.Type == "text" {
				commands = block.Text
				break
			}
		}

		if *verbose {
			log.Printf("LLM response:\n%s", commands)
		}

		// Parse and execute commands
		output, rewritten, err := executeCommands(ctx, commands, fsys, registry)
		if rewritten {
			result.Rewrites++
		}

		if err != nil {
			// Add error context to next prompt
			userPrompt = fmt.Sprintf("Previous attempt failed: %v\n\nNamespace:\n%s\n\nTask: %s", err, namespace, task)
			continue
		}

		if output != "" && !isErrorOutput(output) {
			result.Success = true
			result.Output = output
			return result, nil
		}

		// Empty or error output - add to context
		userPrompt = fmt.Sprintf("Previous result was empty or error. Try a different approach.\n\nNamespace:\n%s\n\nTask: %s", namespace, task)
	}

	result.Error = "Max iterations reached"
	return result, nil
}

func executeCommands(ctx context.Context, commands string, fsys *client.Fsys, registry *nerv9p.RewriterRegistry) (string, bool, error) {
	// Extract echo > file patterns
	writeRe := regexp.MustCompile(`echo\s+'([^']+)'\s*>\s*(\S+)`)
	readRe := regexp.MustCompile(`cat\s+(\S+)`)

	var lastOutput string
	var didRewrite bool

	// Track last written input per tool path for retry
	// For query file: stores the full input
	// For param files: accumulates param=value pairs
	lastWritten := make(map[string]string)
	paramWrites := make(map[string]map[string]string) // tool -> param -> value

	lines := strings.Split(commands, "\n")
	for _, line := range lines {
		line = strings.TrimSpace(line)
		if line == "" || strings.HasPrefix(line, "#") {
			continue
		}

		// Check for write command
		if m := writeRe.FindStringSubmatch(line); m != nil {
			input := m[1]
			path := m[2]

			// Extract tool path and target file
			toolPath := extractToolPath(path)
			targetFile := extractFileName(path)

			// Only canonicalize when writing to 'query' file
			// Individual param files (lat, lon, etc.) should receive raw values
			// --no-canon bypasses canonicalization for negative testing
			if targetFile == "query" && !*noCanon {
				params := readParams(fsys, toolPath)
				if len(params) > 0 {
					canonical := nerv9p.CanonicalizeInput(input, params)
					if canonical != input {
						if *verbose || *logRewrites {
							log.Printf("CANONICALIZE: tool=%s params=%v", toolPath, params)
							log.Printf("  LLM proposed: %q", input)
							log.Printf("  Canonical:    %q", canonical)
						}
						input = canonical
						didRewrite = true
					}
				}
			}

			// Track what we wrote for potential retry
			if targetFile == "query" {
				lastWritten[toolPath] = input
			} else {
				// Track individual param writes for error recovery
				if paramWrites[toolPath] == nil {
					paramWrites[toolPath] = make(map[string]string)
				}
				paramWrites[toolPath][targetFile] = input
				// Reconstruct full input from all params
				var parts []string
				for param, val := range paramWrites[toolPath] {
					parts = append(parts, fmt.Sprintf("%s=%s", param, val))
				}
				lastWritten[toolPath] = strings.Join(parts, " ")
			}

			// Write to file
			if err := writeFile(fsys, path, input); err != nil {
				return "", didRewrite, fmt.Errorf("write %s: %w", path, err)
			}

			if *verbose {
				log.Printf("Wrote to %s: %s", path, input)
			}
		}

		// Check for read command
		if m := readRe.FindStringSubmatch(line); m != nil {
			path := m[1]

			output, err := readFile(fsys, path)
			if err != nil {
				return "", didRewrite, fmt.Errorf("read %s: %w", path, err)
			}

			lastOutput = output

			// Check for error and attempt single rewrite retry
			if isErrorOutput(output) {
				toolPath := extractToolPath(path)
				errPayload := parseErrorFromOutput(output)

				if errPayload != nil && errPayload.Retryable {
					rw := registry.Get(errPayload.Code)
					originalInput := lastWritten[toolPath]

					if rw != nil && originalInput != "" {
						// Read _params and _example
						params := readParams(fsys, toolPath)
						example := readExample(fsys, toolPath)

						if *verbose || *logRewrites {
							log.Printf("REWRITE: tool=%s error=%s retryable=%v", toolPath, errPayload.Code, errPayload.Retryable)
							log.Printf("  Original:  %q", originalInput)
							log.Printf("  Expected:  %v", errPayload.Expected)
							log.Printf("  Missing:   %v", errPayload.Missing)
						}

						// Attempt rewrite
						result, rwErr := rw.Rewrite(originalInput, *errPayload, params, example)
						if rwErr == nil && result.DidRewrite && !result.Terminal {
							if *verbose || *logRewrites {
								log.Printf("  Rewritten: %q", result.RewrittenInput)
							}

							// Write rewritten input
							queryPath := toolPath + "/query"
							if err := writeFile(fsys, queryPath, result.RewrittenInput); err != nil {
								return "", true, fmt.Errorf("rewrite write %s: %w", queryPath, err)
							}

							// Read result again
							retryOutput, retryErr := readFile(fsys, path)
							if retryErr == nil {
								lastOutput = retryOutput
								didRewrite = true

								if *verbose {
									log.Printf("Retry result: %s", truncate(retryOutput, 200))
								}
							}
						} else if result.Terminal {
							if *verbose {
								log.Printf("Rewrite terminal, no retry")
							}
						}
					}
				}
			}

			if *verbose {
				log.Printf("Read from %s: %s", path, truncate(output, 200))
			}
		}
	}

	return lastOutput, didRewrite, nil
}

func listNamespace(fsys *client.Fsys, path string) string {
	var buf strings.Builder

	var walk func(path string, depth int)
	walk = func(path string, depth int) {
		if depth > 3 {
			return
		}

		fid, err := fsys.Open(path, plan9.OREAD)
		if err != nil {
			return
		}
		defer fid.Close()

		entries, err := fid.Dirreadall()
		if err != nil {
			return
		}

		indent := strings.Repeat("  ", depth)
		for _, e := range entries {
			name := e.Name
			if strings.HasPrefix(name, ".") {
				continue
			}

			if e.Mode&plan9.DMDIR != 0 {
				fmt.Fprintf(&buf, "%s%s/\n", indent, name)
				subPath := path
				if subPath == "/" {
					subPath = "/" + name
				} else {
					subPath = path + "/" + name
				}
				walk(subPath, depth+1)
			} else {
				fmt.Fprintf(&buf, "%s%s\n", indent, name)
			}
		}
	}

	walk(path, 0)
	return buf.String()
}

func writeFile(fsys *client.Fsys, path string, content string) error {
	fid, err := fsys.Open(path, plan9.OWRITE|plan9.OTRUNC)
	if err != nil {
		return err
	}
	defer fid.Close()

	_, err = fid.Write([]byte(content))
	return err
}

func readFile(fsys *client.Fsys, path string) (string, error) {
	fid, err := fsys.Open(path, plan9.OREAD)
	if err != nil {
		return "", err
	}
	defer fid.Close()

	data, err := io.ReadAll(fid)
	if err != nil {
		return "", err
	}
	return string(data), nil
}

func readParams(fsys *client.Fsys, toolPath string) []string {
	content, err := readFile(fsys, toolPath+"/_params")
	if err != nil {
		return nil
	}
	return strings.Fields(strings.TrimSpace(content))
}

func readExample(fsys *client.Fsys, toolPath string) string {
	content, err := readFile(fsys, toolPath+"/_example")
	if err != nil {
		return ""
	}
	return strings.TrimSpace(content)
}

func extractToolPath(filePath string) string {
	// /nearby/query -> /nearby
	parts := strings.Split(filePath, "/")
	if len(parts) > 1 {
		return strings.Join(parts[:len(parts)-1], "/")
	}
	return filePath
}

func extractFileName(filePath string) string {
	// /nearby/query -> query
	parts := strings.Split(filePath, "/")
	if len(parts) > 0 {
		return parts[len(parts)-1]
	}
	return filePath
}

func isErrorOutput(output string) bool {
	return strings.Contains(output, `"error": true`) || strings.Contains(output, `"error":true`)
}

func parseErrorFromOutput(output string) *nerv9p.ErrorPayload {
	var ep nerv9p.ErrorPayload
	if err := json.Unmarshal([]byte(output), &ep); err != nil {
		return nil
	}
	if !ep.Error {
		return nil
	}
	return &ep
}

func truncate(s string, n int) string {
	if len(s) <= n {
		return s
	}
	return s[:n] + "..."
}
