// llm9p is a 9P server that exposes LLM inference as a filesystem.
//
// This allows agents running in Inferno/NervNode to access Claude via
// standard file operations, completing the namespace-bounded architecture.
//
// Usage:
//
//	export ANTHROPIC_API_KEY=your-key
//	llm9p -addr :5641
//	mount -A tcp!localhost!5641 /n/llm  (from Inferno)
//	echo "What is 2+2?" > /n/llm/query
//	cat /n/llm/query
package main

import (
	"bytes"
	"context"
	"encoding/json"
	"flag"
	"fmt"
	"io"
	"log"
	"net"
	"net/http"
	"os"
	"os/signal"
	"strings"
	"sync"
	"syscall"
	"time"

	"github.com/NERVsystems/nerva-9p-paper/prototype/pkg/nerv9p"
)

var (
	version = "0.1.0"
	addr    = flag.String("addr", ":5641", "Address to listen on")
	model   = flag.String("model", "claude-sonnet-4-20250514", "Model to use")
	debug   = flag.Bool("debug", false, "Enable debug logging")
)

// LLMClient handles communication with Claude API
type LLMClient struct {
	apiKey       string
	model        string
	systemPrompt string
	httpClient   *http.Client
	mu           sync.RWMutex
}

type ClaudeRequest struct {
	Model     string    `json:"model"`
	MaxTokens int       `json:"max_tokens"`
	System    string    `json:"system,omitempty"`
	Messages  []Message `json:"messages"`
}

type Message struct {
	Role    string `json:"role"`
	Content string `json:"content"`
}

type ClaudeResponse struct {
	Content []struct {
		Text string `json:"text"`
	} `json:"content"`
	Usage struct {
		InputTokens  int `json:"input_tokens"`
		OutputTokens int `json:"output_tokens"`
	} `json:"usage"`
	Error *struct {
		Message string `json:"message"`
	} `json:"error,omitempty"`
}

func (c *LLMClient) Complete(userPrompt string) (string, error) {
	c.mu.RLock()
	systemPrompt := c.systemPrompt
	modelName := c.model
	c.mu.RUnlock()

	reqBody := ClaudeRequest{
		Model:     modelName,
		MaxTokens: 4096,
		System:    systemPrompt,
		Messages: []Message{
			{Role: "user", Content: userPrompt},
		},
	}

	jsonBody, err := json.Marshal(reqBody)
	if err != nil {
		return "", fmt.Errorf("failed to marshal request: %w", err)
	}

	req, err := http.NewRequest("POST", "https://api.anthropic.com/v1/messages", bytes.NewBuffer(jsonBody))
	if err != nil {
		return "", fmt.Errorf("failed to create request: %w", err)
	}

	req.Header.Set("Content-Type", "application/json")
	req.Header.Set("x-api-key", c.apiKey)
	req.Header.Set("anthropic-version", "2023-06-01")

	resp, err := c.httpClient.Do(req)
	if err != nil {
		return "", fmt.Errorf("API request failed: %w", err)
	}
	defer resp.Body.Close()

	body, err := io.ReadAll(resp.Body)
	if err != nil {
		return "", fmt.Errorf("failed to read response: %w", err)
	}

	if resp.StatusCode != 200 {
		return "", fmt.Errorf("API error %d: %s", resp.StatusCode, string(body))
	}

	var claudeResp ClaudeResponse
	if err := json.Unmarshal(body, &claudeResp); err != nil {
		return "", fmt.Errorf("failed to parse response: %w", err)
	}

	if claudeResp.Error != nil {
		return "", fmt.Errorf("API error: %s", claudeResp.Error.Message)
	}

	if len(claudeResp.Content) == 0 {
		return "", fmt.Errorf("empty response")
	}

	// Log token usage for metrics
	log.Printf("[TOKENS] input=%d output=%d total=%d",
		claudeResp.Usage.InputTokens,
		claudeResp.Usage.OutputTokens,
		claudeResp.Usage.InputTokens+claudeResp.Usage.OutputTokens)

	return claudeResp.Content[0].Text, nil
}

func (c *LLMClient) SetSystemPrompt(prompt string) {
	c.mu.Lock()
	defer c.mu.Unlock()
	c.systemPrompt = prompt
}

func (c *LLMClient) GetSystemPrompt() string {
	c.mu.RLock()
	defer c.mu.RUnlock()
	return c.systemPrompt
}

func (c *LLMClient) SetModel(m string) {
	c.mu.Lock()
	defer c.mu.Unlock()
	c.model = m
}

func (c *LLMClient) GetModel() string {
	c.mu.RLock()
	defer c.mu.RUnlock()
	return c.model
}

func main() {
	flag.Parse()

	apiKey := os.Getenv("ANTHROPIC_API_KEY")
	if apiKey == "" {
		log.Fatal("ANTHROPIC_API_KEY environment variable required")
	}

	log.Printf("llm9p server version %s", version)
	log.Printf("Model: %s", *model)

	// Create LLM client
	client := &LLMClient{
		apiKey:     apiKey,
		model:      *model,
		httpClient: &http.Client{Timeout: 120 * time.Second},
	}

	// Create root filesystem with tools directly (no service wrapper)
	root := createLLMRoot(client)

	// Create server
	srv := nerv9p.NewServer(root)
	srv.SetDebug(*debug)

	// Start listening
	listener, err := net.Listen("tcp", *addr)
	if err != nil {
		log.Fatalf("Failed to listen: %v", err)
	}
	defer listener.Close()

	log.Printf("Listening on %s", *addr)
	log.Printf("From Inferno: mount -A tcp!<host>!%s /n/llm", (*addr)[1:])

	// Handle shutdown
	ctx, cancel := context.WithCancel(context.Background())
	defer cancel()

	go func() {
		sigCh := make(chan os.Signal, 1)
		signal.Notify(sigCh, syscall.SIGINT, syscall.SIGTERM)
		<-sigCh
		log.Println("Shutting down...")
		cancel()
		listener.Close()
	}()

	// Serve
	if err := srv.Serve(ctx, listener); err != nil && err != context.Canceled {
		log.Printf("Server error: %v", err)
	}
}

// createLLMRoot creates the root filesystem with tools at top level.
// This gives us /query/query instead of /llm/query/query
func createLLMRoot(client *LLMClient) *nerv9p.RootDir {
	root := nerv9p.NewRootDir()

	// Add prompt tool - the main interface
	root.AddChild(nerv9p.NewToolDir(nerv9p.ToolConfig{
		Name:        "prompt",
		Description: "Send a prompt to the LLM and receive a response. Write your prompt, then read the response.",
		Schema: map[string]interface{}{
			"input": map[string]string{
				"type":        "string",
				"description": "The prompt to send to the LLM",
			},
		},
		Examples: []string{
			`"What is 2+2?"`,
			`"Explain quantum computing in one paragraph"`,
		},
		Handler: func(input []byte) ([]byte, error) {
			prompt := strings.TrimSpace(string(input))
			if prompt == "" {
				return nil, fmt.Errorf("empty prompt")
			}

			log.Printf("LLM query: %q", prompt)

			result, err := client.Complete(prompt)
			if err != nil {
				return nil, err
			}

			log.Printf("LLM response: %d chars", len(result))
			return []byte(result), nil
		},
	}))

	// Add system prompt tool
	root.AddChild(nerv9p.NewToolDir(nerv9p.ToolConfig{
		Name:        "system",
		Description: "Get or set the system prompt. Write to set, read to get current value.",
		Handler: func(input []byte) ([]byte, error) {
			if len(input) > 0 {
				client.SetSystemPrompt(strings.TrimSpace(string(input)))
				log.Printf("System prompt set: %q", client.GetSystemPrompt())
			}
			return []byte(client.GetSystemPrompt()), nil
		},
	}))

	// Add model tool
	root.AddChild(nerv9p.NewToolDir(nerv9p.ToolConfig{
		Name:        "model",
		Description: "Get or set the model name. Write to set, read to get current value.",
		Handler: func(input []byte) ([]byte, error) {
			if len(input) > 0 {
				client.SetModel(strings.TrimSpace(string(input)))
				log.Printf("Model set: %s", client.GetModel())
			}
			return []byte(client.GetModel() + "\n"), nil
		},
	}))

	return root
}

func init() {
	flag.Usage = func() {
		fmt.Fprintf(os.Stderr, `llm9p - LLM 9P Server

Exposes Claude API as a 9P filesystem for namespace-bounded agents.

Usage:
  llm9p [flags]

Environment:
  ANTHROPIC_API_KEY - Required API key

Flags:
`)
		flag.PrintDefaults()
		fmt.Fprintf(os.Stderr, `
Namespace structure (when mounted at /n/llm):
  /n/llm/
    query/query       - Write prompt, read response
    system/query      - Read/write system prompt
    model/query       - Read/write model name
    help              - Service overview

Example:
  export ANTHROPIC_API_KEY=sk-...
  llm9p -addr :5641

  # From Inferno/NervNode:
  mount -A tcp!127.0.0.1!5641 /n/llm
  echo "You are a helpful assistant" > /n/llm/system/query
  echo "Hello" > /n/llm/query/query
  cat /n/llm/query/query

`)
	}
}
