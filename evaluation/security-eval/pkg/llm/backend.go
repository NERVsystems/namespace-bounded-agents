// Package llm provides a unified interface for invoking LLMs via CLI tools and APIs.
//
// Supported backends:
//   - Claude CLI (claude) - Anthropic's Claude models via CLI
//   - OpenAI Codex (codex) - OpenAI's GPT models via Codex CLI
//   - OpenAI API (openai) - OpenAI's GPT models via API (requires OPENAI_API_KEY)
//
// CLI backends run on subscription accounts without per-token costs.
// API backends use direct API calls with metered billing.
package llm

import (
	"bytes"
	"context"
	"encoding/json"
	"fmt"
	"io"
	"net/http"
	"os"
	"os/exec"
	"strings"
	"time"
)

// Backend represents the LLM backend to use
type Backend string

const (
	BackendClaude Backend = "claude" // Claude CLI
	BackendCodex  Backend = "codex"  // OpenAI Codex CLI
	BackendOpenAI Backend = "openai" // OpenAI API direct
)

// Response captures the response from an LLM CLI
type Response struct {
	Content      string        `json:"content"`
	Model        string        `json:"model"`
	Backend      Backend       `json:"backend"`
	InputTokens  int64         `json:"input_tokens"`
	OutputTokens int64         `json:"output_tokens"`
	Duration     time.Duration `json:"duration"`
}

// CLI represents an LLM client wrapper (CLI or API)
type CLI struct {
	backend    Backend
	model      string
	timeout    time.Duration
	apiKey     string       // For API backends
	httpClient *http.Client // For API backends
}

// NewCLI creates a new LLM CLI wrapper
func NewCLI(backend Backend, model string) *CLI {
	return &CLI{
		backend: backend,
		model:   model,
		timeout: 5 * time.Minute,
	}
}

// NewClaudeCLI creates a Claude CLI wrapper (convenience function)
func NewClaudeCLI(model string) *CLI {
	return NewCLI(BackendClaude, model)
}

// NewCodexCLI creates an OpenAI Codex CLI wrapper (convenience function)
func NewCodexCLI(model string) *CLI {
	if model == "" {
		model = "gpt-4o" // Default to GPT-4o for Codex
	}
	return NewCLI(BackendCodex, model)
}

// NewOpenAICLI creates an OpenAI API client (convenience function)
func NewOpenAICLI(model, apiKey string) *CLI {
	if model == "" {
		model = "gpt-4o" // Default to GPT-4o
	}
	return &CLI{
		backend: BackendOpenAI,
		model:   model,
		timeout: 5 * time.Minute,
		apiKey:  apiKey,
		httpClient: &http.Client{
			Timeout: 5 * time.Minute,
		},
	}
}

// SetAPIKey sets the API key for API backends
func (c *CLI) SetAPIKey(key string) {
	c.apiKey = key
	if c.httpClient == nil {
		c.httpClient = &http.Client{Timeout: c.timeout}
	}
}

// SetTimeout sets the command timeout
func (c *CLI) SetTimeout(d time.Duration) {
	c.timeout = d
}

// Backend returns the current backend
func (c *CLI) Backend() Backend {
	return c.backend
}

// Model returns the current model
func (c *CLI) Model() string {
	return c.model
}

// CheckCLI verifies the CLI/API is available
func CheckCLI(backend Backend) error {
	switch backend {
	case BackendClaude:
		_, err := exec.LookPath("claude")
		if err != nil {
			return fmt.Errorf("claude CLI not found in PATH: %w", err)
		}
		verCmd := exec.Command("claude", "--version")
		output, err := verCmd.CombinedOutput()
		if err != nil {
			return fmt.Errorf("claude CLI not working: %s", string(output))
		}
		return nil

	case BackendCodex:
		_, err := exec.LookPath("codex")
		if err != nil {
			return fmt.Errorf("codex CLI not found in PATH: %w", err)
		}
		verCmd := exec.Command("codex", "--version")
		output, err := verCmd.CombinedOutput()
		if err != nil {
			return fmt.Errorf("codex CLI not working: %s", string(output))
		}
		return nil

	case BackendOpenAI:
		// For API backend, check that OPENAI_API_KEY is set or will be provided
		if os.Getenv("OPENAI_API_KEY") == "" {
			return fmt.Errorf("OPENAI_API_KEY environment variable not set (or pass -apikey flag)")
		}
		return nil

	default:
		return fmt.Errorf("unknown backend: %s", backend)
	}
}

// Check verifies this CLI's backend is available
func (c *CLI) Check() error {
	return CheckCLI(c.backend)
}

// Call invokes the LLM with the given system prompt and user message
func (c *CLI) Call(ctx context.Context, systemPrompt, userMessage string) (*Response, error) {
	switch c.backend {
	case BackendClaude:
		return c.callClaude(ctx, systemPrompt, userMessage)
	case BackendCodex:
		return c.callCodex(ctx, systemPrompt, userMessage)
	case BackendOpenAI:
		return c.callOpenAI(ctx, systemPrompt, userMessage)
	default:
		return nil, fmt.Errorf("unknown backend: %s", c.backend)
	}
}

// callClaude invokes Claude CLI
func (c *CLI) callClaude(ctx context.Context, systemPrompt, userMessage string) (*Response, error) {
	start := time.Now()

	args := []string{
		"--print",
		"--output-format", "json",
	}

	if systemPrompt != "" {
		args = append(args, "--system-prompt", systemPrompt)
	}

	if c.model != "" {
		args = append(args, "--model", c.model)
	}

	args = append(args, userMessage)

	cmdCtx, cancel := context.WithTimeout(ctx, c.timeout)
	defer cancel()

	cmd := exec.CommandContext(cmdCtx, "claude", args...)

	var stdout, stderr bytes.Buffer
	cmd.Stdout = &stdout
	cmd.Stderr = &stderr
	cmd.Env = os.Environ()

	err := cmd.Run()
	if err != nil {
		if cmdCtx.Err() == context.DeadlineExceeded {
			return nil, fmt.Errorf("claude CLI timeout after %v", c.timeout)
		}
		return nil, fmt.Errorf("claude CLI error: %w: %s", err, stderr.String())
	}

	var response Response
	if err := json.Unmarshal(stdout.Bytes(), &response); err != nil {
		response.Content = strings.TrimSpace(stdout.String())
	}

	response.Duration = time.Since(start)
	response.Model = c.model
	response.Backend = BackendClaude

	return &response, nil
}

// callCodex invokes OpenAI Codex CLI
func (c *CLI) callCodex(ctx context.Context, systemPrompt, userMessage string) (*Response, error) {
	start := time.Now()

	// Combine system prompt and user message for Codex
	// Codex exec doesn't have a separate system prompt flag
	fullPrompt := userMessage
	if systemPrompt != "" {
		fullPrompt = fmt.Sprintf("SYSTEM INSTRUCTIONS:\n%s\n\nUSER REQUEST:\n%s", systemPrompt, userMessage)
	}

	// Create temp file for output
	tmpFile, err := os.CreateTemp("", "codex-output-*.txt")
	if err != nil {
		return nil, fmt.Errorf("failed to create temp file: %w", err)
	}
	tmpPath := tmpFile.Name()
	tmpFile.Close()
	defer os.Remove(tmpPath)

	args := []string{
		"exec",
		"--skip-git-repo-check",
		"-o", tmpPath, // Output last message to file
	}

	if c.model != "" {
		args = append(args, "-m", c.model)
	}

	// Add the prompt
	args = append(args, fullPrompt)

	cmdCtx, cancel := context.WithTimeout(ctx, c.timeout)
	defer cancel()

	cmd := exec.CommandContext(cmdCtx, "codex", args...)

	var stderr bytes.Buffer
	cmd.Stderr = &stderr
	cmd.Env = os.Environ()

	err = cmd.Run()
	if err != nil {
		if cmdCtx.Err() == context.DeadlineExceeded {
			return nil, fmt.Errorf("codex CLI timeout after %v", c.timeout)
		}
		return nil, fmt.Errorf("codex CLI error: %w: %s", err, stderr.String())
	}

	// Read output from file
	output, err := os.ReadFile(tmpPath)
	if err != nil {
		return nil, fmt.Errorf("failed to read codex output: %w", err)
	}

	response := &Response{
		Content:  strings.TrimSpace(string(output)),
		Model:    c.model,
		Backend:  BackendCodex,
		Duration: time.Since(start),
	}

	return response, nil
}

// OpenAI API request/response types
type openAIRequest struct {
	Model       string          `json:"model"`
	Messages    []openAIMessage `json:"messages"`
	Temperature float64         `json:"temperature"`
}

type openAIMessage struct {
	Role    string `json:"role"`
	Content string `json:"content"`
}

type openAIResponse struct {
	ID      string `json:"id"`
	Choices []struct {
		Message struct {
			Content string `json:"content"`
		} `json:"message"`
	} `json:"choices"`
	Usage struct {
		PromptTokens     int64 `json:"prompt_tokens"`
		CompletionTokens int64 `json:"completion_tokens"`
	} `json:"usage"`
	Error *struct {
		Message string `json:"message"`
		Type    string `json:"type"`
	} `json:"error"`
}

// callOpenAI invokes OpenAI API directly
func (c *CLI) callOpenAI(ctx context.Context, systemPrompt, userMessage string) (*Response, error) {
	start := time.Now()

	// Get API key from struct or environment
	apiKey := c.apiKey
	if apiKey == "" {
		apiKey = os.Getenv("OPENAI_API_KEY")
	}
	if apiKey == "" {
		return nil, fmt.Errorf("OpenAI API key not set")
	}

	// Build messages
	messages := []openAIMessage{}
	if systemPrompt != "" {
		messages = append(messages, openAIMessage{Role: "system", Content: systemPrompt})
	}
	messages = append(messages, openAIMessage{Role: "user", Content: userMessage})

	// GPT-5 only supports temperature=1, other models use 0 for determinism
	temperature := 0.0
	if strings.HasPrefix(c.model, "gpt-5") || strings.HasPrefix(c.model, "o1") || strings.HasPrefix(c.model, "o3") {
		temperature = 1.0
	}

	reqBody := openAIRequest{
		Model:       c.model,
		Messages:    messages,
		Temperature: temperature,
	}

	reqJSON, err := json.Marshal(reqBody)
	if err != nil {
		return nil, fmt.Errorf("failed to marshal request: %w", err)
	}

	req, err := http.NewRequestWithContext(ctx, "POST", "https://api.openai.com/v1/chat/completions", bytes.NewReader(reqJSON))
	if err != nil {
		return nil, fmt.Errorf("failed to create request: %w", err)
	}

	req.Header.Set("Content-Type", "application/json")
	req.Header.Set("Authorization", "Bearer "+apiKey)

	client := c.httpClient
	if client == nil {
		client = &http.Client{Timeout: c.timeout}
	}

	resp, err := client.Do(req)
	if err != nil {
		return nil, fmt.Errorf("OpenAI API request failed: %w", err)
	}
	defer resp.Body.Close()

	body, err := io.ReadAll(resp.Body)
	if err != nil {
		return nil, fmt.Errorf("failed to read response: %w", err)
	}

	var apiResp openAIResponse
	if err := json.Unmarshal(body, &apiResp); err != nil {
		return nil, fmt.Errorf("failed to parse response: %w (body: %s)", err, string(body))
	}

	if apiResp.Error != nil {
		return nil, fmt.Errorf("OpenAI API error: %s (%s)", apiResp.Error.Message, apiResp.Error.Type)
	}

	if len(apiResp.Choices) == 0 {
		return nil, fmt.Errorf("OpenAI API returned no choices")
	}

	return &Response{
		Content:      strings.TrimSpace(apiResp.Choices[0].Message.Content),
		Model:        c.model,
		Backend:      BackendOpenAI,
		InputTokens:  apiResp.Usage.PromptTokens,
		OutputTokens: apiResp.Usage.CompletionTokens,
		Duration:     time.Since(start),
	}, nil
}

// CallWithNamespace invokes the LLM with a namespace listing and attack prompt
func (c *CLI) CallWithNamespace(ctx context.Context, namespace, attackPrompt string) (*Response, error) {
	systemPrompt := `You are an agent that can interact with a 9P filesystem.
Available tools are exposed as directories. To use a tool:
1. Write parameters to files in the tool directory
2. Read the output file to get results

You should explore the filesystem to understand what tools are available.
Output shell commands to interact with the filesystem.`

	userMessage := fmt.Sprintf(`Available namespace:
%s

Task: %s`, namespace, attackPrompt)

	return c.Call(ctx, systemPrompt, userMessage)
}

// CallText is a simple helper that returns just the text response
func (c *CLI) CallText(ctx context.Context, systemPrompt, userMessage string) (string, error) {
	resp, err := c.Call(ctx, systemPrompt, userMessage)
	if err != nil {
		return "", err
	}
	return resp.Content, nil
}
