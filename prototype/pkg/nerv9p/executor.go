package nerv9p

import (
	"context"
	"encoding/json"
	"fmt"
	"os"
	"path/filepath"
	"strings"
)

// ExecuteResult contains the outcome of a tool execution.
type ExecuteResult struct {
	Output     []byte
	Iterations int
	Rewrote    bool
	Error      *ErrorPayload
}

// isErrorResponse checks if output is a JSON error response
func isErrorResponse(data []byte) bool {
	if len(data) == 0 {
		return true
	}

	var check struct {
		Error bool `json:"error"`
	}
	if err := json.Unmarshal(data, &check); err != nil {
		return false
	}
	return check.Error
}

// =============================================================================
// LocalExecutor (filesystem-based, for testing and integration)
// =============================================================================

// LocalExecutor executes tools via local filesystem (for testing)
type LocalExecutor struct {
	basePath string
	registry *RewriterRegistry
}

// NewLocalExecutor creates an executor that uses local filesystem
func NewLocalExecutor(basePath string) *LocalExecutor {
	return &LocalExecutor{
		basePath: basePath,
		registry: NewRewriterRegistry(),
	}
}

// Execute runs a tool with deterministic rewriting
func (e *LocalExecutor) Execute(ctx context.Context, toolName string, rawInput string) (*ExecuteResult, error) {
	result := &ExecuteResult{Iterations: 1}
	toolPath := filepath.Join(e.basePath, toolName)

	// Read _params
	params := e.readLocalParams(toolPath)

	// Canonicalise to kv
	canonicalInput := CanonicalizeInput(rawInput, params)

	// First attempt
	output, err := e.localWriteThenRead(toolPath, canonicalInput)
	if err == nil && len(output) > 0 && !isErrorResponse(output) {
		result.Output = output
		return result, nil
	}

	// Read error
	errPayload, readErr := e.readLocalError(toolPath)
	if readErr != nil {
		return nil, fmt.Errorf("read error: %w", readErr)
	}

	result.Error = errPayload

	if !errPayload.Retryable {
		return result, fmt.Errorf("terminal: %s", errPayload.Code)
	}

	rewriter := e.registry.Get(errPayload.Code)
	if rewriter == nil {
		return result, fmt.Errorf("no rewriter: %s", errPayload.Code)
	}

	example := e.readLocalExample(toolPath)
	rr, rwErr := rewriter.Rewrite(canonicalInput, *errPayload, params, example)
	if rwErr != nil || rr.Terminal || !rr.DidRewrite {
		return result, fmt.Errorf("rewrite failed")
	}

	result.Iterations = 2
	result.Rewrote = true

	output2, err2 := e.localWriteThenRead(toolPath, rr.RewrittenInput)
	if err2 == nil && len(output2) > 0 && !isErrorResponse(output2) {
		result.Output = output2
		return result, nil
	}

	return result, fmt.Errorf("retry failed")
}

func (e *LocalExecutor) localWriteThenRead(toolPath, input string) ([]byte, error) {
	queryPath := filepath.Join(toolPath, "query")

	if err := os.WriteFile(queryPath, []byte(input), 0644); err != nil {
		return nil, err
	}

	return os.ReadFile(queryPath)
}

func (e *LocalExecutor) readLocalError(toolPath string) (*ErrorPayload, error) {
	data, err := os.ReadFile(filepath.Join(toolPath, "error"))
	if err != nil {
		return nil, err
	}
	return ParseErrorPayload(data)
}

func (e *LocalExecutor) readLocalParams(toolPath string) []string {
	data, err := os.ReadFile(filepath.Join(toolPath, "_params"))
	if err != nil {
		return nil
	}
	return strings.Fields(strings.TrimSpace(string(data)))
}

func (e *LocalExecutor) readLocalExample(toolPath string) string {
	data, err := os.ReadFile(filepath.Join(toolPath, "_example"))
	if err != nil {
		return ""
	}
	return strings.TrimSpace(string(data))
}
