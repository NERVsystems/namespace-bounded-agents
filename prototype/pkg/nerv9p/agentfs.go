// Package nerv9p provides AgentFS - a Plan 9-style tool interface for LLM agents.
//
// This implements the AgentFS Tool Contract Spec v0.
package nerv9p

import (
	"bytes"
	"encoding/json"
	"fmt"
	"io"
	"strconv"
	"strings"
	"sync"
	"sync/atomic"
	"time"
)

// =============================================================================
// Error Handling (§8)
// =============================================================================

// AgentError represents a canonical error payload per §8.2
// AgentError provides structured, machine-readable error responses
// For param errors: structured fields (missing, expected, formats, hint_code)
// For exec errors: simple message field (no prose hints, just error description)
type AgentError struct {
	IsError   bool     `json:"error"`
	Code      string   `json:"code"`               // error code: missing_param, parse_error, exec_failed
	Message   string   `json:"message,omitempty"`  // simple error message (for exec_failed)
	Missing   []string `json:"missing,omitempty"`  // missing required parameters
	Expected  []string `json:"expected,omitempty"` // expected parameters in order
	Formats   []string `json:"formats,omitempty"`  // accepted formats: ["kv", "csv"]
	HintCode  string   `json:"hint_code,omitempty"` // machine-readable hint: type_b_query
	Retryable bool     `json:"retryable"`
}

// Error implements the error interface
func (e *AgentError) Error() string {
	if e.Message != "" {
		return e.Message
	}
	if len(e.Missing) > 0 {
		return fmt.Sprintf("%s: %s", e.Code, strings.Join(e.Missing, ", "))
	}
	return e.Code
}

// NewAgentError creates a simple error with message (for exec failures, etc.)
func NewAgentError(code, message string, retryable bool) *AgentError {
	return &AgentError{
		IsError:   true,
		Code:      code,
		Message:   message,
		Retryable: retryable,
	}
}

// NewParamError creates a structured parameter error for Type B tools
func NewParamError(missing []string, expected []string) *AgentError {
	return &AgentError{
		IsError:   true,
		Code:      "missing_param",
		Missing:   missing,
		Expected:  expected,
		Formats:   []string{"kv", "csv"},
		HintCode:  "type_b_query",
		Retryable: true,
	}
}

// NewParseError creates a structured parse error
func NewParseError(expected []string) *AgentError {
	return &AgentError{
		IsError:   true,
		Code:      "parse_error",
		Expected:  expected,
		Formats:   []string{"kv", "csv"},
		HintCode:  "type_b_query",
		Retryable: true,
	}
}

// NewUnknownParamError creates an error for unrecognized parameter names
func NewUnknownParamError(unknown []string, valid []string) *AgentError {
	return &AgentError{
		IsError:   true,
		Code:      "unknown_param",
		Message:   fmt.Sprintf("unknown parameter(s): %s", strings.Join(unknown, ", ")),
		Expected:  valid,
		Formats:   []string{"kv"},
		HintCode:  "type_b_query",
		Retryable: true,
	}
}

// NewFormatError creates an error for malformed parameter values
func NewFormatError(param string, hint string, expected []string) *AgentError {
	return &AgentError{
		IsError:   true,
		Code:      "format_error",
		Message:   fmt.Sprintf("%s: %s", param, hint),
		Expected:  expected,
		HintCode:  "see_example",
		Retryable: true,
	}
}

// NewInputTooLargeError creates an error for inputs exceeding bounds
func NewInputTooLargeError(param string, limit int, actual int) *AgentError {
	return &AgentError{
		IsError:   true,
		Code:      "input_too_large",
		Message:   fmt.Sprintf("%s: limit %d, got %d", param, limit, actual),
		Retryable: false,
	}
}

// Parsing bounds - defense against unbounded input
const (
	MaxParamBytes  = 65536  // 64KB max per parameter value
	MaxPointsCount = 10000  // Max points in a list parameter
)

// ErrorFormat controls how errors are formatted for LLM consumption
// Used in experiments to test which error format helps LLMs recover best
type ErrorFormat int

const (
	ErrorFormatJSON          ErrorFormat = iota // Full structured JSON (default)
	ErrorFormatTerse                            // Simple "error: message" text
	ErrorFormatStructured                       // JSON with key fields only
	ErrorFormatConversational                   // Natural language explanation (E5)
)

var globalErrorFormat ErrorFormat = ErrorFormatJSON

// SetErrorFormat configures the global error format
func SetErrorFormat(fmt ErrorFormat) {
	globalErrorFormat = fmt
}

// GetErrorFormat returns the current error format
func GetErrorFormat() ErrorFormat {
	return globalErrorFormat
}

// Bytes returns the error in the configured format
func (e *AgentError) Bytes() []byte {
	switch globalErrorFormat {
	case ErrorFormatTerse:
		return e.bytesToTerse()
	case ErrorFormatStructured:
		return e.bytesToStructured()
	case ErrorFormatConversational:
		return e.bytesToConversational()
	default:
		return e.bytesToJSON()
	}
}

// bytesToJSON returns full JSON encoding (default)
func (e *AgentError) bytesToJSON() []byte {
	data, _ := json.MarshalIndent(e, "", "  ")
	return append(data, '\n')
}

// bytesToTerse returns simple "error: message" format
func (e *AgentError) bytesToTerse() []byte {
	msg := e.Error()
	return []byte(fmt.Sprintf("error: %s\n", msg))
}

// bytesToStructured returns JSON with only essential fields
func (e *AgentError) bytesToStructured() []byte {
	// Include only fields that help LLM recover
	compact := map[string]interface{}{
		"error": true,
		"code":  e.Code,
	}
	if e.Message != "" {
		compact["message"] = e.Message
	}
	if len(e.Missing) > 0 {
		compact["missing"] = e.Missing
	}
	if len(e.Expected) > 0 {
		compact["expected"] = e.Expected
	}
	data, _ := json.Marshal(compact)
	return append(data, '\n')
}

// bytesToConversational returns natural language error explanation
func (e *AgentError) bytesToConversational() []byte {
	var sb strings.Builder

	switch e.Code {
	case "missing_param":
		sb.WriteString("I couldn't complete this because some required parameters are missing.\n\n")
		if len(e.Missing) > 0 {
			sb.WriteString("Missing: ")
			sb.WriteString(strings.Join(e.Missing, ", "))
			sb.WriteString("\n")
		}
		if len(e.Expected) > 0 {
			sb.WriteString("This tool expects: ")
			sb.WriteString(strings.Join(e.Expected, ", "))
			sb.WriteString("\n")
		}
		sb.WriteString("\nTry writing each parameter to its own file, then read the output.\n")

	case "parse_error":
		sb.WriteString("I couldn't understand the input format.\n\n")
		if len(e.Expected) > 0 {
			sb.WriteString("Expected parameters: ")
			sb.WriteString(strings.Join(e.Expected, ", "))
			sb.WriteString("\n")
		}
		sb.WriteString("\nEach parameter should be written to a separate file with that name.\n")

	case "unknown_param":
		sb.WriteString("I don't recognize one of the parameters you provided.\n\n")
		if e.Message != "" {
			sb.WriteString(e.Message)
			sb.WriteString("\n")
		}
		if len(e.Expected) > 0 {
			sb.WriteString("Valid parameters are: ")
			sb.WriteString(strings.Join(e.Expected, ", "))
			sb.WriteString("\n")
		}

	case "format_error":
		sb.WriteString("The format of one of your inputs isn't quite right.\n\n")
		if e.Message != "" {
			sb.WriteString(e.Message)
			sb.WriteString("\n")
		}
		sb.WriteString("\nCheck the _example file in the tool directory to see the expected format.\n")

	case "no_input":
		sb.WriteString("No input was provided.\n\n")
		sb.WriteString("Write your input to the appropriate file in the tool directory, then read the output.\n")

	case "exec_failed":
		sb.WriteString("The operation failed to execute.\n\n")
		if e.Message != "" {
			sb.WriteString("Reason: ")
			sb.WriteString(e.Message)
			sb.WriteString("\n")
		}
		if e.Retryable {
			sb.WriteString("\nThis might work if you try again.\n")
		}

	default:
		sb.WriteString("An error occurred: ")
		sb.WriteString(e.Error())
		sb.WriteString("\n")
	}

	return []byte(sb.String())
}

// Common error codes
var (
	ErrNoInput      = NewAgentError("no_input", "no input has been set", false)
	ErrMissingParam = NewAgentError("missing_param", "required parameter missing", false)
	ErrInvalidInput = NewAgentError("invalid_input", "invalid input format", false)
	ErrExecFailed   = NewAgentError("exec_failed", "execution failed", true)
)

// FormatAgentError converts a Go error to AgentError bytes
func FormatAgentError(err error) []byte {
	if ae, ok := err.(*AgentError); ok {
		return ae.Bytes()
	}
	return NewAgentError("error", err.Error(), true).Bytes()
}

// =============================================================================
// Provenance (§7.3)
// =============================================================================

// Provenance provides execution metadata required for poll results
type Provenance struct {
	Timestamp string `json:"timestamp"`          // RFC 3339 UTC
	ExecID    string `json:"exec_id,omitempty"`  // Optional stable execution ID
}

// NewProvenance creates provenance with current timestamp
func NewProvenance() Provenance {
	return Provenance{
		Timestamp: time.Now().UTC().Format(time.RFC3339),
		ExecID:    fmt.Sprintf("%d", time.Now().UnixNano()),
	}
}

// WrapWithProvenance wraps a result with provenance metadata
func WrapWithProvenance(result []byte) []byte {
	// Try to parse as JSON and add provenance
	var data map[string]interface{}
	if err := json.Unmarshal(result, &data); err == nil {
		data["provenance"] = NewProvenance()
		wrapped, _ := json.MarshalIndent(data, "", "  ")
		return append(wrapped, '\n')
	}

	// If not JSON object, try array
	var arr []interface{}
	if err := json.Unmarshal(result, &arr); err == nil {
		wrapper := map[string]interface{}{
			"result":     arr,
			"provenance": NewProvenance(),
		}
		wrapped, _ := json.MarshalIndent(wrapper, "", "  ")
		return append(wrapped, '\n')
	}

	// Fallback: wrap as string result
	wrapper := map[string]interface{}{
		"result":     string(bytes.TrimSpace(result)),
		"provenance": NewProvenance(),
	}
	wrapped, _ := json.MarshalIndent(wrapper, "", "  ")
	return append(wrapped, '\n')
}

// =============================================================================
// Type A Tool (§3.1, §5.1)
// =============================================================================

// TypeAHandler processes input and returns output for Type A tools
type TypeAHandler func(input []byte) (output []byte, err error)

// TypeAConfig configures a Type A tool
type TypeAConfig struct {
	Name    string       // Tool name (must match [a-z0-9_]+, <=32 chars)
	Handler TypeAHandler // The execution handler
	TTL     int64        // Cache TTL in ms (-1=indefinite, 0=no cache, >0=ms)
	Types   string       // Optional _types content (e.g., "query:string")
	Example string       // Optional _example content
}

// TypeATool implements a Type A (single-input) tool per AgentFS spec
type TypeATool struct {
	*StaticDir
	config     TypeAConfig
	mu         sync.RWMutex
	lastInput  []byte
	lastResult []byte
	lastExec   time.Time
	lastError  *AgentError
	hasInput   bool
}

// NewTypeATool creates a Type A tool directory
func NewTypeATool(cfg TypeAConfig) *TypeATool {
	tool := &TypeATool{
		StaticDir: NewStaticDir(cfg.Name),
		config:    cfg,
	}

	// query (rw) - required
	tool.AddChild(&typeAQueryFile{tool: tool})

	// poll (r) - always present for freshness support
	tool.AddChild(&typeAPollFile{tool: tool})

	// _ttl (r) - if TTL is set
	if cfg.TTL != 0 {
		ttlStr := fmt.Sprintf("%d\n", cfg.TTL)
		tool.AddChild(NewStaticFile("_ttl", []byte(ttlStr)))
	}

	// _clear (w) - for clearing state
	tool.AddChild(&typeAClearFile{tool: tool})

	// error (r) - last error
	tool.AddChild(&typeAErrorFile{tool: tool})

	// _types (r) - optional
	if cfg.Types != "" {
		tool.AddChild(NewStaticFile("_types", []byte(cfg.Types+"\n")))
	}

	// _example (r) - optional
	if cfg.Example != "" {
		tool.AddChild(NewStaticFile("_example", []byte(cfg.Example+"\n")))
	}

	return tool
}

// typeAQueryFile implements the query file (rw)
type typeAQueryFile struct {
	*BaseFile
	tool *TypeATool
}

func (f *typeAQueryFile) Stat() Stat {
	if f.BaseFile == nil {
		f.BaseFile = NewBaseFile("query", 0666)
	}
	s := f.BaseFile.Stat()
	f.tool.mu.RLock()
	s.Length = uint64(len(f.tool.lastResult))
	f.tool.mu.RUnlock()
	return s
}

func (f *typeAQueryFile) Write(p []byte, offset int64) (int, error) {
	f.tool.mu.Lock()
	defer f.tool.mu.Unlock()

	input := bytes.TrimSpace(p)
	// Must copy - the buffer may be reused by the 9P layer
	f.tool.lastInput = make([]byte, len(input))
	copy(f.tool.lastInput, input)
	f.tool.hasInput = true

	// Execute
	result, err := f.tool.config.Handler(input)
	if err != nil {
		// Preserve structured error type if handler returned AgentError
		if ae, ok := err.(*AgentError); ok {
			f.tool.lastError = ae
		} else {
			f.tool.lastError = NewAgentError("exec_failed", err.Error(), true)
		}
		f.tool.lastResult = f.tool.lastError.Bytes()
	} else {
		f.tool.lastError = nil
		f.tool.lastResult = result
	}
	f.tool.lastExec = time.Now()

	return len(p), nil
}

func (f *typeAQueryFile) Read(p []byte, offset int64) (int, error) {
	f.tool.mu.RLock()
	defer f.tool.mu.RUnlock()

	if offset >= int64(len(f.tool.lastResult)) {
		return 0, io.EOF
	}
	n := copy(p, f.tool.lastResult[offset:])
	return n, nil
}

// typeAPollFile implements the poll file (r) - re-executes with provenance
type typeAPollFile struct {
	*BaseFile
	tool *TypeATool
}

func (f *typeAPollFile) Stat() Stat {
	if f.BaseFile == nil {
		f.BaseFile = NewBaseFile("poll", 0444)
	}
	return f.BaseFile.Stat()
}

func (f *typeAPollFile) Read(p []byte, offset int64) (int, error) {
	f.tool.mu.Lock()
	defer f.tool.mu.Unlock()

	// §6.1: poll MUST fail if no input has been set
	if !f.tool.hasInput {
		errBytes := ErrNoInput.Bytes()
		if offset >= int64(len(errBytes)) {
			return 0, io.EOF
		}
		n := copy(p, errBytes[offset:])
		return n, nil
	}

	// Re-execute with current input
	result, err := f.tool.config.Handler(f.tool.lastInput)
	if err != nil {
		// Preserve structured error type if handler returned AgentError
		if ae, ok := err.(*AgentError); ok {
			f.tool.lastError = ae
		} else {
			f.tool.lastError = NewAgentError("exec_failed", err.Error(), true)
		}
		f.tool.lastResult = f.tool.lastError.Bytes()
	} else {
		f.tool.lastError = nil
		// §6.1: poll results MUST include provenance
		f.tool.lastResult = WrapWithProvenance(result)
	}
	f.tool.lastExec = time.Now()

	if offset >= int64(len(f.tool.lastResult)) {
		return 0, io.EOF
	}
	n := copy(p, f.tool.lastResult[offset:])
	return n, nil
}

// typeAClearFile implements _clear (w)
type typeAClearFile struct {
	*BaseFile
	tool *TypeATool
}

func (f *typeAClearFile) Stat() Stat {
	if f.BaseFile == nil {
		f.BaseFile = NewBaseFile("_clear", 0222)
	}
	return f.BaseFile.Stat()
}

func (f *typeAClearFile) Write(p []byte, offset int64) (int, error) {
	f.tool.mu.Lock()
	defer f.tool.mu.Unlock()

	f.tool.lastInput = nil
	f.tool.lastResult = nil
	f.tool.lastError = nil
	f.tool.hasInput = false
	f.tool.lastExec = time.Time{}

	return len(p), nil
}

// typeAErrorFile implements error (r)
type typeAErrorFile struct {
	*BaseFile
	tool *TypeATool
}

func (f *typeAErrorFile) Stat() Stat {
	if f.BaseFile == nil {
		f.BaseFile = NewBaseFile("error", 0444)
	}
	return f.BaseFile.Stat()
}

func (f *typeAErrorFile) Read(p []byte, offset int64) (int, error) {
	f.tool.mu.RLock()
	defer f.tool.mu.RUnlock()

	var content []byte
	if f.tool.lastError != nil {
		content = f.tool.lastError.Bytes()
	} else {
		content = []byte("{}\n")
	}

	if offset >= int64(len(content)) {
		return 0, io.EOF
	}
	n := copy(p, content[offset:])
	return n, nil
}

// =============================================================================
// Type B Tool (§3.2, §5.2)
// =============================================================================

// TypeBHandler processes parameters and returns output
type TypeBHandler func(params map[string]string) (output []byte, err error)

// TypeBConfig configures a Type B tool
type TypeBConfig struct {
	Name     string       // Tool name
	Params   []string     // Parameter names (order preserved)
	Required []string     // Required parameter names
	Handler  TypeBHandler // The execution handler
	TTL      int64        // Cache TTL in ms
	Types    string       // Optional _types content
	Example  string       // Optional _example content
}

// TypeBTool implements a Type B (multi-parameter) tool per AgentFS spec
type TypeBTool struct {
	*StaticDir
	config      TypeBConfig
	mu          sync.RWMutex
	params      map[string]*typeBParamFile
	lastResult  []byte
	lastExec    time.Time
	lastError   *AgentError
	lastParams  map[string]string // params at last execution
}

// NewTypeBTool creates a Type B tool directory
func NewTypeBTool(cfg TypeBConfig) *TypeBTool {
	tool := &TypeBTool{
		StaticDir:  NewStaticDir(cfg.Name),
		config:     cfg,
		params:     make(map[string]*typeBParamFile),
		lastParams: make(map[string]string),
	}

	// Parameter files (w) - §3.2 shows params as write-only
	for _, pname := range cfg.Params {
		pf := &typeBParamFile{
			BaseFile: NewBaseFile(pname, 0222), // write-only per spec
			tool:     tool,
			name:     pname,
		}
		tool.params[pname] = pf
		tool.AddChild(pf)
	}

	// query (rw) - Factotum-style key=value shim for Type B tools
	// Canonical: echo 'lat=48.8 lon=2.2 radius=500' > query
	// CSV opt-in: echo 'csv:48.8,2.2,500' > query
	tool.AddChild(&typeBQueryFile{
		BaseFile: NewBaseFile("query", 0666), // read-write
		tool:     tool,
	})

	// _params (r) - parameter order for CSV format
	// Machine-readable, prevents ordering ambiguity
	paramsContent := strings.Join(cfg.Params, "\n") + "\n"
	tool.AddChild(NewStaticFile("_params", []byte(paramsContent)))

	// result (r) - required
	tool.AddChild(&typeBResultFile{tool: tool})

	// poll (r) - for freshness
	tool.AddChild(&typeBPollFile{tool: tool})

	// _ttl (r) - if TTL is set
	if cfg.TTL != 0 {
		ttlStr := fmt.Sprintf("%d\n", cfg.TTL)
		tool.AddChild(NewStaticFile("_ttl", []byte(ttlStr)))
	}

	// _clear (w) - for clearing state
	tool.AddChild(&typeBClearFile{tool: tool})

	// error (r) - last error
	tool.AddChild(&typeBErrorFile{tool: tool})

	// _types (r) - optional
	if cfg.Types != "" {
		tool.AddChild(NewStaticFile("_types", []byte(cfg.Types+"\n")))
	}

	// _example (r) - optional
	if cfg.Example != "" {
		tool.AddChild(NewStaticFile("_example", []byte(cfg.Example+"\n")))
	}

	return tool
}

// getCurrentParams returns current parameter values
func (t *TypeBTool) getCurrentParams() map[string]string {
	params := make(map[string]string)
	for name, pf := range t.params {
		params[name] = pf.value
	}
	return params
}

// checkRequired verifies required params are set
func (t *TypeBTool) checkRequired() *AgentError {
	var missing []string
	for _, req := range t.config.Required {
		if pf, ok := t.params[req]; !ok || pf.value == "" {
			missing = append(missing, req)
		}
	}
	if len(missing) > 0 {
		return NewParamError(missing, t.config.Params)
	}
	return nil
}

// typeBParamFile implements a parameter file (w)
type typeBParamFile struct {
	*BaseFile
	tool  *TypeBTool
	name  string
	value string
}

func (f *typeBParamFile) Write(p []byte, offset int64) (int, error) {
	f.tool.mu.Lock()
	defer f.tool.mu.Unlock()
	f.value = string(bytes.TrimSpace(p))
	return len(p), nil
}

func (f *typeBParamFile) Read(p []byte, offset int64) (int, error) {
	// Write-only per spec §3.2
	return 0, ErrPermission
}

// typeBQueryFile implements a Factotum-style query shim for Type B tools
// Canonical format: key=value pairs (no prefix needed)
//   lat=48.8 lon=2.2 radius=500 category=restaurant
// Explicit CSV format (requires prefix, order from _params):
//   csv:48.8,2.2,500,restaurant
// Returns structured errors with expected params and accepted formats
type typeBQueryFile struct {
	*BaseFile
	tool *TypeBTool
}

func (f *typeBQueryFile) Write(p []byte, offset int64) (int, error) {
	f.tool.mu.Lock()
	defer f.tool.mu.Unlock()

	input := string(bytes.TrimSpace(p))
	if input == "" {
		return len(p), nil
	}

	parsed := 0

	// Format 1: Explicit CSV prefix - "csv:48.8,2.2,500,restaurant"
	// Order defined by _params file
	if strings.HasPrefix(input, "csv:") {
		csvData := strings.TrimPrefix(input, "csv:")
		parts := strings.Split(csvData, ",")
		if len(parts) == len(f.tool.config.Params) {
			for i, paramName := range f.tool.config.Params {
				if pf, ok := f.tool.params[paramName]; ok {
					pf.value = strings.TrimSpace(parts[i])
					parsed++
				}
			}
			if parsed > 0 {
				f.tool.lastError = nil
				return len(p), nil
			}
		}
		// Wrong number of CSV fields
		f.tool.lastError = NewParseError(f.tool.config.Params)
		return len(p), nil
	}

	// Format 2 (canonical): Key=value pairs - "lat=48.8 lon=2.2 radius=500 category=restaurant"
	// This is the default, no prefix needed
	pairs := strings.FieldsFunc(input, func(r rune) bool {
		return r == ' ' || r == '\n' || r == '\t'
	})

	var unknown []string
	for _, pair := range pairs {
		parts := strings.SplitN(pair, "=", 2)
		if len(parts) != 2 {
			continue
		}
		key := strings.TrimSpace(parts[0])
		value := strings.TrimSpace(parts[1])

		if pf, ok := f.tool.params[key]; ok {
			pf.value = value
			parsed++
		} else {
			// Track unknown keys - don't silently ignore
			unknown = append(unknown, key)
		}
	}

	// Reject unknown keys immediately - typos become errors, not silent failures
	if len(unknown) > 0 {
		f.tool.lastError = NewUnknownParamError(unknown, f.tool.config.Params)
		return len(p), nil
	}

	if parsed > 0 {
		f.tool.lastError = nil
		return len(p), nil
	}

	// Nothing parsed - structured error
	f.tool.lastError = NewParseError(f.tool.config.Params)
	return len(p), nil
}

func (f *typeBQueryFile) Read(p []byte, offset int64) (int, error) {
	f.tool.mu.Lock()
	defer f.tool.mu.Unlock()

	// If Write already set an error (unknown params, parse error), return empty
	// This prevents overwriting the error with exec_failed
	if f.tool.lastError != nil {
		return 0, io.EOF
	}

	// Check required params - error goes to error file, query returns empty
	if err := f.tool.checkRequired(); err != nil {
		f.tool.lastError = err
		return 0, io.EOF
	}

	// Get current params
	params := f.tool.getCurrentParams()

	// Check if params changed since last execution
	paramsChanged := false
	if len(f.tool.lastParams) != len(params) {
		paramsChanged = true
	} else {
		for k, v := range params {
			if f.tool.lastParams[k] != v {
				paramsChanged = true
				break
			}
		}
	}

	// Execute if params changed or no cached result
	if paramsChanged || f.tool.lastResult == nil {
		result, err := f.tool.config.Handler(params)
		if err != nil {
			// Preserve structured error type if handler returned AgentError
			if ae, ok := err.(*AgentError); ok {
				f.tool.lastError = ae
			} else {
				f.tool.lastError = NewAgentError("exec_failed", err.Error(), true)
			}
			f.tool.lastResult = nil
			return 0, io.EOF
		}
		f.tool.lastError = nil
		f.tool.lastResult = result
		f.tool.lastExec = time.Now()
		f.tool.lastParams = params
	}

	if offset >= int64(len(f.tool.lastResult)) {
		return 0, io.EOF
	}
	n := copy(p, f.tool.lastResult[offset:])
	return n, nil
}

// typeBResultFile implements result (r)
type typeBResultFile struct {
	*BaseFile
	tool *TypeBTool
}

func (f *typeBResultFile) Stat() Stat {
	if f.BaseFile == nil {
		f.BaseFile = NewBaseFile("result", 0444)
	}
	s := f.BaseFile.Stat()
	f.tool.mu.RLock()
	s.Length = uint64(len(f.tool.lastResult))
	f.tool.mu.RUnlock()
	return s
}

func (f *typeBResultFile) Read(p []byte, offset int64) (int, error) {
	f.tool.mu.Lock()
	defer f.tool.mu.Unlock()

	// Check required params
	if err := f.tool.checkRequired(); err != nil {
		errBytes := err.Bytes()
		if offset >= int64(len(errBytes)) {
			return 0, io.EOF
		}
		n := copy(p, errBytes[offset:])
		return n, nil
	}

	// Get current params
	params := f.tool.getCurrentParams()

	// §5.2: Server MAY cache results keyed by parameter tuple
	// Check if params changed since last execution
	paramsChanged := false
	if len(f.tool.lastParams) != len(params) {
		paramsChanged = true
	} else {
		for k, v := range params {
			if f.tool.lastParams[k] != v {
				paramsChanged = true
				break
			}
		}
	}

	// Execute if params changed or no cached result
	if paramsChanged || f.tool.lastResult == nil {
		result, err := f.tool.config.Handler(params)
		if err != nil {
			// Preserve structured error type if handler returned AgentError
			if ae, ok := err.(*AgentError); ok {
				f.tool.lastError = ae
			} else {
				f.tool.lastError = NewAgentError("exec_failed", err.Error(), true)
			}
			f.tool.lastResult = f.tool.lastError.Bytes()
		} else {
			f.tool.lastError = nil
			f.tool.lastResult = result
		}
		f.tool.lastExec = time.Now()
		f.tool.lastParams = params
	}

	if offset >= int64(len(f.tool.lastResult)) {
		return 0, io.EOF
	}
	n := copy(p, f.tool.lastResult[offset:])
	return n, nil
}

// typeBPollFile implements poll (r) - re-executes with provenance
type typeBPollFile struct {
	*BaseFile
	tool *TypeBTool
}

func (f *typeBPollFile) Stat() Stat {
	if f.BaseFile == nil {
		f.BaseFile = NewBaseFile("poll", 0444)
	}
	return f.BaseFile.Stat()
}

func (f *typeBPollFile) Read(p []byte, offset int64) (int, error) {
	f.tool.mu.Lock()
	defer f.tool.mu.Unlock()

	// Check required params
	if err := f.tool.checkRequired(); err != nil {
		errBytes := err.Bytes()
		if offset >= int64(len(errBytes)) {
			return 0, io.EOF
		}
		n := copy(p, errBytes[offset:])
		return n, nil
	}

	// Get current params and execute fresh
	params := f.tool.getCurrentParams()
	result, err := f.tool.config.Handler(params)
	if err != nil {
		// Preserve structured error type if handler returned AgentError
		if ae, ok := err.(*AgentError); ok {
			f.tool.lastError = ae
		} else {
			f.tool.lastError = NewAgentError("exec_failed", err.Error(), true)
		}
		f.tool.lastResult = f.tool.lastError.Bytes()
	} else {
		f.tool.lastError = nil
		// §6.1: poll results MUST include provenance
		f.tool.lastResult = WrapWithProvenance(result)
	}
	f.tool.lastExec = time.Now()
	f.tool.lastParams = params

	if offset >= int64(len(f.tool.lastResult)) {
		return 0, io.EOF
	}
	n := copy(p, f.tool.lastResult[offset:])
	return n, nil
}

// typeBClearFile implements _clear (w)
type typeBClearFile struct {
	*BaseFile
	tool *TypeBTool
}

func (f *typeBClearFile) Stat() Stat {
	if f.BaseFile == nil {
		f.BaseFile = NewBaseFile("_clear", 0222)
	}
	return f.BaseFile.Stat()
}

func (f *typeBClearFile) Write(p []byte, offset int64) (int, error) {
	f.tool.mu.Lock()
	defer f.tool.mu.Unlock()

	// Clear all params
	for _, pf := range f.tool.params {
		pf.value = ""
	}
	f.tool.lastResult = nil
	f.tool.lastError = nil
	f.tool.lastParams = make(map[string]string)
	f.tool.lastExec = time.Time{}

	return len(p), nil
}

// typeBErrorFile implements error (r)
type typeBErrorFile struct {
	*BaseFile
	tool *TypeBTool
}

func (f *typeBErrorFile) Stat() Stat {
	if f.BaseFile == nil {
		f.BaseFile = NewBaseFile("error", 0444)
	}
	return f.BaseFile.Stat()
}

func (f *typeBErrorFile) Read(p []byte, offset int64) (int, error) {
	f.tool.mu.RLock()
	defer f.tool.mu.RUnlock()

	var content []byte
	if f.tool.lastError != nil {
		content = f.tool.lastError.Bytes()
	} else {
		content = []byte("{}\n")
	}

	if offset >= int64(len(content)) {
		return 0, io.EOF
	}
	n := copy(p, content[offset:])
	return n, nil
}

// =============================================================================
// Session Tool with Clone Pattern (§4)
// =============================================================================

// SessionHandler creates a new session's tool implementation
type SessionHandler func(sessionID string) File

// SessionConfig configures a session-based tool
type SessionConfig struct {
	Name       string         // Tool name
	NewSession SessionHandler // Creates session directory content
	IdleTTL    int64          // Idle timeout in ms (0 = no timeout)
}

// SessionTool implements clone-based session allocation per §4
type SessionTool struct {
	*StaticDir
	config      SessionConfig
	mu          sync.RWMutex
	sessions    map[string]*sessionDir
	nextID      uint64
	idleChecker *time.Ticker
	stopIdle    chan struct{}
}

// NewSessionTool creates a session-based tool
func NewSessionTool(cfg SessionConfig) *SessionTool {
	tool := &SessionTool{
		StaticDir: NewStaticDir(cfg.Name),
		config:    cfg,
		sessions:  make(map[string]*sessionDir),
	}

	// clone (r) - required
	tool.AddChild(&sessionCloneFile{tool: tool})

	// _idle_ttl (r) - if set
	if cfg.IdleTTL > 0 {
		ttlStr := fmt.Sprintf("%d\n", cfg.IdleTTL)
		tool.AddChild(NewStaticFile("_idle_ttl", []byte(ttlStr)))

		// Start idle checker
		tool.stopIdle = make(chan struct{})
		tool.idleChecker = time.NewTicker(time.Duration(cfg.IdleTTL/2) * time.Millisecond)
		go tool.checkIdleSessions()
	}

	return tool
}

// checkIdleSessions removes expired sessions
func (t *SessionTool) checkIdleSessions() {
	for {
		select {
		case <-t.stopIdle:
			return
		case <-t.idleChecker.C:
			t.mu.Lock()
			now := time.Now()
			ttl := time.Duration(t.config.IdleTTL) * time.Millisecond
			for id, sess := range t.sessions {
				if now.Sub(sess.lastAccess) > ttl {
					delete(t.sessions, id)
					// Remove from directory listing
					t.removeSession(id)
				}
			}
			t.mu.Unlock()
		}
	}
}

func (t *SessionTool) removeSession(id string) {
	// Remove from children map and order
	delete(t.StaticDir.children, id)
	newOrder := make([]string, 0, len(t.StaticDir.order)-1)
	for _, name := range t.StaticDir.order {
		if name != id {
			newOrder = append(newOrder, name)
		}
	}
	t.StaticDir.order = newOrder
}

// Stop stops the idle checker
func (t *SessionTool) Stop() {
	if t.stopIdle != nil {
		close(t.stopIdle)
		t.idleChecker.Stop()
	}
}

// Lookup overrides to track session access
func (t *SessionTool) Lookup(name string) (File, error) {
	t.mu.Lock()
	if sess, ok := t.sessions[name]; ok {
		sess.lastAccess = time.Now()
	}
	t.mu.Unlock()
	return t.StaticDir.Lookup(name)
}

// sessionDir tracks session state
type sessionDir struct {
	*StaticDir
	lastAccess time.Time
}

// sessionCloneFile implements clone (r)
type sessionCloneFile struct {
	*BaseFile
	tool *SessionTool
}

func (f *sessionCloneFile) Stat() Stat {
	if f.BaseFile == nil {
		f.BaseFile = NewBaseFile("clone", 0444)
	}
	return f.BaseFile.Stat()
}

func (f *sessionCloneFile) Read(p []byte, offset int64) (int, error) {
	f.tool.mu.Lock()
	defer f.tool.mu.Unlock()

	// Allocate new session
	id := strconv.FormatUint(atomic.AddUint64(&f.tool.nextID, 1), 10)

	// Create session directory
	sessDir := &sessionDir{
		StaticDir:  NewStaticDir(id),
		lastAccess: time.Now(),
	}

	// Get session content from handler
	content := f.tool.config.NewSession(id)
	if dir, ok := content.(Dir); ok {
		for _, child := range dir.Children() {
			sessDir.AddChild(child)
		}
	} else {
		sessDir.AddChild(content)
	}

	f.tool.sessions[id] = sessDir
	f.tool.AddChild(sessDir.StaticDir)

	// Return session ID
	result := []byte(id + "\n")
	if offset >= int64(len(result)) {
		return 0, io.EOF
	}
	n := copy(p, result[offset:])
	return n, nil
}

// =============================================================================
// Convenience Functions
// =============================================================================

// MustValidateName validates a name matches the spec regex
func MustValidateName(name string) string {
	if len(name) > 32 {
		panic(fmt.Sprintf("name too long: %s (max 32 chars)", name))
	}
	for _, c := range name {
		if !((c >= 'a' && c <= 'z') || (c >= '0' && c <= '9') || c == '_') {
			panic(fmt.Sprintf("invalid character in name: %s (must match [a-z0-9_]+)", name))
		}
	}
	return name
}

// JSONResult formats a result as indented JSON
func JSONResult(v interface{}) []byte {
	data, err := json.MarshalIndent(v, "", "  ")
	if err != nil {
		return FormatAgentError(err)
	}
	return append(data, '\n')
}
