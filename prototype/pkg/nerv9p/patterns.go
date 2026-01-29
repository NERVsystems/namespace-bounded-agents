// patterns.go implements alternative filesystem patterns for the AgentFS experiment.
//
// Pattern B: Plan 9 Canonical (ctl/data)
//   - ctl (w): write command with positional arguments
//   - data (r): read result
//
// Pattern C: Explicit I/O
//   - input (w) or param files: write input/parameters
//   - output (r): read result
//
// These patterns avoid the "query shim" that accepts key=value encoding,
// testing whether LLMs can navigate raw filesystem structure as schema.
package nerv9p

import (
	"bytes"
	"encoding/json"
	"io"
	"strings"
	"sync"
	"time"
)

// =============================================================================
// Pattern B: Plan 9 Canonical (ctl/data)
// =============================================================================

// CtlDataHandler processes positional arguments and returns output
type CtlDataHandler func(args []string) (output []byte, err error)

// CtlDataConfig configures a ctl/data pattern tool
type CtlDataConfig struct {
	Name     string         // Tool name
	ArgNames []string       // Argument names in order (for _types)
	Required int            // Number of required arguments (from start)
	Handler  CtlDataHandler // The execution handler
	Types    string         // _types content (auto-generated if empty)
	Example  string         // _example content
}

// CtlDataTool implements the Plan 9 canonical ctl/data pattern
type CtlDataTool struct {
	*StaticDir
	config    CtlDataConfig
	mu        sync.RWMutex
	lastArgs  []string
	lastResult []byte
	lastExec  time.Time
	lastError string
}

// NewCtlDataTool creates a ctl/data pattern tool
func NewCtlDataTool(cfg CtlDataConfig) *CtlDataTool {
	tool := &CtlDataTool{
		StaticDir: NewStaticDir(cfg.Name),
		config:    cfg,
	}

	// ctl (w) - write positional arguments
	tool.AddChild(&ctlFile{
		BaseFile: NewBaseFile("ctl", 0222),
		tool:     tool,
	})

	// data (r) - read result
	tool.AddChild(&dataFile{
		BaseFile: NewBaseFile("data", 0444),
		tool:     tool,
	})

	// _types (r) - argument types in order
	types := cfg.Types
	if types == "" && len(cfg.ArgNames) > 0 {
		// Auto-generate types from arg names
		var parts []string
		for _, name := range cfg.ArgNames {
			parts = append(parts, name+":string")
		}
		types = strings.Join(parts, " ")
	}
	if types != "" {
		tool.AddChild(NewStaticFile("_types", []byte(types+"\n")))
	}

	// _example (r) - usage example
	if cfg.Example != "" {
		tool.AddChild(NewStaticFile("_example", []byte(cfg.Example+"\n")))
	}

	return tool
}

// ctlFile implements ctl (w) for writing commands
type ctlFile struct {
	*BaseFile
	tool *CtlDataTool
}

func (f *ctlFile) Write(p []byte, offset int64) (int, error) {
	f.tool.mu.Lock()
	defer f.tool.mu.Unlock()

	input := strings.TrimSpace(string(p))

	// Split on whitespace for positional arguments
	args := strings.Fields(input)
	f.tool.lastArgs = args

	// Check required arguments
	if len(args) < f.tool.config.Required {
		missing := f.tool.config.ArgNames[len(args):f.tool.config.Required]
		f.tool.lastError = formatNaturalError(
			"missing required arguments",
			missing,
			f.tool.config.ArgNames[:len(args)],
			"provide all required arguments in order",
		)
		f.tool.lastResult = nil
		return len(p), nil
	}

	// Execute handler
	result, err := f.tool.config.Handler(args)
	if err != nil {
		f.tool.lastError = formatNaturalError(
			err.Error(),
			nil,
			nil,
			"check argument values",
		)
		f.tool.lastResult = nil
		return len(p), nil
	}

	f.tool.lastResult = result
	f.tool.lastError = ""
	f.tool.lastExec = time.Now()

	return len(p), nil
}

func (f *ctlFile) Read(p []byte, offset int64) (int, error) {
	return 0, ErrPermission
}

// dataFile implements data (r) for reading results
type dataFile struct {
	*BaseFile
	tool *CtlDataTool
}

func (f *dataFile) Read(p []byte, offset int64) (int, error) {
	f.tool.mu.RLock()
	defer f.tool.mu.RUnlock()

	// Check for error
	if f.tool.lastError != "" {
		data := []byte(f.tool.lastError)
		if offset >= int64(len(data)) {
			return 0, io.EOF
		}
		n := copy(p, data[offset:])
		return n, nil
	}

	// Check for no input
	if f.tool.lastResult == nil {
		errMsg := formatNaturalError(
			"no command received",
			f.tool.config.ArgNames[:f.tool.config.Required],
			nil,
			"write command to ctl first",
		)
		if offset >= int64(len(errMsg)) {
			return 0, io.EOF
		}
		n := copy(p, []byte(errMsg)[offset:])
		return n, nil
	}

	// Return cached result
	if offset >= int64(len(f.tool.lastResult)) {
		return 0, io.EOF
	}
	n := copy(p, f.tool.lastResult[offset:])
	return n, nil
}

func (f *dataFile) Write(p []byte, offset int64) (int, error) {
	return 0, ErrPermission
}

// =============================================================================
// Pattern C: Explicit I/O (param files + output)
// =============================================================================

// ExplicitIOHandler processes named parameters and returns output
type ExplicitIOHandler func(params map[string]string) (output []byte, err error)

// ExplicitIOConfig configures an explicit I/O pattern tool
type ExplicitIOConfig struct {
	Name     string           // Tool name
	Params   []string         // Parameter names
	Required []string         // Required parameter names
	Handler  ExplicitIOHandler // The execution handler
	Types    string           // _types content
	Example  string           // _example content
}

// ExplicitIOTool implements the explicit I/O pattern
type ExplicitIOTool struct {
	*StaticDir
	config     ExplicitIOConfig
	mu         sync.RWMutex
	params     map[string]*explicitParamFile
	lastResult []byte
	lastExec   time.Time
	lastError  string
}

// NewExplicitIOTool creates an explicit I/O pattern tool
func NewExplicitIOTool(cfg ExplicitIOConfig) *ExplicitIOTool {
	tool := &ExplicitIOTool{
		StaticDir: NewStaticDir(cfg.Name),
		config:    cfg,
		params:    make(map[string]*explicitParamFile),
	}

	// Create parameter files
	for _, pname := range cfg.Params {
		pf := &explicitParamFile{
			BaseFile: NewBaseFile(pname, 0222),
			tool:     tool,
			name:     pname,
		}
		tool.params[pname] = pf
		tool.AddChild(pf)
	}

	// output (r) - read result
	tool.AddChild(&explicitOutputFile{
		BaseFile: NewBaseFile("output", 0444),
		tool:     tool,
	})

	// _types (r)
	if cfg.Types != "" {
		tool.AddChild(NewStaticFile("_types", []byte(cfg.Types+"\n")))
	}

	// _example (r)
	if cfg.Example != "" {
		tool.AddChild(NewStaticFile("_example", []byte(cfg.Example+"\n")))
	}

	return tool
}

// explicitParamFile implements a write-only parameter file
type explicitParamFile struct {
	*BaseFile
	tool  *ExplicitIOTool
	name  string
	value string
}

func (f *explicitParamFile) Write(p []byte, offset int64) (int, error) {
	f.tool.mu.Lock()
	defer f.tool.mu.Unlock()
	f.value = strings.TrimSpace(string(p))
	// Clear cached result when params change
	f.tool.lastResult = nil
	f.tool.lastError = ""
	return len(p), nil
}

func (f *explicitParamFile) Read(p []byte, offset int64) (int, error) {
	return 0, ErrPermission
}

// explicitOutputFile implements output (r) for reading results
type explicitOutputFile struct {
	*BaseFile
	tool *ExplicitIOTool
}

func (f *explicitOutputFile) Read(p []byte, offset int64) (int, error) {
	f.tool.mu.Lock()
	defer f.tool.mu.Unlock()

	// Check required parameters
	var missing []string
	var provided []string
	for _, req := range f.tool.config.Required {
		if pf, ok := f.tool.params[req]; !ok || pf.value == "" {
			missing = append(missing, req)
		} else {
			provided = append(provided, req)
		}
	}

	if len(missing) > 0 {
		errMsg := formatNaturalError(
			"missing required parameters",
			missing,
			provided,
			"write to parameter files before reading output",
		)
		if offset >= int64(len(errMsg)) {
			return 0, io.EOF
		}
		n := copy(p, []byte(errMsg)[offset:])
		return n, nil
	}

	// Execute if no cached result
	if f.tool.lastResult == nil {
		params := make(map[string]string)
		for name, pf := range f.tool.params {
			if pf.value != "" {
				params[name] = pf.value
			}
		}

		result, err := f.tool.config.Handler(params)
		if err != nil {
			f.tool.lastError = formatNaturalError(
				err.Error(),
				nil,
				nil,
				"check parameter values",
			)
		} else {
			f.tool.lastResult = result
			f.tool.lastError = ""
			f.tool.lastExec = time.Now()
		}
	}

	// Check for error
	if f.tool.lastError != "" {
		data := []byte(f.tool.lastError)
		if offset >= int64(len(data)) {
			return 0, io.EOF
		}
		n := copy(p, data[offset:])
		return n, nil
	}

	// Return result
	if offset >= int64(len(f.tool.lastResult)) {
		return 0, io.EOF
	}
	n := copy(p, f.tool.lastResult[offset:])
	return n, nil
}

func (f *explicitOutputFile) Write(p []byte, offset int64) (int, error) {
	return 0, ErrPermission
}

// =============================================================================
// Pattern C: Single Input/Output (for simple tools)
// =============================================================================

// InputOutputConfig configures a simple input/output tool
type InputOutputConfig struct {
	Name    string                             // Tool name
	Handler func(input []byte) ([]byte, error) // The execution handler
	Types   string                             // _types content
	Example string                             // _example content
}

// InputOutputTool implements a simple input/output pattern
type InputOutputTool struct {
	*StaticDir
	config     InputOutputConfig
	mu         sync.RWMutex
	lastInput  []byte
	lastResult []byte
	lastError  string
}

// NewInputOutputTool creates a simple input/output tool
func NewInputOutputTool(cfg InputOutputConfig) *InputOutputTool {
	tool := &InputOutputTool{
		StaticDir: NewStaticDir(cfg.Name),
		config:    cfg,
	}

	// input (w)
	tool.AddChild(&simpleInputFile{
		BaseFile: NewBaseFile("input", 0222),
		tool:     tool,
	})

	// output (r)
	tool.AddChild(&simpleOutputFile{
		BaseFile: NewBaseFile("output", 0444),
		tool:     tool,
	})

	// _types (r)
	if cfg.Types != "" {
		tool.AddChild(NewStaticFile("_types", []byte(cfg.Types+"\n")))
	}

	// _example (r)
	if cfg.Example != "" {
		tool.AddChild(NewStaticFile("_example", []byte(cfg.Example+"\n")))
	}

	return tool
}

type simpleInputFile struct {
	*BaseFile
	tool *InputOutputTool
}

func (f *simpleInputFile) Write(p []byte, offset int64) (int, error) {
	f.tool.mu.Lock()
	defer f.tool.mu.Unlock()

	input := bytes.TrimSpace(p)
	f.tool.lastInput = make([]byte, len(input))
	copy(f.tool.lastInput, input)

	// Execute immediately
	result, err := f.tool.config.Handler(input)
	if err != nil {
		f.tool.lastError = formatNaturalError(
			err.Error(),
			nil,
			nil,
			"check input format",
		)
		f.tool.lastResult = nil
	} else {
		f.tool.lastResult = result
		f.tool.lastError = ""
	}

	return len(p), nil
}

func (f *simpleInputFile) Read(p []byte, offset int64) (int, error) {
	return 0, ErrPermission
}

type simpleOutputFile struct {
	*BaseFile
	tool *InputOutputTool
}

func (f *simpleOutputFile) Read(p []byte, offset int64) (int, error) {
	f.tool.mu.RLock()
	defer f.tool.mu.RUnlock()

	// Check for error
	if f.tool.lastError != "" {
		data := []byte(f.tool.lastError)
		if offset >= int64(len(data)) {
			return 0, io.EOF
		}
		n := copy(p, data[offset:])
		return n, nil
	}

	// Check for no input
	if f.tool.lastResult == nil {
		errMsg := formatNaturalError(
			"no input received",
			nil,
			nil,
			"write to input file first",
		)
		if offset >= int64(len(errMsg)) {
			return 0, io.EOF
		}
		n := copy(p, []byte(errMsg)[offset:])
		return n, nil
	}

	if offset >= int64(len(f.tool.lastResult)) {
		return 0, io.EOF
	}
	n := copy(p, f.tool.lastResult[offset:])
	return n, nil
}

func (f *simpleOutputFile) Write(p []byte, offset int64) (int, error) {
	return 0, ErrPermission
}

// =============================================================================
// Natural Language Error Formatting
// =============================================================================

// formatNaturalError creates a plain-text error message that won't prime
// the LLM toward JSON responses.
func formatNaturalError(msg string, missing, provided []string, hint string) string {
	var buf strings.Builder

	buf.WriteString("error: ")
	buf.WriteString(msg)
	buf.WriteString("\n")

	if len(missing) > 0 {
		buf.WriteString("missing: ")
		buf.WriteString(strings.Join(missing, ", "))
		buf.WriteString("\n")
	}

	if len(provided) > 0 {
		buf.WriteString("provided: ")
		buf.WriteString(strings.Join(provided, ", "))
		buf.WriteString("\n")
	}

	if hint != "" {
		buf.WriteString("hint: ")
		buf.WriteString(hint)
		buf.WriteString("\n")
	}

	buf.WriteString("help: cat _example\n")

	return buf.String()
}

// FormatJSONResult formats a result as pretty-printed JSON
func FormatJSONResult(v interface{}) ([]byte, error) {
	return json.MarshalIndent(v, "", "  ")
}
