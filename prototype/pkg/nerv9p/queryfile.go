package nerv9p

import (
	"bytes"
	"encoding/json"
	"io"
	"sync"
)

// QueryHandler is a function that processes input and returns output.
// This is the core abstraction for LLM-friendly file operations.
type QueryHandler func(input []byte) (output []byte, err error)

// QueryFile implements a write-then-read pattern ideal for LLM interaction.
// Write your query, then read the result.
type QueryFile struct {
	*BaseFile
	handler QueryHandler
	mu      sync.RWMutex
	result  []byte
}

// NewQueryFile creates a new query file with the given handler
func NewQueryFile(name string, handler QueryHandler) *QueryFile {
	return &QueryFile{
		BaseFile: NewBaseFile(name, 0666),
		handler:  handler,
	}
}

func (f *QueryFile) Write(p []byte, offset int64) (int, error) {
	f.mu.Lock()
	defer f.mu.Unlock()

	// Execute the query
	result, err := f.handler(bytes.TrimSpace(p))
	if err != nil {
		// Return error as JSON for LLM parsing
		f.result = formatError(err)
	} else {
		f.result = result
	}
	f.SetLength(uint64(len(f.result)))

	return len(p), nil
}

func (f *QueryFile) Read(p []byte, offset int64) (int, error) {
	f.mu.RLock()
	defer f.mu.RUnlock()

	if offset >= int64(len(f.result)) {
		return 0, io.EOF
	}

	n := copy(p, f.result[offset:])
	return n, nil
}

// formatError creates an LLM-friendly error response
func formatError(err error) []byte {
	resp := map[string]interface{}{
		"error":   true,
		"message": err.Error(),
	}
	// Add suggestions based on error type
	if err == ErrNotFound {
		resp["suggestion"] = "Check the path exists with ls"
	} else if err == ErrPermission {
		resp["suggestion"] = "This file may be read-only or write-only"
	}

	data, _ := json.MarshalIndent(resp, "", "  ")
	return data
}

// ToolDir creates an LLM-friendly directory for a single tool.
// It contains:
//   - query: the main query file (write input, read output)
//   - schema: describes the expected input format
//   - description: human-readable description
type ToolDir struct {
	*StaticDir
}

// ToolConfig defines an LLM tool exposed via 9P
type ToolConfig struct {
	Name        string            // tool name
	Description string            // human-readable description
	Schema      interface{}       // JSON schema for input (or nil)
	Handler     QueryHandler      // the actual handler
	Examples    []string          // example inputs
}

// NewToolDir creates a new tool directory.
// Contains only the query file - the path IS the schema.
func NewToolDir(cfg ToolConfig) *ToolDir {
	dir := &ToolDir{
		StaticDir: NewStaticDir(cfg.Name),
	}

	// Only the query file - no description, no schema
	// The filesystem path is self-documenting
	dir.AddChild(NewQueryFile("query", cfg.Handler))

	return dir
}

// ServiceDir creates a top-level directory for a service (like /osm/).
// Contains only tool directories - no help, no metadata.
type ServiceDir struct {
	*StaticDir
}

// NewServiceDir creates a new service directory
func NewServiceDir(name string) *ServiceDir {
	return &ServiceDir{
		StaticDir: NewStaticDir(name),
	}
}

// AddTool adds a tool to the service
func (d *ServiceDir) AddTool(cfg ToolConfig) {
	d.StaticDir.AddChild(NewToolDir(cfg))
}

// RootDir creates the root filesystem with LLM-friendly features
type RootDir struct {
	*StaticDir
}

// NewRootDir creates a new root directory
// No help files - the namespace structure is self-documenting
func NewRootDir() *RootDir {
	return &RootDir{
		StaticDir: NewStaticDir("/"),
	}
}

// AddService adds a service directory to the root
func (r *RootDir) AddService(svc *ServiceDir) {
	r.StaticDir.AddChild(svc.StaticDir)
}

// ParameterizedTool creates a tool with multiple parameter files.
// This is the proper 9P way - each parameter is a file.
// Write to parameter files, then read from result.
//
// Example structure:
//
//	/nearby/
//	  lat       # write latitude
//	  lon       # write longitude
//	  radius    # write radius
//	  category  # write category
//	  result    # read to execute and get results
type ParameterizedTool struct {
	*StaticDir
	params  map[string]*ParamFile
	handler func(params map[string]string) ([]byte, error)
	mu      sync.RWMutex
}

// ParamFile is a file that stores a parameter value
type ParamFile struct {
	*BaseFile
	value string
	tool  *ParameterizedTool
}

func (f *ParamFile) Write(p []byte, offset int64) (int, error) {
	f.tool.mu.Lock()
	defer f.tool.mu.Unlock()
	f.value = string(bytes.TrimSpace(p))
	return len(p), nil
}

func (f *ParamFile) Read(p []byte, offset int64) (int, error) {
	f.tool.mu.RLock()
	defer f.tool.mu.RUnlock()
	if offset >= int64(len(f.value)) {
		return 0, io.EOF
	}
	n := copy(p, f.value[offset:])
	return n, nil
}

// ResultFile reads the result by executing the handler with current params
type ResultFile struct {
	*BaseFile
	tool *ParameterizedTool
}

func (f *ResultFile) Read(p []byte, offset int64) (int, error) {
	f.tool.mu.RLock()
	params := make(map[string]string)
	for name, pf := range f.tool.params {
		params[name] = pf.value
	}
	f.tool.mu.RUnlock()

	// Execute handler
	result, err := f.tool.handler(params)
	if err != nil {
		result = formatError(err)
	}

	if offset >= int64(len(result)) {
		return 0, io.EOF
	}
	n := copy(p, result[offset:])
	return n, nil
}

func (f *ResultFile) Write(p []byte, offset int64) (int, error) {
	return 0, ErrPermission
}

// NewParameterizedTool creates a tool with named parameter files
func NewParameterizedTool(name string, paramNames []string, handler func(map[string]string) ([]byte, error)) *ParameterizedTool {
	tool := &ParameterizedTool{
		StaticDir: NewStaticDir(name),
		params:    make(map[string]*ParamFile),
		handler:   handler,
	}

	// Create parameter files
	for _, pname := range paramNames {
		pf := &ParamFile{
			BaseFile: NewBaseFile(pname, 0666),
			tool:     tool,
		}
		tool.params[pname] = pf
		tool.StaticDir.AddChild(pf)
	}

	// Create result file
	rf := &ResultFile{
		BaseFile: NewBaseFile("result", 0444),
		tool:     tool,
	}
	tool.StaticDir.AddChild(rf)

	return tool
}
