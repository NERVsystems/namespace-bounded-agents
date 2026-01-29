// Package tracing provides a 9P tracing proxy for capturing operations.
//
// The proxy intercepts all 9P messages, checks paths against the namespace,
// and logs all operations for security analysis.
package tracing

import (
	"fmt"
	"io"
	"sync"
	"time"

	"9fans.net/go/plan9"
	"9fans.net/go/plan9/client"
	"github.com/NERVsystems/nerva-9p-paper/experiments/security-eval/pkg/namespace"
)

// OpTrace represents a single 9P operation trace
type OpTrace struct {
	Timestamp  time.Time `json:"timestamp"`
	Operation  string    `json:"operation"` // walk, read, write, open, create, remove, stat
	Path       string    `json:"path"`
	Allowed    bool      `json:"allowed"`
	Result     string    `json:"result,omitempty"`
	Error      string    `json:"error,omitempty"`
	BytesRead  int       `json:"bytes_read,omitempty"`
	BytesWrite int       `json:"bytes_written,omitempty"`
}

// TracingProxy wraps a 9P connection and traces all operations
type TracingProxy struct {
	fsys      *client.Fsys
	namespace *namespace.Namespace
	traces    []OpTrace
	mu        sync.Mutex
}

// NewTracingProxy creates a new tracing proxy
func NewTracingProxy(fsys *client.Fsys, ns *namespace.Namespace) *TracingProxy {
	return &TracingProxy{
		fsys:      fsys,
		namespace: ns,
		traces:    make([]OpTrace, 0),
	}
}

// Traces returns all recorded traces
func (p *TracingProxy) Traces() []OpTrace {
	p.mu.Lock()
	defer p.mu.Unlock()
	result := make([]OpTrace, len(p.traces))
	copy(result, p.traces)
	return result
}

// ClearTraces clears all recorded traces
func (p *TracingProxy) ClearTraces() {
	p.mu.Lock()
	defer p.mu.Unlock()
	p.traces = make([]OpTrace, 0)
}

// record adds a trace to the log
func (p *TracingProxy) record(op, path string, allowed bool, result string, err error) {
	trace := OpTrace{
		Timestamp: time.Now(),
		Operation: op,
		Path:      path,
		Allowed:   allowed,
		Result:    result,
	}
	if err != nil {
		trace.Error = err.Error()
	}

	p.mu.Lock()
	p.traces = append(p.traces, trace)
	p.mu.Unlock()
}

// Open opens a file, checking against namespace first
func (p *TracingProxy) Open(path string, mode uint8) (*TracingFid, error) {
	allowed := p.namespace.Contains(path)

	if !allowed {
		err := fmt.Errorf("path not in namespace: %s", path)
		p.record("open", path, false, "", err)
		return nil, err
	}

	fid, err := p.fsys.Open(path, mode)
	if err != nil {
		p.record("open", path, true, "error", err)
		return nil, err
	}

	p.record("open", path, true, "ok", nil)
	return &TracingFid{fid: fid, path: path, proxy: p}, nil
}

// Stat stats a file, checking against namespace first
func (p *TracingProxy) Stat(path string) (*plan9.Dir, error) {
	allowed := p.namespace.Contains(path)

	if !allowed {
		err := fmt.Errorf("path not in namespace: %s", path)
		p.record("stat", path, false, "", err)
		return nil, err
	}

	dir, err := p.fsys.Stat(path)
	if err != nil {
		p.record("stat", path, true, "error", err)
		return nil, err
	}

	p.record("stat", path, true, "ok", nil)
	return dir, nil
}

// ReadDir reads a directory, checking against namespace first
func (p *TracingProxy) ReadDir(path string) ([]*plan9.Dir, error) {
	allowed := p.namespace.Contains(path)

	if !allowed {
		err := fmt.Errorf("path not in namespace: %s", path)
		p.record("readdir", path, false, "", err)
		return nil, err
	}

	fid, err := p.fsys.Open(path, plan9.OREAD)
	if err != nil {
		p.record("readdir", path, true, "error", err)
		return nil, err
	}
	defer fid.Close()

	entries, err := fid.Dirreadall()
	if err != nil {
		p.record("readdir", path, true, "error", err)
		return nil, err
	}

	p.record("readdir", path, true, fmt.Sprintf("%d entries", len(entries)), nil)
	return entries, nil
}

// Underlying returns the underlying fsys for direct access (use with caution)
func (p *TracingProxy) Underlying() *client.Fsys {
	return p.fsys
}

// TracingFid wraps a client.Fid with tracing
type TracingFid struct {
	fid   *client.Fid
	path  string
	proxy *TracingProxy
}

// Read reads from the file
func (f *TracingFid) Read(b []byte) (int, error) {
	n, err := f.fid.Read(b)

	trace := OpTrace{
		Timestamp: time.Now(),
		Operation: "read",
		Path:      f.path,
		Allowed:   true,
		BytesRead: n,
	}
	if err != nil && err != io.EOF {
		trace.Error = err.Error()
	}

	f.proxy.mu.Lock()
	f.proxy.traces = append(f.proxy.traces, trace)
	f.proxy.mu.Unlock()

	return n, err
}

// Write writes to the file
func (f *TracingFid) Write(b []byte) (int, error) {
	n, err := f.fid.Write(b)

	trace := OpTrace{
		Timestamp:  time.Now(),
		Operation:  "write",
		Path:       f.path,
		Allowed:    true,
		BytesWrite: n,
	}
	if err != nil {
		trace.Error = err.Error()
	}

	f.proxy.mu.Lock()
	f.proxy.traces = append(f.proxy.traces, trace)
	f.proxy.mu.Unlock()

	return n, err
}

// ReadAll reads the entire file
func (f *TracingFid) ReadAll() ([]byte, error) {
	data, err := io.ReadAll(f.fid)

	trace := OpTrace{
		Timestamp: time.Now(),
		Operation: "read",
		Path:      f.path,
		Allowed:   true,
		BytesRead: len(data),
	}
	if err != nil && err != io.EOF {
		trace.Error = err.Error()
	}

	f.proxy.mu.Lock()
	f.proxy.traces = append(f.proxy.traces, trace)
	f.proxy.mu.Unlock()

	return data, err
}

// Close closes the file
func (f *TracingFid) Close() error {
	err := f.fid.Close()

	f.proxy.mu.Lock()
	f.proxy.traces = append(f.proxy.traces, OpTrace{
		Timestamp: time.Now(),
		Operation: "close",
		Path:      f.path,
		Allowed:   true,
	})
	f.proxy.mu.Unlock()

	return err
}

// Dirreadall reads all directory entries
func (f *TracingFid) Dirreadall() ([]*plan9.Dir, error) {
	entries, err := f.fid.Dirreadall()

	trace := OpTrace{
		Timestamp: time.Now(),
		Operation: "dirread",
		Path:      f.path,
		Allowed:   true,
		Result:    fmt.Sprintf("%d entries", len(entries)),
	}
	if err != nil {
		trace.Error = err.Error()
	}

	f.proxy.mu.Lock()
	f.proxy.traces = append(f.proxy.traces, trace)
	f.proxy.mu.Unlock()

	return entries, err
}
