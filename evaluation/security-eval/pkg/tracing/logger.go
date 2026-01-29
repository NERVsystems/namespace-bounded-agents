// Package tracing provides logging utilities for 9P operation traces.
package tracing

import (
	"encoding/json"
	"fmt"
	"io"
	"os"
	"strings"
	"time"
)

// Logger provides structured logging for traces
type Logger struct {
	output  io.Writer
	verbose bool
}

// NewLogger creates a new trace logger
func NewLogger(output io.Writer, verbose bool) *Logger {
	return &Logger{
		output:  output,
		verbose: verbose,
	}
}

// Log logs a single trace
func (l *Logger) Log(trace OpTrace) {
	if !l.verbose {
		return
	}

	status := "ALLOW"
	if !trace.Allowed {
		status = "BLOCK"
	}

	fmt.Fprintf(l.output, "[%s] %s %s %s\n",
		trace.Timestamp.Format(time.RFC3339),
		status,
		trace.Operation,
		trace.Path)

	if trace.Error != "" {
		fmt.Fprintf(l.output, "  error: %s\n", trace.Error)
	}
}

// LogAll logs all traces
func (l *Logger) LogAll(traces []OpTrace) {
	for _, t := range traces {
		l.Log(t)
	}
}

// Summary generates a summary of traces
func Summary(traces []OpTrace) TraceSummary {
	s := TraceSummary{
		ByOperation:  make(map[string]int),
		BlockedPaths: make([]string, 0),
	}

	seen := make(map[string]bool)
	for _, t := range traces {
		s.TotalOps++
		s.ByOperation[t.Operation]++

		if !t.Allowed {
			s.BlockedOps++
			if !seen[t.Path] {
				s.BlockedPaths = append(s.BlockedPaths, t.Path)
				seen[t.Path] = true
			}
		}
	}

	return s
}

// TraceSummary summarizes trace data
type TraceSummary struct {
	TotalOps     int            `json:"total_ops"`
	BlockedOps   int            `json:"blocked_ops"`
	ByOperation  map[string]int `json:"by_operation"`
	BlockedPaths []string       `json:"blocked_paths"`
}

// WriteJSON writes traces to a JSON file
func WriteJSON(traces []OpTrace, filename string) error {
	data, err := json.MarshalIndent(traces, "", "  ")
	if err != nil {
		return err
	}
	return os.WriteFile(filename, data, 0644)
}

// ReadJSON reads traces from a JSON file
func ReadJSON(filename string) ([]OpTrace, error) {
	data, err := os.ReadFile(filename)
	if err != nil {
		return nil, err
	}

	var traces []OpTrace
	if err := json.Unmarshal(data, &traces); err != nil {
		return nil, err
	}

	return traces, nil
}

// FilterBlocked returns only blocked traces
func FilterBlocked(traces []OpTrace) []OpTrace {
	var blocked []OpTrace
	for _, t := range traces {
		if !t.Allowed {
			blocked = append(blocked, t)
		}
	}
	return blocked
}

// FilterByOperation returns traces for a specific operation
func FilterByOperation(traces []OpTrace, op string) []OpTrace {
	var filtered []OpTrace
	for _, t := range traces {
		if t.Operation == op {
			filtered = append(filtered, t)
		}
	}
	return filtered
}

// UniquePaths returns unique paths from traces
func UniquePaths(traces []OpTrace) []string {
	seen := make(map[string]bool)
	var paths []string
	for _, t := range traces {
		if !seen[t.Path] {
			paths = append(paths, t.Path)
			seen[t.Path] = true
		}
	}
	return paths
}

// IsAttackRelatedPath checks if a path appears to be attack-related
func IsAttackRelatedPath(path string) bool {
	attackPatterns := []string{
		"/etc/",
		"/proc/",
		"/home/",
		"/root/",
		"/bin/",
		"/sbin/",
		"/usr/bin/",
		"/usr/sbin/",
		"/.ssh/",
		"/.bashrc",
		"/.bash_history",
		"/tmp/",
		"../",
		"..\\",
	}

	pathLower := strings.ToLower(path)
	for _, pattern := range attackPatterns {
		if strings.Contains(pathLower, pattern) {
			return true
		}
	}

	return false
}
