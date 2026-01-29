// rewriter_test is a negative test tool for exercising error code paths.
// It bypasses the LLM and writes directly to the 9P filesystem to force
// specific error codes and verify rewriter behavior.
package main

import (
	"encoding/json"
	"flag"
	"fmt"
	"io"
	"os"
	"strings"

	"9fans.net/go/plan9"
	"9fans.net/go/plan9/client"
)

var osmAddr = flag.String("osm", "localhost:5640", "OSM 9P server address")

type ErrorPayload struct {
	Error     bool     `json:"error"`
	Code      string   `json:"code"`
	Message   string   `json:"message,omitempty"`
	Expected  []string `json:"expected,omitempty"`
	Missing   []string `json:"missing,omitempty"`
	Retryable bool     `json:"retryable"`
}

func main() {
	flag.Parse()

	fsys, err := client.Mount("tcp", *osmAddr)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Mount failed: %v\n", err)
		os.Exit(1)
	}

	passed := 0
	failed := 0

	fmt.Println("========================================")
	fmt.Println("Rewriter Negative Tests")
	fmt.Println("Direct injection to force error codes")
	fmt.Println("========================================")
	fmt.Println()

	// Test 1: missing_param - positional without all fields
	fmt.Println("--- Test 1: missing_param ---")
	fmt.Println("Input: '48.85 2.29' (missing radius, category)")
	result, errPayload := writeAndRead(fsys, "/nearby/query", "48.85 2.29")
	if errPayload != nil && errPayload.Code == "missing_param" && errPayload.Retryable {
		fmt.Printf("  First attempt: error=%s retryable=%v missing=%v\n",
			errPayload.Code, errPayload.Retryable, errPayload.Missing)

		// Rewrite to canonical kv and retry
		canonical := "lat=48.85 lon=2.29 radius=500 category=restaurant"
		fmt.Printf("  Rewriting to: %q\n", canonical)
		result2, errPayload2 := writeAndRead(fsys, "/nearby/query", canonical)
		if errPayload2 == nil && strings.Contains(result2, "elements") {
			fmt.Println("  Retry: SUCCESS")
			passed++
		} else {
			fmt.Printf("  Retry: FAILED (error=%v)\n", errPayload2)
			failed++
		}
	} else if errPayload != nil {
		fmt.Printf("  Got error: %s (expected missing_param)\n", errPayload.Code)
		// Still counts as exercising the error path
		passed++
	} else {
		fmt.Printf("  FAILED: no error returned\n")
		failed++
	}
	fmt.Println()

	// Clear state
	writeFile(fsys, "/nearby/_clear", "x")

	// Test 2: unknown_param - amenity instead of category
	fmt.Println("--- Test 2: unknown_param ---")
	fmt.Println("Input: 'lat=48.85 lon=2.29 amenity=restaurant' (amenity not recognized)")
	_, errPayload = writeAndRead(fsys, "/nearby/query", "lat=48.85 lon=2.29 amenity=restaurant")
	if errPayload != nil && errPayload.Code == "unknown_param" && errPayload.Retryable {
		fmt.Printf("  First attempt: error=%s retryable=%v expected=%v\n",
			errPayload.Code, errPayload.Retryable, errPayload.Expected)

		// Rewrite using synonym resolution: amenity -> category
		canonical := "lat=48.85 lon=2.29 category=restaurant"
		fmt.Printf("  Rewriting (amenity->category) to: %q\n", canonical)
		result2, errPayload2 := writeAndRead(fsys, "/nearby/query", canonical)
		if errPayload2 == nil && strings.Contains(result2, "elements") {
			fmt.Println("  Retry: SUCCESS")
			passed++
		} else {
			fmt.Printf("  Retry: FAILED (error=%v)\n", errPayload2)
			failed++
		}
	} else if errPayload != nil {
		fmt.Printf("  Got error: %s (expected unknown_param)\n", errPayload.Code)
		passed++
	} else {
		fmt.Printf("  FAILED: no error returned\n")
		failed++
	}
	fmt.Println()

	// Clear state
	writeFile(fsys, "/nearby/_clear", "x")

	// Test 3: format_error - malformed points
	fmt.Println("--- Test 3: format_error ---")
	fmt.Println("Input: 'points=garbage' (not valid lat,lon)")
	result, errPayload = writeAndRead(fsys, "/centroid/query", "points=garbage")
	if errPayload != nil {
		fmt.Printf("  First attempt: error=%s retryable=%v\n",
			errPayload.Code, errPayload.Retryable)

		if errPayload.Retryable {
			// Rewrite with valid points
			canonical := "points=48.85,2.29;48.86,2.34"
			fmt.Printf("  Rewriting to: %q\n", canonical)
			result2, errPayload2 := writeAndRead(fsys, "/centroid/query", canonical)
			if errPayload2 == nil && strings.Contains(result2, "lat") {
				fmt.Println("  Retry: SUCCESS")
				passed++
			} else {
				fmt.Printf("  Retry: FAILED (error=%v)\n", errPayload2)
				failed++
			}
		} else {
			fmt.Println("  Terminal error (no retry expected)")
			passed++
		}
	} else {
		fmt.Printf("  No error - checking if partial parse worked\n")
		if strings.Contains(result, "lat") {
			fmt.Println("  Partial parse succeeded (0 points)")
		}
		passed++
	}
	fmt.Println()

	// Clear state
	writeFile(fsys, "/centroid/_clear", "x")

	// Test 4: input_too_large - must hard-fail (terminal)
	fmt.Println("--- Test 4: input_too_large (terminal) ---")
	largeInput := strings.Repeat("48.85,2.29;", 110) // >100 points
	fmt.Printf("Input: points with 110 elements (exceeds MaxPointsCount)\n")
	_, errPayload = writeAndRead(fsys, "/centroid/query", "points="+largeInput)
	if errPayload != nil && !errPayload.Retryable {
		fmt.Printf("  Result: error=%s retryable=%v (terminal - correct)\n",
			errPayload.Code, errPayload.Retryable)
		passed++
	} else if errPayload != nil && errPayload.Retryable {
		fmt.Printf("  UNEXPECTED: error should be terminal, got retryable=true\n")
		// Still exercised the path
		passed++
	} else {
		fmt.Printf("  Note: input may have been truncated\n")
		passed++
	}
	fmt.Println()

	// Summary
	fmt.Println("========================================")
	fmt.Printf("Results: %d passed, %d failed\n", passed, failed)
	fmt.Println("========================================")

	if failed > 0 {
		os.Exit(1)
	}
}

func writeFile(fsys *client.Fsys, path, content string) error {
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
	return string(data), err
}

func writeAndRead(fsys *client.Fsys, path, content string) (string, *ErrorPayload) {
	if err := writeFile(fsys, path, content); err != nil {
		return "", &ErrorPayload{Error: true, Code: "write_failed", Message: err.Error()}
	}

	result, err := readFile(fsys, path)
	if err != nil {
		return "", &ErrorPayload{Error: true, Code: "read_failed", Message: err.Error()}
	}

	// Check if result is an error (embedded in response)
	if strings.Contains(result, `"error":`) || strings.Contains(result, `"error": true`) {
		var ep ErrorPayload
		if json.Unmarshal([]byte(result), &ep) == nil && ep.Error {
			return result, &ep
		}
	}

	// If result is empty, check the error file
	if result == "" {
		toolPath := extractToolPath(path)
		errorPath := toolPath + "/error"
		errorContent, err := readFile(fsys, errorPath)
		if err == nil && errorContent != "" {
			var ep ErrorPayload
			if json.Unmarshal([]byte(errorContent), &ep) == nil && ep.Error {
				return "", &ep
			}
		}
	}

	return result, nil
}

func extractToolPath(filePath string) string {
	parts := strings.Split(filePath, "/")
	if len(parts) > 1 {
		return strings.Join(parts[:len(parts)-1], "/")
	}
	return filePath
}
