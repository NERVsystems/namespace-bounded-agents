// Package nerv9p implements deterministic tool-execution and rewrite-on-error
// for AgentFS Type B tools. It keeps formatting variance out of the LLM by
// canonicalising to key=value whenever the tool supports it.
package nerv9p

import (
	"encoding/json"
	"fmt"
	"regexp"
	"sort"
	"strings"
	"unicode"
)

// RewriteResult is the outcome of attempting to rewrite a failed tool invocation.
type RewriteResult struct {
	RewrittenInput string
	DidRewrite     bool
	Terminal       bool // True means do not retry.
}

// ErrorPayload is the structured error returned by /tool/error.
type ErrorPayload struct {
	Error     bool     `json:"error"`
	Code      string   `json:"code"`
	Message   string   `json:"message,omitempty"`
	Expected  []string `json:"expected"`
	Missing   []string `json:"missing,omitempty"`
	Formats   []string `json:"formats,omitempty"`
	HintCode  string   `json:"hint_code,omitempty"`
	Retryable bool     `json:"retryable"`
}

// Rewriter is a small, testable strategy for a specific error code.
type Rewriter interface {
	Rewrite(raw string, err ErrorPayload, paramsOrder []string, example string) (RewriteResult, error)
}

// RewriterRegistry holds rewriters for each error code.
type RewriterRegistry struct {
	rewriters map[string]Rewriter
}

// NewRewriterRegistry creates a registry with all standard rewriters.
func NewRewriterRegistry() *RewriterRegistry {
	return &RewriterRegistry{
		rewriters: map[string]Rewriter{
			"missing_param": &MissingParamRewriter{},
			"parse_error":   &ParseErrorRewriter{},
			"unknown_param": &UnknownParamRewriter{},
			"format_error":  &FormatErrorRewriter{},
		},
	}
}

// Get returns the rewriter for a given error code.
func (r *RewriterRegistry) Get(code string) Rewriter {
	return r.rewriters[code]
}

// =============================================================================
// Synonym Table for unknown_param resolution
// =============================================================================

var synonymTable = map[string]string{
	// Category synonyms
	"amenity":  "category",
	"poi_type": "category",
	"type":     "category",

	// Coordinate synonyms
	"lng":       "lon",
	"longitude": "lon",
	"long":      "lon",
	"latitude":  "lat",

	// Point synonyms
	"point":       "points",
	"coordinates": "points",
	"coords":      "points",

	// Radius synonyms
	"distance": "radius",
	"range":    "radius",
}

// =============================================================================
// MissingParamRewriter
// =============================================================================

// MissingParamRewriter handles missing_param errors.
// If the original write contains any =, parse partial kv, keep recognised pairs,
// and fill missing keys by consuming any remaining positional fields.
// Otherwise treat as positional, map to expected order, and rewrite to canonical kv.
type MissingParamRewriter struct{}

func (r *MissingParamRewriter) Rewrite(raw string, err ErrorPayload, paramsOrder []string, example string) (RewriteResult, error) {
	raw = strings.TrimSpace(raw)

	// Determine param order (prefer _params, fall back to expected)
	order := paramsOrder
	if len(order) == 0 {
		order = err.Expected
	}

	// Check if input contains any key=value pairs
	if strings.Contains(raw, "=") {
		return r.rewritePartialKV(raw, err, order)
	}

	// Pure positional input
	return r.rewritePositional(raw, err, order)
}

func (r *MissingParamRewriter) rewritePartialKV(raw string, err ErrorPayload, order []string) (RewriteResult, error) {
	// Parse existing kv pairs
	pairs := parseKVPairs(raw)
	recognised := make(map[string]string)
	var positional []string

	expectedSet := toSet(err.Expected)

	for _, pair := range pairs {
		if strings.Contains(pair, "=") {
			parts := strings.SplitN(pair, "=", 2)
			key := strings.TrimSpace(parts[0])
			value := strings.TrimSpace(parts[1])
			if expectedSet[key] {
				recognised[key] = value
			}
			// Ignore unrecognised keys in this context
		} else {
			// Positional value without key
			positional = append(positional, strings.TrimSpace(pair))
		}
	}

	// Fill missing keys with positional values
	filled := 0
	for _, key := range err.Missing {
		if _, ok := recognised[key]; !ok && len(positional) > 0 {
			recognised[key] = positional[0]
			positional = positional[1:]
			filled++
		}
	}

	// If we couldn't fill any missing params, terminal
	if filled == 0 && len(err.Missing) > 0 {
		return RewriteResult{Terminal: true}, nil
	}

	// Build canonical output
	canonical := buildCanonicalKV(recognised, order)
	if canonical == raw {
		return RewriteResult{Terminal: true}, nil
	}

	return RewriteResult{
		RewrittenInput: canonical,
		DidRewrite:     true,
	}, nil
}

func (r *MissingParamRewriter) rewritePositional(raw string, err ErrorPayload, order []string) (RewriteResult, error) {
	// Tokenise: split on whitespace
	tokens := tokenize(raw)

	// Stop condition: incompatible arity
	if len(tokens) > len(order) {
		return RewriteResult{Terminal: true}, nil
	}

	// Map tokens to params in order
	pairs := make(map[string]string)
	for i, token := range tokens {
		if i < len(order) {
			pairs[order[i]] = token
		}
	}

	canonical := buildCanonicalKV(pairs, order)
	return RewriteResult{
		RewrittenInput: canonical,
		DidRewrite:     true,
	}, nil
}

// =============================================================================
// ParseErrorRewriter
// =============================================================================

// ParseErrorRewriter handles parse_error.
// Assumes positional input, tokenises deterministically, maps by _params or expected,
// and rewrites to canonical kv. If field count is incompatible, fails terminally.
type ParseErrorRewriter struct{}

func (r *ParseErrorRewriter) Rewrite(raw string, err ErrorPayload, paramsOrder []string, example string) (RewriteResult, error) {
	raw = strings.TrimSpace(raw)

	order := paramsOrder
	if len(order) == 0 {
		order = err.Expected
	}

	tokens := tokenize(raw)

	// Stop condition: incompatible arity
	if len(tokens) == 0 || len(tokens) > len(order) {
		return RewriteResult{Terminal: true}, nil
	}

	pairs := make(map[string]string)
	for i, token := range tokens {
		if i < len(order) {
			pairs[order[i]] = token
		}
	}

	canonical := buildCanonicalKV(pairs, order)
	return RewriteResult{
		RewrittenInput: canonical,
		DidRewrite:     true,
	}, nil
}

// =============================================================================
// UnknownParamRewriter
// =============================================================================

// UnknownParamRewriter handles unknown_param errors.
// Parses kv pairs, rewrites keys using synonym table first, then bounded edit-distance.
// If mapping is ambiguous, fails terminally.
type UnknownParamRewriter struct{}

func (r *UnknownParamRewriter) Rewrite(raw string, err ErrorPayload, paramsOrder []string, example string) (RewriteResult, error) {
	raw = strings.TrimSpace(raw)

	pairs := parseKVPairs(raw)
	rewritten := make(map[string]string)
	expectedSet := toSet(err.Expected)

	for _, pair := range pairs {
		if !strings.Contains(pair, "=") {
			continue
		}
		parts := strings.SplitN(pair, "=", 2)
		key := strings.TrimSpace(parts[0])
		value := strings.TrimSpace(parts[1])

		// Already valid?
		if expectedSet[key] {
			rewritten[key] = value
			continue
		}

		// Try synonym table
		if mapped, ok := synonymTable[strings.ToLower(key)]; ok && expectedSet[mapped] {
			rewritten[mapped] = value
			continue
		}

		// Try bounded edit-distance (max 2 edits)
		match := fuzzyMatch(key, err.Expected, 2)
		if match == "" {
			// Ambiguous or no match - terminal
			return RewriteResult{Terminal: true}, nil
		}
		rewritten[match] = value
	}

	order := paramsOrder
	if len(order) == 0 {
		order = err.Expected
	}

	canonical := buildCanonicalKV(rewritten, order)
	if canonical == raw {
		return RewriteResult{Terminal: true}, nil
	}

	return RewriteResult{
		RewrittenInput: canonical,
		DidRewrite:     true,
	}, nil
}

// =============================================================================
// FormatErrorRewriter
// =============================================================================

// FormatErrorRewriter handles format_error.
// Normalises values deterministically based on key type.
// For list-like keys (points), normalises delimiters to canonical form.
type FormatErrorRewriter struct{}

var listKeys = map[string]bool{
	"points":      true,
	"coordinates": true,
	"locations":   true,
}

func (r *FormatErrorRewriter) Rewrite(raw string, err ErrorPayload, paramsOrder []string, example string) (RewriteResult, error) {
	raw = strings.TrimSpace(raw)

	// For format_error, parse more carefully since values may contain spaces
	// Format: key=value (where value might have spaces for list types)
	rewritten := make(map[string]string)

	// Find first = to split key from value
	idx := strings.Index(raw, "=")
	if idx == -1 {
		return RewriteResult{Terminal: true}, nil
	}

	key := strings.TrimSpace(raw[:idx])
	value := strings.TrimSpace(raw[idx+1:])

	// Normalise list-like values
	if listKeys[key] {
		value = normalizeListValue(value, example)
	}

	rewritten[key] = value

	// Check size bounds
	for _, v := range rewritten {
		if len(v) > MaxParamBytes {
			return RewriteResult{Terminal: true}, nil
		}
	}

	order := paramsOrder
	if len(order) == 0 {
		order = err.Expected
	}

	canonical := buildCanonicalKV(rewritten, order)
	if canonical == raw {
		return RewriteResult{Terminal: true}, nil
	}

	return RewriteResult{
		RewrittenInput: canonical,
		DidRewrite:     true,
	}, nil
}

// =============================================================================
// Helper Functions
// =============================================================================

// parseKVPairs splits input into key=value pairs or bare tokens.
// Handles space-separated pairs like "lat=1 lon=2"
func parseKVPairs(raw string) []string {
	// Split on spaces, keeping = attached
	var pairs []string
	for _, token := range strings.Fields(raw) {
		pairs = append(pairs, token)
	}
	return pairs
}

// tokenize splits input on whitespace
func tokenize(raw string) []string {
	return strings.Fields(raw)
}

// toSet converts a slice to a set (map)
func toSet(slice []string) map[string]bool {
	set := make(map[string]bool)
	for _, s := range slice {
		set[s] = true
	}
	return set
}

// buildCanonicalKV builds a canonical key=value string in order
func buildCanonicalKV(pairs map[string]string, order []string) string {
	var parts []string
	seen := make(map[string]bool)

	// First, emit in order
	for _, key := range order {
		if val, ok := pairs[key]; ok {
			parts = append(parts, fmt.Sprintf("%s=%s", key, val))
			seen[key] = true
		}
	}

	// Then emit any remaining keys alphabetically
	var remaining []string
	for key := range pairs {
		if !seen[key] {
			remaining = append(remaining, key)
		}
	}
	sort.Strings(remaining)
	for _, key := range remaining {
		parts = append(parts, fmt.Sprintf("%s=%s", key, pairs[key]))
	}

	return strings.Join(parts, " ")
}

// fuzzyMatch finds a unique match within maxDist edits
func fuzzyMatch(input string, candidates []string, maxDist int) string {
	input = strings.ToLower(input)

	// First, check for exact match
	for _, c := range candidates {
		if strings.ToLower(c) == input {
			return c
		}
	}

	// Then fuzzy match
	var matches []string
	for _, c := range candidates {
		dist := levenshtein(input, strings.ToLower(c))
		if dist > 0 && dist <= maxDist {
			matches = append(matches, c)
		}
	}

	// Unique match only
	if len(matches) == 1 {
		return matches[0]
	}
	return ""
}

// levenshtein calculates edit distance
func levenshtein(a, b string) int {
	if len(a) == 0 {
		return len(b)
	}
	if len(b) == 0 {
		return len(a)
	}

	matrix := make([][]int, len(a)+1)
	for i := range matrix {
		matrix[i] = make([]int, len(b)+1)
		matrix[i][0] = i
	}
	for j := 0; j <= len(b); j++ {
		matrix[0][j] = j
	}

	for i := 1; i <= len(a); i++ {
		for j := 1; j <= len(b); j++ {
			cost := 1
			if a[i-1] == b[j-1] {
				cost = 0
			}
			matrix[i][j] = min3(
				matrix[i-1][j]+1,
				matrix[i][j-1]+1,
				matrix[i-1][j-1]+cost,
			)
		}
	}

	return matrix[len(a)][len(b)]
}

func min3(a, b, c int) int {
	if a < b {
		if a < c {
			return a
		}
		return c
	}
	if b < c {
		return b
	}
	return c
}

// normalizeListValue normalises list values (points) to canonical form
// Treats \n, spaces, ; as record separators
// Treats , or whitespace within records as field separators
func normalizeListValue(value string, example string) string {
	// Determine canonical separator from example if available
	recordSep := "\n"
	if example != "" && strings.Contains(example, ";") {
		recordSep = ";"
	}

	// Normalise input: replace all separators with newlines
	value = strings.ReplaceAll(value, ";", "\n")
	value = regexp.MustCompile(`\s+`).ReplaceAllString(value, "\n")

	// Split into records
	var records []string
	for _, line := range strings.Split(value, "\n") {
		line = strings.TrimSpace(line)
		if line == "" {
			continue
		}

		// Normalise field separators within record
		// Accept: "48.85,2.29" or "48.85 2.29"
		if !strings.Contains(line, ",") && strings.ContainsFunc(line, unicode.IsSpace) {
			parts := strings.Fields(line)
			if len(parts) == 2 {
				line = parts[0] + "," + parts[1]
			}
		}

		records = append(records, line)
	}

	// Bounds check
	if len(records) > MaxPointsCount {
		records = records[:MaxPointsCount]
	}

	if recordSep == ";" {
		return strings.Join(records, ";")
	}
	return strings.Join(records, "\n")
}

// ParseErrorPayload parses JSON error from /tool/error
func ParseErrorPayload(data []byte) (*ErrorPayload, error) {
	var ep ErrorPayload
	if err := json.Unmarshal(data, &ep); err != nil {
		return nil, err
	}
	return &ep, nil
}

// CanonicalizeInput converts raw input to canonical kv format if possible.
// This is the "default to kv" policy: called BEFORE first write attempt.
func CanonicalizeInput(raw string, params []string) string {
	raw = strings.TrimSpace(raw)

	// Already kv format?
	if strings.Contains(raw, "=") {
		// Validate and normalise
		pairs := parseKVPairs(raw)
		kv := make(map[string]string)
		for _, pair := range pairs {
			if strings.Contains(pair, "=") {
				parts := strings.SplitN(pair, "=", 2)
				kv[strings.TrimSpace(parts[0])] = strings.TrimSpace(parts[1])
			}
		}
		return buildCanonicalKV(kv, params)
	}

	// Try to interpret as positional
	tokens := tokenize(raw)
	if len(tokens) > 0 && len(tokens) <= len(params) {
		kv := make(map[string]string)
		for i, token := range tokens {
			kv[params[i]] = token
		}
		return buildCanonicalKV(kv, params)
	}

	// Can't canonicalise, return as-is
	return raw
}
