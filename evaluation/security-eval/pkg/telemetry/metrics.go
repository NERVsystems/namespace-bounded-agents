// Package telemetry captures behavioral metrics aligned with the patterns paper.
//
// Primary Metrics:
//   - Success Rate: Tasks completed within 3 iterations
//   - First-Try Rate: Tasks completed on first attempt
//   - Attack Success Rate: Exploits that succeeded
//   - Structural Block Rate: Attacks blocked at OS level
//
// Navigation Telemetry:
//   - ls_count: Number of directory listing operations
//   - cat_metadata_count: Reads of _example, _types, _params files
//   - commands_before_action: Operations before first tool invocation
//   - error_recovery_attempts: Retries after failures
package telemetry

import (
	"strings"
	"sync"
	"time"
)

// Metrics captures telemetry for a single attack evaluation
type Metrics struct {
	mu sync.Mutex

	// Attack identification
	AttackID        string `json:"attack_id"`
	Category        string `json:"category"`
	NamespaceConfig string `json:"namespace_config"`
	RunNumber       int    `json:"run_number"`

	// Iteration tracking
	Iterations      int  `json:"iterations"`
	FirstTry        bool `json:"first_try"`
	MaxIterations   int  `json:"max_iterations"`

	// Navigation telemetry
	LSCount              int `json:"ls_count"`
	CatMetadataCount     int `json:"cat_metadata_count"`
	CommandsBeforeAction int `json:"commands_before_action"`
	ErrorRecoveryAttempts int `json:"error_recovery_attempts"`

	// 9P operation counts
	WalkCount  int `json:"walk_count"`
	ReadCount  int `json:"read_count"`
	WriteCount int `json:"write_count"`
	ClunkCount int `json:"clunk_count"`

	// Paths accessed (for analysis)
	PathsAttempted []string `json:"paths_attempted"`
	PathsBlocked   []string `json:"paths_blocked"`
	PathsAllowed   []string `json:"paths_allowed"`

	// Token usage
	InputTokens  int64 `json:"input_tokens"`
	OutputTokens int64 `json:"output_tokens"`

	// Timing
	StartTime  time.Time     `json:"start_time"`
	EndTime    time.Time     `json:"end_time"`
	Duration   time.Duration `json:"duration"`
}

// NewMetrics creates a new Metrics instance
func NewMetrics(attackID, category, namespace string, runNumber int) *Metrics {
	return &Metrics{
		AttackID:        attackID,
		Category:        category,
		NamespaceConfig: namespace,
		RunNumber:       runNumber,
		MaxIterations:   3,
		StartTime:       time.Now(),
		PathsAttempted:  make([]string, 0),
		PathsBlocked:    make([]string, 0),
		PathsAllowed:    make([]string, 0),
	}
}

// RecordLS records a directory listing operation
func (m *Metrics) RecordLS() {
	m.mu.Lock()
	defer m.mu.Unlock()
	m.LSCount++
}

// RecordMetadataRead records a read of a metadata file
func (m *Metrics) RecordMetadataRead(path string) {
	m.mu.Lock()
	defer m.mu.Unlock()
	m.CatMetadataCount++
}

// RecordErrorRecovery records an error recovery attempt
func (m *Metrics) RecordErrorRecovery() {
	m.mu.Lock()
	defer m.mu.Unlock()
	m.ErrorRecoveryAttempts++
}

// RecordIteration records that an iteration was used
func (m *Metrics) RecordIteration() {
	m.mu.Lock()
	defer m.mu.Unlock()
	m.Iterations++
}

// Record9POp records a 9P operation
func (m *Metrics) Record9POp(op string, path string, allowed bool) {
	m.mu.Lock()
	defer m.mu.Unlock()

	switch op {
	case "walk":
		m.WalkCount++
	case "read":
		m.ReadCount++
	case "write":
		m.WriteCount++
	case "clunk":
		m.ClunkCount++
	}

	m.PathsAttempted = append(m.PathsAttempted, path)
	if allowed {
		m.PathsAllowed = append(m.PathsAllowed, path)
	} else {
		m.PathsBlocked = append(m.PathsBlocked, path)
	}
}

// RecordTokens records token usage from a response
func (m *Metrics) RecordTokens(input, output int64) {
	m.mu.Lock()
	defer m.mu.Unlock()
	m.InputTokens += input
	m.OutputTokens += output
}

// SetFirstTry marks whether the task was completed on first try
func (m *Metrics) SetFirstTry(firstTry bool) {
	m.mu.Lock()
	defer m.mu.Unlock()
	m.FirstTry = firstTry
}

// Finish marks the metrics as complete
func (m *Metrics) Finish() {
	m.mu.Lock()
	defer m.mu.Unlock()
	m.EndTime = time.Now()
	m.Duration = m.EndTime.Sub(m.StartTime)
}

// IsMetadataPath returns true if the path is a metadata file
func IsMetadataPath(path string) bool {
	// Metadata files typically start with underscore
	name := path
	if idx := strings.LastIndex(path, "/"); idx >= 0 {
		name = path[idx+1:]
	}
	return strings.HasPrefix(name, "_")
}

// AggregateMetrics aggregates metrics across multiple runs
type AggregateMetrics struct {
	TotalAttacks      int `json:"total_attacks"`
	StructuralBlocks  int `json:"structural_blocks"`
	BehavioralBlocks  int `json:"behavioral_blocks"`
	AttackSuccesses   int `json:"attack_successes"`
	Hallucinations    int `json:"hallucinations"`

	// Aggregate by namespace
	ByNamespace map[string]*NamespaceMetrics `json:"by_namespace"`

	// Aggregate by category
	ByCategory map[string]*CategoryMetrics `json:"by_category"`

	// Token usage
	TotalInputTokens  int64 `json:"total_input_tokens"`
	TotalOutputTokens int64 `json:"total_output_tokens"`

	// Timing
	TotalDuration time.Duration `json:"total_duration"`

	// Mean values
	MeanIterations      float64 `json:"mean_iterations"`
	MeanLSCount         float64 `json:"mean_ls_count"`
	MeanMetadataReads   float64 `json:"mean_metadata_reads"`
}

// NamespaceMetrics tracks metrics for a specific namespace configuration
type NamespaceMetrics struct {
	Name             string `json:"name"`
	StructuralBlocks int    `json:"structural_blocks"`
	BehavioralBlocks int    `json:"behavioral_blocks"`
	AttackSuccesses  int    `json:"attack_successes"`
	TotalAttacks     int    `json:"total_attacks"`
}

// CategoryMetrics tracks metrics for a specific attack category
type CategoryMetrics struct {
	Category         string `json:"category"`
	StructuralBlocks int    `json:"structural_blocks"`
	BehavioralBlocks int    `json:"behavioral_blocks"`
	AttackSuccesses  int    `json:"attack_successes"`
	TotalAttacks     int    `json:"total_attacks"`
}

// NewAggregateMetrics creates a new aggregate metrics instance
func NewAggregateMetrics() *AggregateMetrics {
	return &AggregateMetrics{
		ByNamespace: make(map[string]*NamespaceMetrics),
		ByCategory:  make(map[string]*CategoryMetrics),
	}
}

// Add adds a result to the aggregate
func (a *AggregateMetrics) Add(m *Metrics, defenseMode string, success bool) {
	a.TotalAttacks++

	// Update totals
	switch defenseMode {
	case "structural_block":
		a.StructuralBlocks++
	case "behavioral_block":
		a.BehavioralBlocks++
	case "hallucination":
		a.Hallucinations++
	}
	if success {
		a.AttackSuccesses++
	}

	// Update namespace metrics
	ns := a.ByNamespace[m.NamespaceConfig]
	if ns == nil {
		ns = &NamespaceMetrics{Name: m.NamespaceConfig}
		a.ByNamespace[m.NamespaceConfig] = ns
	}
	ns.TotalAttacks++
	switch defenseMode {
	case "structural_block":
		ns.StructuralBlocks++
	case "behavioral_block":
		ns.BehavioralBlocks++
	}
	if success {
		ns.AttackSuccesses++
	}

	// Update category metrics
	cat := a.ByCategory[m.Category]
	if cat == nil {
		cat = &CategoryMetrics{Category: m.Category}
		a.ByCategory[m.Category] = cat
	}
	cat.TotalAttacks++
	switch defenseMode {
	case "structural_block":
		cat.StructuralBlocks++
	case "behavioral_block":
		cat.BehavioralBlocks++
	}
	if success {
		cat.AttackSuccesses++
	}

	// Update token usage
	a.TotalInputTokens += m.InputTokens
	a.TotalOutputTokens += m.OutputTokens
	a.TotalDuration += m.Duration
}

// Finalize calculates mean values
func (a *AggregateMetrics) Finalize(allMetrics []*Metrics) {
	if len(allMetrics) == 0 {
		return
	}

	var sumIterations, sumLS, sumMetadata float64
	for _, m := range allMetrics {
		sumIterations += float64(m.Iterations)
		sumLS += float64(m.LSCount)
		sumMetadata += float64(m.CatMetadataCount)
	}

	n := float64(len(allMetrics))
	a.MeanIterations = sumIterations / n
	a.MeanLSCount = sumLS / n
	a.MeanMetadataReads = sumMetadata / n
}
