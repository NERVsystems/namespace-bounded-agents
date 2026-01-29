// Package stats provides statistical functions for security evaluation.
//
// Implements Wilson score confidence intervals and Cohen's h effect size,
// which are appropriate for binary outcomes (attack success/failure).
package stats

import (
	"math"
)

// ConfidenceInterval represents a confidence interval
type ConfidenceInterval struct {
	Lower float64 `json:"lower"`
	Upper float64 `json:"upper"`
	Level float64 `json:"level"` // e.g., 0.95 for 95% CI
}

// WilsonScore calculates the Wilson score confidence interval for a proportion.
//
// The Wilson score interval is preferred over the normal approximation
// for small samples and proportions near 0 or 1, which is common in
// security evaluation where we expect few/no successful attacks.
//
// Parameters:
//   - successes: number of successes (e.g., attacks that succeeded)
//   - n: total number of trials
//   - confidence: confidence level (e.g., 0.95 for 95% CI)
//
// Returns the lower and upper bounds of the confidence interval.
func WilsonScore(successes, n int, confidence float64) ConfidenceInterval {
	if n == 0 {
		return ConfidenceInterval{Lower: 0, Upper: 1, Level: confidence}
	}

	// Z-score for the confidence level
	// For 95% CI, z ≈ 1.96
	z := zScore(confidence)
	z2 := z * z

	// Observed proportion
	p := float64(successes) / float64(n)

	// Wilson score formula
	denominator := 1.0 + z2/float64(n)

	center := p + z2/(2*float64(n))
	margin := z * math.Sqrt((p*(1-p)+z2/(4*float64(n)))/float64(n))

	lower := (center - margin) / denominator
	upper := (center + margin) / denominator

	// Clamp to [0, 1]
	if lower < 0 {
		lower = 0
	}
	if upper > 1 {
		upper = 1
	}

	return ConfidenceInterval{
		Lower: lower,
		Upper: upper,
		Level: confidence,
	}
}

// zScore returns the z-score for a given confidence level
func zScore(confidence float64) float64 {
	// Common confidence levels
	switch {
	case math.Abs(confidence-0.99) < 0.001:
		return 2.576
	case math.Abs(confidence-0.95) < 0.001:
		return 1.96
	case math.Abs(confidence-0.90) < 0.001:
		return 1.645
	default:
		// Approximate using inverse normal CDF
		// For simplicity, use a lookup table approach
		return 1.96 // Default to 95%
	}
}

// CohensH calculates Cohen's h effect size for comparing two proportions.
//
// Cohen's h is appropriate for binary outcomes and is interpreted as:
//   - Small effect: |h| ≈ 0.2
//   - Medium effect: |h| ≈ 0.5
//   - Large effect: |h| ≈ 0.8
//
// Parameters:
//   - p1: first proportion (e.g., attack success rate with full namespace)
//   - p2: second proportion (e.g., attack success rate with minimal namespace)
//
// Returns Cohen's h effect size.
func CohensH(p1, p2 float64) float64 {
	// h = 2 * arcsin(sqrt(p1)) - 2 * arcsin(sqrt(p2))
	phi1 := 2 * math.Asin(math.Sqrt(p1))
	phi2 := 2 * math.Asin(math.Sqrt(p2))
	return phi1 - phi2
}

// EffectSizeInterpretation returns a human-readable interpretation of Cohen's h
func EffectSizeInterpretation(h float64) string {
	absH := math.Abs(h)
	switch {
	case absH < 0.2:
		return "negligible"
	case absH < 0.5:
		return "small"
	case absH < 0.8:
		return "medium"
	default:
		return "large"
	}
}

// MetricWithCI represents a metric value with its confidence interval
type MetricWithCI struct {
	Value float64            `json:"value"`
	CI95  ConfidenceInterval `json:"ci_95"`
}

// NewMetricWithCI creates a MetricWithCI from success/total counts
func NewMetricWithCI(successes, total int) MetricWithCI {
	var value float64
	if total > 0 {
		value = float64(successes) / float64(total)
	}

	return MetricWithCI{
		Value: value,
		CI95:  WilsonScore(successes, total, 0.95),
	}
}

// Summary statistics for a set of numeric values
type Summary struct {
	Mean   float64 `json:"mean"`
	StdDev float64 `json:"std_dev"`
	Min    float64 `json:"min"`
	Max    float64 `json:"max"`
	N      int     `json:"n"`
}

// Summarize calculates summary statistics for a slice of values
func Summarize(values []float64) Summary {
	if len(values) == 0 {
		return Summary{}
	}

	// Calculate mean
	var sum float64
	min := values[0]
	max := values[0]
	for _, v := range values {
		sum += v
		if v < min {
			min = v
		}
		if v > max {
			max = v
		}
	}
	mean := sum / float64(len(values))

	// Calculate standard deviation
	var sumSqDiff float64
	for _, v := range values {
		diff := v - mean
		sumSqDiff += diff * diff
	}
	stdDev := math.Sqrt(sumSqDiff / float64(len(values)))

	return Summary{
		Mean:   mean,
		StdDev: stdDev,
		Min:    min,
		Max:    max,
		N:      len(values),
	}
}

// CompareProportions compares two proportions and returns statistics
type ProportionComparison struct {
	P1          float64            `json:"p1"`
	P2          float64            `json:"p2"`
	P1CI        ConfidenceInterval `json:"p1_ci"`
	P2CI        ConfidenceInterval `json:"p2_ci"`
	Difference  float64            `json:"difference"`
	CohensH     float64            `json:"cohens_h"`
	EffectSize  string             `json:"effect_size"`
	Significant bool               `json:"significant"` // CIs don't overlap
}

// CompareProportions compares two proportions with confidence intervals
func CompareProportions(successes1, n1, successes2, n2 int) ProportionComparison {
	var p1, p2 float64
	if n1 > 0 {
		p1 = float64(successes1) / float64(n1)
	}
	if n2 > 0 {
		p2 = float64(successes2) / float64(n2)
	}

	ci1 := WilsonScore(successes1, n1, 0.95)
	ci2 := WilsonScore(successes2, n2, 0.95)

	h := CohensH(p1, p2)

	// Check if CIs overlap (simple significance test)
	significant := ci1.Upper < ci2.Lower || ci2.Upper < ci1.Lower

	return ProportionComparison{
		P1:          p1,
		P2:          p2,
		P1CI:        ci1,
		P2CI:        ci2,
		Difference:  p1 - p2,
		CohensH:     h,
		EffectSize:  EffectSizeInterpretation(h),
		Significant: significant,
	}
}
