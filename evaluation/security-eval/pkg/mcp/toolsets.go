// Package mcp provides tool set definitions for hardened MCP experiments.
//
// Each attack category gets the minimal set of tools needed for legitimate tasks.
// This simulates "task-appropriate tool exposure" - an MCP best practice.
package mcp

import "github.com/NERVsystems/nerva-9p-paper/experiments/security-eval/attacks"

// MinimalToolSet returns the smallest set of tools needed for legitimate tasks.
// Most attacks only need geocode to appear legitimate.
var MinimalToolSet = []string{"geocode"}

// NearbyToolSet adds nearby for tasks that legitimately need location search.
var NearbyToolSet = []string{"geocode", "nearby"}

// FullToolSet includes all OSM tools (used for comparison only).
var FullToolSet = []string{"geocode", "nearby", "distance", "reverse", "centroid"}

// ToolSetForCategory returns the minimal tool set for a given attack category.
// This simulates "task-appropriate tool exposure" - MCP best practice.
//
// Rationale:
//   - PT (Path Traversal): geocode - Legitimate: look up address
//   - TD (Tool Discovery): geocode - Legitimate: look up address
//   - UE (Unauthorized Exec): geocode - Legitimate: look up address
//   - IPI (Indirect Injection): geocode, nearby - Cross-tool, needs both
//   - CM (Capability Misuse): geocode - DoS via allowed tool
//   - CT (Cross-Tool Chain): geocode, nearby - Cross-tool, needs both
//   - SA (Session Pollution): geocode - Session attacks
//   - ITI (In-Tool Injection): geocode - Parameter injection
//   - CE (Capability Escalation): geocode - Mount/bind attacks
func ToolSetForCategory(cat attacks.AttackCategory) []string {
	switch cat {
	case attacks.IndirectInjection, attacks.CrossToolChain:
		// These attacks try cross-tool exploitation, so we give them nearby too
		return NearbyToolSet
	default:
		// All other attacks only need geocode to be legitimate
		return MinimalToolSet
	}
}

// ToolSetForCategoryString is like ToolSetForCategory but takes a string.
func ToolSetForCategoryString(cat string) []string {
	return ToolSetForCategory(attacks.AttackCategory(cat))
}

// AllToolSets returns a map of category to tool set for documentation/analysis.
func AllToolSets() map[string][]string {
	return map[string][]string{
		string(attacks.PathTraversal):        MinimalToolSet,
		string(attacks.ToolDiscovery):        MinimalToolSet,
		string(attacks.UnauthorizedExec):     MinimalToolSet,
		string(attacks.IndirectInjection):    NearbyToolSet,
		string(attacks.CapabilityMisuse):     MinimalToolSet,
		string(attacks.CrossToolChain):       NearbyToolSet,
		string(attacks.SessionPollution):     MinimalToolSet,
		string(attacks.InToolInjection):      MinimalToolSet,
		string(attacks.CapabilityEscalation): MinimalToolSet,
	}
}
