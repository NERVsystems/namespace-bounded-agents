// combined_server.go provides a unified 9P server combining all AgentDojo domains.
//
// The combined server supports two layout modes:
//
// Flat layout (AgentFS-compliant, default):
//
//	/list_accounts/query
//	/get_account_balance/query
//	/initiate_transfer/query
//	/send_email/query
//	... (33 tools at root level with action-verb names)
//
// Hierarchical layout (traditional):
//
//	/banking/...     - Banking tools (accounts, transfers)
//	/workspace/...   - Workspace tools (email, calendar, docs)
//	/travel/...      - Travel tools (flights, hotels, bookings)
//	/slack/...       - Slack tools (messages, channels, users)
//
// This allows cross-domain attacks to be evaluated (e.g., email injection
// triggering unauthorized banking transfers).
package servers

import (
	"context"
	"fmt"
	"log"
	"net"
	"os"
	"os/signal"
	"syscall"

	"github.com/NERVsystems/nerva-9p-paper/prototype/pkg/nerv9p"
)

// CombinedState holds the state for all domains.
type CombinedState struct {
	Banking   *BankingState
	Workspace *WorkspaceState
	Travel    *TravelState
	Slack     *SlackState
}

// NewCombinedState creates a new combined environment with default sample data.
func NewCombinedState() *CombinedState {
	return &CombinedState{
		Banking:   NewBankingState(),
		Workspace: NewWorkspaceState(),
		Travel:    NewTravelState(),
		Slack:     NewSlackState(),
	}
}

// CreateCombined9PServer creates a 9P server with all AgentDojo domains.
// Uses hierarchical layout by default.
func CreateCombined9PServer(state *CombinedState) *nerv9p.RootDir {
	return CreateCombined9PServerWithLayout(state, LayoutHierarchical)
}

// CreateCombined9PServerWithLayout creates a 9P server with the specified layout mode.
func CreateCombined9PServerWithLayout(state *CombinedState, layout LayoutMode) *nerv9p.RootDir {
	if layout == LayoutFlat {
		return CreateFlat9PServer(state)
	}

	// Hierarchical layout
	root := nerv9p.NewRootDir()

	// Create individual domain servers and merge their children into root
	bankingRoot := CreateBanking9PServer(state.Banking)
	workspaceRoot := CreateWorkspace9PServer(state.Workspace)
	travelRoot := CreateTravel9PServer(state.Travel)
	slackRoot := CreateSlack9PServer(state.Slack)

	// Merge all domain directories into root
	// Each domain server creates its own top-level directory (e.g., /banking, /workspace)
	for _, child := range bankingRoot.Children() {
		root.AddChild(child)
	}
	for _, child := range workspaceRoot.Children() {
		root.AddChild(child)
	}
	for _, child := range travelRoot.Children() {
		root.AddChild(child)
	}
	for _, child := range slackRoot.Children() {
		root.AddChild(child)
	}

	return root
}

// ServerConfig holds configuration for the combined server.
type ServerConfig struct {
	Address string     // TCP address to listen on (e.g., ":5640")
	Debug   bool       // Enable debug logging
	Layout  LayoutMode // Filesystem layout mode (default: LayoutFlat)
}

// DefaultServerConfig returns the default server configuration.
func DefaultServerConfig() *ServerConfig {
	return &ServerConfig{
		Address: ":5640",
		Debug:   false,
		Layout:  LayoutFlat, // AgentFS-compliant flat layout by default
	}
}

// RunCombinedServer starts the combined 9P server and blocks until shutdown.
func RunCombinedServer(cfg *ServerConfig) error {
	if cfg == nil {
		cfg = DefaultServerConfig()
	}

	// Create combined state
	state := NewCombinedState()

	// Create combined 9P server with configured layout
	root := CreateCombined9PServerWithLayout(state, cfg.Layout)
	srv := nerv9p.NewServer(root)
	srv.SetDebug(cfg.Debug)

	// Start listening
	listener, err := net.Listen("tcp", cfg.Address)
	if err != nil {
		return fmt.Errorf("failed to listen on %s: %w", cfg.Address, err)
	}
	defer listener.Close()

	layoutName := "flat"
	if cfg.Layout == LayoutHierarchical {
		layoutName = "hierarchical"
	}
	log.Printf("AgentDojo 9P server listening on %s (layout: %s)", cfg.Address, layoutName)
	log.Printf("Domains: banking, workspace, travel, slack")

	// Handle shutdown
	ctx, cancel := context.WithCancel(context.Background())
	defer cancel()

	go func() {
		sigCh := make(chan os.Signal, 1)
		signal.Notify(sigCh, syscall.SIGINT, syscall.SIGTERM)
		<-sigCh
		log.Println("Shutting down...")
		cancel()
		listener.Close()
	}()

	// Serve
	if err := srv.Serve(ctx, listener); err != nil && err != context.Canceled {
		return fmt.Errorf("server error: %w", err)
	}

	return nil
}

// NamespaceSpec describes which paths are available in a namespace.
// Used by the Python adapter to construct minimal namespaces for each task.
type NamespaceSpec struct {
	Name  string   `json:"name"`
	Paths []string `json:"paths"`
}

// AllPaths returns all available paths in the combined server.
// Defaults to flat layout.
func AllPaths() []string {
	return AllPathsWithLayout(LayoutFlat)
}

// AllPathsWithLayout returns all available paths for the specified layout.
func AllPathsWithLayout(layout LayoutMode) []string {
	if layout == LayoutFlat {
		return FlatAllPaths()
	}
	return HierarchicalAllPaths()
}

// HierarchicalAllPaths returns all paths in hierarchical layout.
func HierarchicalAllPaths() []string {
	return []string{
		// Banking
		"/banking/accounts/list/query",
		"/banking/accounts/balance/query",
		"/banking/accounts/history/query",
		"/banking/transfers/initiate/query",
		"/banking/transfers/schedule/query",
		"/banking/transfers/list/query",

		// Workspace
		"/workspace/email/send/query",
		"/workspace/email/read/query",
		"/workspace/email/search/query",
		"/workspace/email/list/query",
		"/workspace/calendar/create/query",
		"/workspace/calendar/list/query",
		"/workspace/calendar/delete/query",
		"/workspace/docs/read/query",
		"/workspace/docs/list/query",
		"/workspace/docs/write/query",

		// Travel
		"/travel/flights/search/query",
		"/travel/flights/book/query",
		"/travel/flights/cancel/query",
		"/travel/hotels/search/query",
		"/travel/hotels/book/query",
		"/travel/hotels/cancel/query",
		"/travel/bookings/list/query",
		"/travel/profile/view/query",

		// Slack
		"/slack/messages/send/query",
		"/slack/messages/read/query",
		"/slack/messages/search/query",
		"/slack/channels/list/query",
		"/slack/channels/create/query",
		"/slack/channels/join/query",
		"/slack/channels/info/query",
		"/slack/users/list/query",
		"/slack/users/lookup/query",
	}
}

// DomainPaths returns paths for a specific domain.
// For flat layout, filters by domain prefix in tool name.
func DomainPaths(domain string) []string {
	return DomainPathsWithLayout(domain, LayoutFlat)
}

// DomainPathsWithLayout returns paths for a specific domain with layout mode.
func DomainPathsWithLayout(domain string, layout LayoutMode) []string {
	if layout == LayoutFlat {
		// For flat layout, filter by domain mapping
		var result []string
		for tool, path := range FlatToolMapping {
			if len(tool) > len(domain) && tool[:len(domain)] == domain {
				result = append(result, path)
			}
		}
		return result
	}

	// Hierarchical layout - filter by path prefix
	all := HierarchicalAllPaths()
	var result []string
	prefix := "/" + domain + "/"
	for _, p := range all {
		if len(p) > len(prefix) && p[:len(prefix)] == prefix {
			result = append(result, p)
		}
	}
	return result
}

// MinimalNamespace constructs a minimal namespace for a specific task.
// This is the key innovation: the namespace IS the capability set.
func MinimalNamespace(taskTools []string) *NamespaceSpec {
	return MinimalNamespaceWithLayout(taskTools, LayoutFlat)
}

// MinimalNamespaceWithLayout constructs a minimal namespace with specified layout.
func MinimalNamespaceWithLayout(taskTools []string, layout LayoutMode) *NamespaceSpec {
	paths := make([]string, 0, len(taskTools))
	for _, tool := range taskTools {
		if layout == LayoutFlat {
			// Use flat tool mapping
			if path, ok := FlatToolMapping[tool]; ok {
				paths = append(paths, path)
			}
		} else {
			// Convert tool name to hierarchical path
			// e.g., "banking_accounts_list" -> "/banking/accounts/list/query"
			path := "/" + tool + "/query"
			// Replace underscores with slashes for hierarchical layout
			for i := 0; i < len(path); i++ {
				if path[i] == '_' {
					path = path[:i] + "/" + path[i+1:]
				}
			}
			paths = append(paths, path)
		}
	}
	return &NamespaceSpec{
		Name:  "task_namespace",
		Paths: paths,
	}
}

// FullNamespace returns the full namespace with all tools available.
// Used for utility comparison (matching MCP baseline capabilities).
func FullNamespace() *NamespaceSpec {
	return FullNamespaceWithLayout(LayoutFlat)
}

// FullNamespaceWithLayout returns the full namespace with specified layout.
func FullNamespaceWithLayout(layout LayoutMode) *NamespaceSpec {
	return &NamespaceSpec{
		Name:  "full_namespace",
		Paths: AllPathsWithLayout(layout),
	}
}

// HierarchicalToolMapping maps AgentDojo tool names to hierarchical paths.
var HierarchicalToolMapping = map[string]string{
	// Banking
	"banking_accounts_list":       "/banking/accounts/list/query",
	"banking_accounts_balance":    "/banking/accounts/balance/query",
	"banking_accounts_history":    "/banking/accounts/history/query",
	"banking_transfers_initiate":  "/banking/transfers/initiate/query",
	"banking_transfers_schedule":  "/banking/transfers/schedule/query",
	"banking_transfers_list":      "/banking/transfers/list/query",
	// Workspace
	"workspace_email_send":        "/workspace/email/send/query",
	"workspace_email_read":        "/workspace/email/read/query",
	"workspace_email_search":      "/workspace/email/search/query",
	"workspace_email_list":        "/workspace/email/list/query",
	"workspace_calendar_create":   "/workspace/calendar/create/query",
	"workspace_calendar_list":     "/workspace/calendar/list/query",
	"workspace_calendar_delete":   "/workspace/calendar/delete/query",
	"workspace_docs_read":         "/workspace/docs/read/query",
	"workspace_docs_list":         "/workspace/docs/list/query",
	"workspace_docs_write":        "/workspace/docs/write/query",
	// Travel
	"travel_flights_search":       "/travel/flights/search/query",
	"travel_flights_book":         "/travel/flights/book/query",
	"travel_flights_cancel":       "/travel/flights/cancel/query",
	"travel_hotels_search":        "/travel/hotels/search/query",
	"travel_hotels_book":          "/travel/hotels/book/query",
	"travel_hotels_cancel":        "/travel/hotels/cancel/query",
	"travel_bookings_list":        "/travel/bookings/list/query",
	"travel_profile_view":         "/travel/profile/view/query",
	// Slack
	"slack_messages_send":         "/slack/messages/send/query",
	"slack_messages_read":         "/slack/messages/read/query",
	"slack_messages_search":       "/slack/messages/search/query",
	"slack_channels_list":         "/slack/channels/list/query",
	"slack_channels_create":       "/slack/channels/create/query",
	"slack_channels_join":         "/slack/channels/join/query",
	"slack_channels_info":         "/slack/channels/info/query",
	"slack_users_list":            "/slack/users/list/query",
	"slack_users_lookup":          "/slack/users/lookup/query",
}
