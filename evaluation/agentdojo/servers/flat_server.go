// flat_server.go provides an AgentFS-compliant flat layout 9P server.
//
// This implements the AgentFS specification from the design patterns paper:
// - MUST be flat (all tools at root level)
// - MUST use action-verb naming (get_, list_, send_, etc.)
// - SHOULD use shim pattern (single query file)
// - SHOULD include _example only (not _types)
//
// Flat paths:
//   /list_accounts/query
//   /get_account_balance/query
//   /initiate_transfer/query
//   /send_email/query
//   etc.
package servers

import (
	"github.com/NERVsystems/nerva-9p-paper/prototype/pkg/nerv9p"
)

// LayoutMode determines the filesystem layout for tool organization.
type LayoutMode int

const (
	// LayoutFlat uses AgentFS-compliant flat layout with action-verb names.
	// Tools appear at root: /get_account_balance/query
	LayoutFlat LayoutMode = iota

	// LayoutHierarchical uses traditional hierarchical layout.
	// Tools appear in domain directories: /banking/accounts/balance/query
	LayoutHierarchical
)

// CreateFlat9PServer creates a 9P server with all tools at root level.
// This follows the AgentFS specification for optimal LLM interaction.
func CreateFlat9PServer(state *CombinedState) *nerv9p.RootDir {
	root := nerv9p.NewRootDir()

	// Banking tools (6)
	addBankingFlatTools(root, state.Banking)

	// Workspace tools (10)
	addWorkspaceFlatTools(root, state.Workspace)

	// Travel tools (8)
	addTravelFlatTools(root, state.Travel)

	// Slack tools (9)
	addSlackFlatTools(root, state.Slack)

	return root
}

// addBankingFlatTools adds banking domain tools with action-verb naming.
func addBankingFlatTools(root *nerv9p.RootDir, state *BankingState) {
	// list_accounts
	root.AddChild(nerv9p.NewTypeATool(nerv9p.TypeAConfig{
		Name: "list_accounts",
		Handler: func(input []byte) ([]byte, error) {
			return state.handleAccountsList(input)
		},
		Example: "echo '{}' > query && cat query",
	}))

	// get_account_balance
	root.AddChild(nerv9p.NewTypeBTool(nerv9p.TypeBConfig{
		Name:     "get_account_balance",
		Params:   []string{"account_id"},
		Required: []string{"account_id"},
		Handler: func(params map[string]string) ([]byte, error) {
			return state.handleAccountBalance(params)
		},
		Example: "echo 'account_id=acct_checking_001' > query && cat query",
	}))

	// get_account_history
	root.AddChild(nerv9p.NewTypeBTool(nerv9p.TypeBConfig{
		Name:     "get_account_history",
		Params:   []string{"account_id", "count"},
		Required: []string{"account_id"},
		Handler: func(params map[string]string) ([]byte, error) {
			return state.handleAccountHistory(params)
		},
		Example: "echo 'account_id=acct_checking_001 count=10' > query && cat query",
	}))

	// initiate_transfer (security-relevant)
	root.AddChild(nerv9p.NewTypeBTool(nerv9p.TypeBConfig{
		Name:     "initiate_transfer",
		Params:   []string{"from_account", "to_account", "amount", "description"},
		Required: []string{"from_account", "to_account", "amount"},
		Handler: func(params map[string]string) ([]byte, error) {
			return state.handleTransferInitiate(params)
		},
		Example: "echo 'from_account=acct_checking_001 to_account=acct_savings_001 amount=100.00' > query && cat query",
	}))

	// schedule_transfer (security-relevant)
	root.AddChild(nerv9p.NewTypeBTool(nerv9p.TypeBConfig{
		Name:     "schedule_transfer",
		Params:   []string{"from_account", "to_account", "amount", "date", "description"},
		Required: []string{"from_account", "to_account", "amount", "date"},
		Handler: func(params map[string]string) ([]byte, error) {
			return state.handleTransferSchedule(params)
		},
		Example: "echo 'from_account=acct_checking_001 to_account=acct_savings_001 amount=500.00 date=2024-02-01' > query && cat query",
	}))

	// list_transfers
	root.AddChild(nerv9p.NewTypeBTool(nerv9p.TypeBConfig{
		Name:     "list_transfers",
		Params:   []string{"status"},
		Required: []string{},
		Handler: func(params map[string]string) ([]byte, error) {
			return state.handleTransfersList(params)
		},
		Example: "echo 'status=pending' > query && cat query",
	}))
}

// addWorkspaceFlatTools adds workspace domain tools with action-verb naming.
func addWorkspaceFlatTools(root *nerv9p.RootDir, state *WorkspaceState) {
	// send_email (security-relevant)
	root.AddChild(nerv9p.NewTypeBTool(nerv9p.TypeBConfig{
		Name:     "send_email",
		Params:   []string{"to", "subject", "body"},
		Required: []string{"to", "subject", "body"},
		Handler: func(params map[string]string) ([]byte, error) {
			return state.handleEmailSend(params)
		},
		Example: "echo 'to=recipient@example.com subject=Hello body=Hi there' > query && cat query",
	}))

	// read_email
	root.AddChild(nerv9p.NewTypeBTool(nerv9p.TypeBConfig{
		Name:     "read_email",
		Params:   []string{"email_id"},
		Required: []string{"email_id"},
		Handler: func(params map[string]string) ([]byte, error) {
			return state.handleEmailRead(params)
		},
		Example: "echo 'email_id=email_001' > query && cat query",
	}))

	// search_emails
	root.AddChild(nerv9p.NewTypeBTool(nerv9p.TypeBConfig{
		Name:     "search_emails",
		Params:   []string{"query", "folder", "limit"},
		Required: []string{},
		Handler: func(params map[string]string) ([]byte, error) {
			return state.handleEmailSearch(params)
		},
		Example: "echo 'query=meeting folder=inbox limit=10' > query && cat query",
	}))

	// list_emails
	root.AddChild(nerv9p.NewTypeBTool(nerv9p.TypeBConfig{
		Name:     "list_emails",
		Params:   []string{"folder", "limit"},
		Required: []string{},
		Handler: func(params map[string]string) ([]byte, error) {
			return state.handleEmailList(params)
		},
		Example: "echo 'folder=inbox limit=20' > query && cat query",
	}))

	// create_calendar_event
	root.AddChild(nerv9p.NewTypeBTool(nerv9p.TypeBConfig{
		Name:     "create_calendar_event",
		Params:   []string{"title", "description", "start_time", "end_time", "location", "attendees"},
		Required: []string{"title", "start_time", "end_time"},
		Handler: func(params map[string]string) ([]byte, error) {
			return state.handleCalendarCreate(params)
		},
		Example: "echo 'title=Meeting start_time=2024-01-15T14:00:00Z end_time=2024-01-15T15:00:00Z' > query && cat query",
	}))

	// list_calendar_events
	root.AddChild(nerv9p.NewTypeBTool(nerv9p.TypeBConfig{
		Name:     "list_calendar_events",
		Params:   []string{"start_date", "end_date"},
		Required: []string{},
		Handler: func(params map[string]string) ([]byte, error) {
			return state.handleCalendarList(params)
		},
		Example: "echo 'start_date=2024-01-01 end_date=2024-01-31' > query && cat query",
	}))

	// delete_calendar_event (security-relevant)
	root.AddChild(nerv9p.NewTypeBTool(nerv9p.TypeBConfig{
		Name:     "delete_calendar_event",
		Params:   []string{"event_id"},
		Required: []string{"event_id"},
		Handler: func(params map[string]string) ([]byte, error) {
			return state.handleCalendarDelete(params)
		},
		Example: "echo 'event_id=cal_001' > query && cat query",
	}))

	// read_document
	root.AddChild(nerv9p.NewTypeBTool(nerv9p.TypeBConfig{
		Name:     "read_document",
		Params:   []string{"doc_id"},
		Required: []string{"doc_id"},
		Handler: func(params map[string]string) ([]byte, error) {
			return state.handleDocRead(params)
		},
		Example: "echo 'doc_id=doc_001' > query && cat query",
	}))

	// list_documents
	root.AddChild(nerv9p.NewTypeBTool(nerv9p.TypeBConfig{
		Name:     "list_documents",
		Params:   []string{"owner"},
		Required: []string{},
		Handler: func(params map[string]string) ([]byte, error) {
			return state.handleDocList(params)
		},
		Example: "echo '' > query && cat query",
	}))

	// write_document (security-relevant)
	root.AddChild(nerv9p.NewTypeBTool(nerv9p.TypeBConfig{
		Name:     "write_document",
		Params:   []string{"doc_id", "title", "content"},
		Required: []string{"title", "content"},
		Handler: func(params map[string]string) ([]byte, error) {
			return state.handleDocWrite(params)
		},
		Example: "echo 'title=New Doc content=Document content here' > query && cat query",
	}))
}

// addTravelFlatTools adds travel domain tools with action-verb naming.
func addTravelFlatTools(root *nerv9p.RootDir, state *TravelState) {
	// search_flights
	root.AddChild(nerv9p.NewTypeBTool(nerv9p.TypeBConfig{
		Name:     "search_flights",
		Params:   []string{"origin", "destination", "date", "passengers"},
		Required: []string{"origin", "destination", "date"},
		Handler: func(params map[string]string) ([]byte, error) {
			return state.handleFlightSearch(params)
		},
		Example: "echo 'origin=LAX destination=JFK date=2024-02-15 passengers=1' > query && cat query",
	}))

	// book_flight (security-relevant)
	root.AddChild(nerv9p.NewTypeBTool(nerv9p.TypeBConfig{
		Name:     "book_flight",
		Params:   []string{"flight_id", "passengers"},
		Required: []string{"flight_id"},
		Handler: func(params map[string]string) ([]byte, error) {
			return state.handleFlightBook(params)
		},
		Example: "echo 'flight_id=FL001 passengers=John Doe' > query && cat query",
	}))

	// cancel_flight (security-relevant)
	root.AddChild(nerv9p.NewTypeBTool(nerv9p.TypeBConfig{
		Name:     "cancel_flight",
		Params:   []string{"booking_id"},
		Required: []string{"booking_id"},
		Handler: func(params map[string]string) ([]byte, error) {
			return state.handleFlightCancel(params)
		},
		Example: "echo 'booking_id=BK001' > query && cat query",
	}))

	// search_hotels
	root.AddChild(nerv9p.NewTypeBTool(nerv9p.TypeBConfig{
		Name:     "search_hotels",
		Params:   []string{"location", "check_in", "check_out", "guests"},
		Required: []string{"location", "check_in", "check_out"},
		Handler: func(params map[string]string) ([]byte, error) {
			return state.handleHotelSearch(params)
		},
		Example: "echo 'location=New York check_in=2024-02-15 check_out=2024-02-18 guests=2' > query && cat query",
	}))

	// book_hotel (security-relevant)
	root.AddChild(nerv9p.NewTypeBTool(nerv9p.TypeBConfig{
		Name:     "book_hotel",
		Params:   []string{"hotel_id", "check_in", "check_out", "guests"},
		Required: []string{"hotel_id", "check_in", "check_out"},
		Handler: func(params map[string]string) ([]byte, error) {
			return state.handleHotelBook(params)
		},
		Example: "echo 'hotel_id=HT001 check_in=2024-02-15 check_out=2024-02-18' > query && cat query",
	}))

	// cancel_hotel (security-relevant)
	root.AddChild(nerv9p.NewTypeBTool(nerv9p.TypeBConfig{
		Name:     "cancel_hotel",
		Params:   []string{"booking_id"},
		Required: []string{"booking_id"},
		Handler: func(params map[string]string) ([]byte, error) {
			return state.handleHotelCancel(params)
		},
		Example: "echo 'booking_id=BK002' > query && cat query",
	}))

	// list_bookings
	root.AddChild(nerv9p.NewTypeBTool(nerv9p.TypeBConfig{
		Name:     "list_bookings",
		Params:   []string{"type", "status"},
		Required: []string{},
		Handler: func(params map[string]string) ([]byte, error) {
			return state.handleBookingsList(params)
		},
		Example: "echo 'type=flight status=confirmed' > query && cat query",
	}))

	// view_travel_profile (security-relevant)
	root.AddChild(nerv9p.NewTypeATool(nerv9p.TypeAConfig{
		Name: "view_travel_profile",
		Handler: func(input []byte) ([]byte, error) {
			return state.handleProfileView()
		},
		Example: "echo '' > query && cat query",
	}))
}

// addSlackFlatTools adds Slack domain tools with action-verb naming.
func addSlackFlatTools(root *nerv9p.RootDir, state *SlackState) {
	// send_slack_message (security-relevant)
	root.AddChild(nerv9p.NewTypeBTool(nerv9p.TypeBConfig{
		Name:     "send_slack_message",
		Params:   []string{"channel", "message"},
		Required: []string{"channel", "message"},
		Handler: func(params map[string]string) ([]byte, error) {
			return state.handleMessageSend(params)
		},
		Example: "echo 'channel=general message=Hello team!' > query && cat query",
	}))

	// read_slack_messages
	root.AddChild(nerv9p.NewTypeBTool(nerv9p.TypeBConfig{
		Name:     "read_slack_messages",
		Params:   []string{"channel", "limit"},
		Required: []string{"channel"},
		Handler: func(params map[string]string) ([]byte, error) {
			return state.handleMessageRead(params)
		},
		Example: "echo 'channel=general limit=20' > query && cat query",
	}))

	// search_slack_messages
	root.AddChild(nerv9p.NewTypeBTool(nerv9p.TypeBConfig{
		Name:     "search_slack_messages",
		Params:   []string{"query", "channel"},
		Required: []string{"query"},
		Handler: func(params map[string]string) ([]byte, error) {
			return state.handleMessageSearch(params)
		},
		Example: "echo 'query=project channel=general' > query && cat query",
	}))

	// list_slack_channels
	root.AddChild(nerv9p.NewTypeBTool(nerv9p.TypeBConfig{
		Name:     "list_slack_channels",
		Params:   []string{},
		Required: []string{},
		Handler: func(params map[string]string) ([]byte, error) {
			return state.handleChannelList(params)
		},
		Example: "echo '' > query && cat query",
	}))

	// create_slack_channel (security-relevant)
	root.AddChild(nerv9p.NewTypeBTool(nerv9p.TypeBConfig{
		Name:     "create_slack_channel",
		Params:   []string{"name", "description", "private"},
		Required: []string{"name"},
		Handler: func(params map[string]string) ([]byte, error) {
			return state.handleChannelCreate(params)
		},
		Example: "echo 'name=new-project description=Project channel private=false' > query && cat query",
	}))

	// join_slack_channel (security-relevant)
	root.AddChild(nerv9p.NewTypeBTool(nerv9p.TypeBConfig{
		Name:     "join_slack_channel",
		Params:   []string{"channel"},
		Required: []string{"channel"},
		Handler: func(params map[string]string) ([]byte, error) {
			return state.handleChannelJoin(params)
		},
		Example: "echo 'channel=new-channel' > query && cat query",
	}))

	// get_slack_channel_info
	root.AddChild(nerv9p.NewTypeBTool(nerv9p.TypeBConfig{
		Name:     "get_slack_channel_info",
		Params:   []string{"channel"},
		Required: []string{"channel"},
		Handler: func(params map[string]string) ([]byte, error) {
			return state.handleChannelInfo(params)
		},
		Example: "echo 'channel=general' > query && cat query",
	}))

	// list_slack_users
	root.AddChild(nerv9p.NewTypeBTool(nerv9p.TypeBConfig{
		Name:     "list_slack_users",
		Params:   []string{},
		Required: []string{},
		Handler: func(params map[string]string) ([]byte, error) {
			return state.handleUserList(params)
		},
		Example: "echo '' > query && cat query",
	}))

	// lookup_slack_user
	root.AddChild(nerv9p.NewTypeBTool(nerv9p.TypeBConfig{
		Name:     "lookup_slack_user",
		Params:   []string{"username", "email"},
		Required: []string{},
		Handler: func(params map[string]string) ([]byte, error) {
			return state.handleUserLookup(params)
		},
		Example: "echo 'username=johndoe' > query && cat query",
	}))
}

// FlatAllPaths returns all paths in flat layout.
func FlatAllPaths() []string {
	return []string{
		// Banking (6)
		"/list_accounts/query",
		"/get_account_balance/query",
		"/get_account_history/query",
		"/initiate_transfer/query",
		"/schedule_transfer/query",
		"/list_transfers/query",
		// Workspace (10)
		"/send_email/query",
		"/read_email/query",
		"/search_emails/query",
		"/list_emails/query",
		"/create_calendar_event/query",
		"/list_calendar_events/query",
		"/delete_calendar_event/query",
		"/read_document/query",
		"/list_documents/query",
		"/write_document/query",
		// Travel (8)
		"/search_flights/query",
		"/book_flight/query",
		"/cancel_flight/query",
		"/search_hotels/query",
		"/book_hotel/query",
		"/cancel_hotel/query",
		"/list_bookings/query",
		"/view_travel_profile/query",
		// Slack (9)
		"/send_slack_message/query",
		"/read_slack_messages/query",
		"/search_slack_messages/query",
		"/list_slack_channels/query",
		"/create_slack_channel/query",
		"/join_slack_channel/query",
		"/get_slack_channel_info/query",
		"/list_slack_users/query",
		"/lookup_slack_user/query",
	}
}

// FlatSecurityRelevantPaths returns security-sensitive paths in flat layout.
func FlatSecurityRelevantPaths() []string {
	return []string{
		// Banking
		"/initiate_transfer/query",
		"/schedule_transfer/query",
		// Workspace
		"/send_email/query",
		"/write_document/query",
		"/delete_calendar_event/query",
		// Travel
		"/book_flight/query",
		"/book_hotel/query",
		"/cancel_flight/query",
		"/cancel_hotel/query",
		"/view_travel_profile/query",
		// Slack
		"/send_slack_message/query",
		"/create_slack_channel/query",
		"/join_slack_channel/query",
	}
}

// FlatToolMapping maps AgentDojo tool names to flat paths.
var FlatToolMapping = map[string]string{
	// Banking
	"banking_accounts_list":       "/list_accounts/query",
	"banking_accounts_balance":    "/get_account_balance/query",
	"banking_accounts_history":    "/get_account_history/query",
	"banking_transfers_initiate":  "/initiate_transfer/query",
	"banking_transfers_schedule":  "/schedule_transfer/query",
	"banking_transfers_list":      "/list_transfers/query",
	// Workspace
	"workspace_email_send":        "/send_email/query",
	"workspace_email_read":        "/read_email/query",
	"workspace_email_search":      "/search_emails/query",
	"workspace_email_list":        "/list_emails/query",
	"workspace_calendar_create":   "/create_calendar_event/query",
	"workspace_calendar_list":     "/list_calendar_events/query",
	"workspace_calendar_delete":   "/delete_calendar_event/query",
	"workspace_docs_read":         "/read_document/query",
	"workspace_docs_list":         "/list_documents/query",
	"workspace_docs_write":        "/write_document/query",
	// Travel
	"travel_flights_search":       "/search_flights/query",
	"travel_flights_book":         "/book_flight/query",
	"travel_flights_cancel":       "/cancel_flight/query",
	"travel_hotels_search":        "/search_hotels/query",
	"travel_hotels_book":          "/book_hotel/query",
	"travel_hotels_cancel":        "/cancel_hotel/query",
	"travel_bookings_list":        "/list_bookings/query",
	"travel_profile_view":         "/view_travel_profile/query",
	// Slack
	"slack_messages_send":         "/send_slack_message/query",
	"slack_messages_read":         "/read_slack_messages/query",
	"slack_messages_search":       "/search_slack_messages/query",
	"slack_channels_list":         "/list_slack_channels/query",
	"slack_channels_create":       "/create_slack_channel/query",
	"slack_channels_join":         "/join_slack_channel/query",
	"slack_channels_info":         "/get_slack_channel_info/query",
	"slack_users_list":            "/list_slack_users/query",
	"slack_users_lookup":          "/lookup_slack_user/query",
}
