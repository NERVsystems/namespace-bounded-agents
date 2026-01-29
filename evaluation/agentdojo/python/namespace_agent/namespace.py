"""
NamespaceSpec - Defines the capability set for a namespace-bounded agent.

The namespace IS the capability set. An agent can only access paths that
exist in its namespace. This module provides utilities for constructing
and validating namespaces.

Supports two layout modes per AgentFS specification:
- FLAT: Action-verb naming at root level (AgentFS-compliant, optimal for LLMs)
- HIERARCHICAL: Domain-based nesting (traditional REST-style)
"""

from dataclasses import dataclass, field
from enum import Enum
from typing import Optional


class LayoutMode(Enum):
    """Layout mode for filesystem interface."""
    FLAT = "flat"           # AgentFS-compliant: /get_account_balance/query
    HIERARCHICAL = "hier"   # Traditional: /banking/accounts/balance/query


# =============================================================================
# FLAT LAYOUT (AgentFS-compliant)
# Action-verb naming at root level per design patterns paper findings
# =============================================================================

# Mapping from AgentDojo tool names to flat filesystem paths
# These are the ACTUAL AgentDojo tool names from each domain
AGENTDOJO_TO_PATH = {
    # Banking domain (from agentdojo.task_suite banking)
    "get_iban": "/get_iban/query",
    "send_money": "/send_money/query",
    "schedule_transaction": "/schedule_transaction/query",
    "update_scheduled_transaction": "/update_scheduled_transaction/query",
    "get_balance": "/get_balance/query",
    "get_most_recent_transactions": "/get_most_recent_transactions/query",
    "get_scheduled_transactions": "/get_scheduled_transactions/query",
    "read_file": "/read_file/query",
    "get_user_info": "/get_user_info/query",
    "update_password": "/update_password/query",
    "update_user_info": "/update_user_info/query",

    # Workspace domain (from agentdojo.task_suite workspace)
    "send_email": "/send_email/query",
    "delete_email": "/delete_email/query",
    "get_unread_emails": "/get_unread_emails/query",
    "get_sent_emails": "/get_sent_emails/query",
    "get_received_emails": "/get_received_emails/query",
    "get_draft_emails": "/get_draft_emails/query",
    "search_emails": "/search_emails/query",
    "search_contacts_by_name": "/search_contacts_by_name/query",
    "search_contacts_by_email": "/search_contacts_by_email/query",
    "get_current_day": "/get_current_day/query",
    "search_calendar_events": "/search_calendar_events/query",
    "get_day_calendar_events": "/get_day_calendar_events/query",
    "create_calendar_event": "/create_calendar_event/query",
    "cancel_calendar_event": "/cancel_calendar_event/query",
    "reschedule_calendar_event": "/reschedule_calendar_event/query",
    "add_calendar_event_participants": "/add_calendar_event_participants/query",
    "append_to_file": "/append_to_file/query",
    "search_files_by_filename": "/search_files_by_filename/query",
    "create_file": "/create_file/query",
    "delete_file": "/delete_file/query",
    "get_file_by_id": "/get_file_by_id/query",
    "list_files": "/list_files/query",
    "share_file": "/share_file/query",
    "search_files": "/search_files/query",

    # Travel domain (from agentdojo.task_suite travel)
    "get_user_information": "/get_user_information/query",
    "get_all_hotels_in_city": "/get_all_hotels_in_city/query",
    "get_hotels_prices": "/get_hotels_prices/query",
    "get_rating_reviews_for_hotels": "/get_rating_reviews_for_hotels/query",
    "get_hotels_address": "/get_hotels_address/query",
    "get_all_restaurants_in_city": "/get_all_restaurants_in_city/query",
    "get_cuisine_type_for_restaurants": "/get_cuisine_type_for_restaurants/query",
    "get_restaurants_address": "/get_restaurants_address/query",
    "get_rating_reviews_for_restaurants": "/get_rating_reviews_for_restaurants/query",
    "get_dietary_restrictions_for_all_restaurants": "/get_dietary_restrictions_for_all_restaurants/query",
    "get_contact_information_for_restaurants": "/get_contact_information_for_restaurants/query",
    "get_price_for_restaurants": "/get_price_for_restaurants/query",
    "check_restaurant_opening_hours": "/check_restaurant_opening_hours/query",
    "get_all_car_rental_companies_in_city": "/get_all_car_rental_companies_in_city/query",
    "get_car_types_available": "/get_car_types_available/query",
    "get_rating_reviews_for_car_rental": "/get_rating_reviews_for_car_rental/query",
    "get_car_fuel_options": "/get_car_fuel_options/query",
    "get_car_rental_address": "/get_car_rental_address/query",
    "get_car_price_per_day": "/get_car_price_per_day/query",
    "reserve_hotel": "/reserve_hotel/query",
    "reserve_car_rental": "/reserve_car_rental/query",
    "reserve_restaurant": "/reserve_restaurant/query",
    "get_flight_information": "/get_flight_information/query",

    # Slack domain (from agentdojo.task_suite slack)
    "get_channels": "/get_channels/query",
    "add_user_to_channel": "/add_user_to_channel/query",
    "read_channel_messages": "/read_channel_messages/query",
    "read_inbox": "/read_inbox/query",
    "send_direct_message": "/send_direct_message/query",
    "send_channel_message": "/send_channel_message/query",
    "get_users_in_channel": "/get_users_in_channel/query",
    "invite_user_to_slack": "/invite_user_to_slack/query",
    "remove_user_from_slack": "/remove_user_from_slack/query",
    "get_webpage": "/get_webpage/query",
    "post_webpage": "/post_webpage/query",
}

# Reverse mapping: path -> AgentDojo tool name
PATH_TO_AGENTDOJO = {v: k for k, v in AGENTDOJO_TO_PATH.items()}

# Legacy mapping (kept for backward compatibility)
FLAT_TOOL_PATH_MAPPING = {
    # Banking domain - 6 tools
    "banking_accounts_list": "/list_accounts/query",
    "banking_accounts_balance": "/get_account_balance/query",
    "banking_accounts_history": "/get_account_history/query",
    "banking_transfers_initiate": "/initiate_transfer/query",
    "banking_transfers_schedule": "/schedule_transfer/query",
    "banking_transfers_list": "/list_transfers/query",

    # Workspace domain - 10 tools
    "workspace_email_send": "/send_email/query",
    "workspace_email_read": "/read_email/query",
    "workspace_email_search": "/search_emails/query",
    "workspace_email_list": "/list_emails/query",
    "workspace_calendar_create": "/create_calendar_event/query",
    "workspace_calendar_list": "/list_calendar_events/query",
    "workspace_calendar_delete": "/delete_calendar_event/query",
    "workspace_docs_read": "/read_document/query",
    "workspace_docs_list": "/list_documents/query",
    "workspace_docs_write": "/write_document/query",

    # Travel domain - 8 tools
    "travel_flights_search": "/search_flights/query",
    "travel_flights_book": "/book_flight/query",
    "travel_flights_cancel": "/cancel_flight/query",
    "travel_hotels_search": "/search_hotels/query",
    "travel_hotels_book": "/book_hotel/query",
    "travel_hotels_cancel": "/cancel_hotel/query",
    "travel_bookings_list": "/list_bookings/query",
    "travel_profile_view": "/view_travel_profile/query",

    # Slack domain - 9 tools
    "slack_messages_send": "/send_slack_message/query",
    "slack_messages_read": "/read_slack_messages/query",
    "slack_messages_search": "/search_slack_messages/query",
    "slack_channels_list": "/list_slack_channels/query",
    "slack_channels_create": "/create_slack_channel/query",
    "slack_channels_join": "/join_slack_channel/query",
    "slack_channels_info": "/get_slack_channel_info/query",
    "slack_users_list": "/list_slack_users/query",
    "slack_users_lookup": "/lookup_slack_user/query",
}

# All flat paths organized by domain (using actual AgentDojo tool names)
FLAT_ALL_PATHS = {
    "banking": [
        "/get_iban/query",
        "/send_money/query",
        "/schedule_transaction/query",
        "/update_scheduled_transaction/query",
        "/get_balance/query",
        "/get_most_recent_transactions/query",
        "/get_scheduled_transactions/query",
        "/read_file/query",
        "/get_user_info/query",
        "/update_password/query",
        "/update_user_info/query",
    ],
    "workspace": [
        "/send_email/query",
        "/delete_email/query",
        "/get_unread_emails/query",
        "/get_sent_emails/query",
        "/get_received_emails/query",
        "/get_draft_emails/query",
        "/search_emails/query",
        "/search_contacts_by_name/query",
        "/search_contacts_by_email/query",
        "/get_current_day/query",
        "/search_calendar_events/query",
        "/get_day_calendar_events/query",
        "/create_calendar_event/query",
        "/cancel_calendar_event/query",
        "/reschedule_calendar_event/query",
        "/add_calendar_event_participants/query",
        "/append_to_file/query",
        "/search_files_by_filename/query",
        "/create_file/query",
        "/delete_file/query",
        "/get_file_by_id/query",
        "/list_files/query",
        "/share_file/query",
        "/search_files/query",
    ],
    "travel": [
        "/get_user_information/query",
        "/get_all_hotels_in_city/query",
        "/get_hotels_prices/query",
        "/get_rating_reviews_for_hotels/query",
        "/get_hotels_address/query",
        "/get_all_restaurants_in_city/query",
        "/get_cuisine_type_for_restaurants/query",
        "/get_restaurants_address/query",
        "/get_rating_reviews_for_restaurants/query",
        "/get_dietary_restrictions_for_all_restaurants/query",
        "/get_contact_information_for_restaurants/query",
        "/get_price_for_restaurants/query",
        "/check_restaurant_opening_hours/query",
        "/get_all_car_rental_companies_in_city/query",
        "/get_car_types_available/query",
        "/get_rating_reviews_for_car_rental/query",
        "/get_car_fuel_options/query",
        "/get_car_rental_address/query",
        "/get_car_price_per_day/query",
        "/create_calendar_event/query",
        "/search_calendar_events/query",
        "/get_day_calendar_events/query",
        "/cancel_calendar_event/query",
        "/reserve_hotel/query",
        "/reserve_car_rental/query",
        "/reserve_restaurant/query",
        "/get_flight_information/query",
        "/send_email/query",
    ],
    "slack": [
        "/get_channels/query",
        "/add_user_to_channel/query",
        "/read_channel_messages/query",
        "/read_inbox/query",
        "/send_direct_message/query",
        "/send_channel_message/query",
        "/get_users_in_channel/query",
        "/invite_user_to_slack/query",
        "/remove_user_from_slack/query",
        "/get_webpage/query",
        "/post_webpage/query",
    ],
}

# Security-relevant tools (attack targets) - flat paths using actual AgentDojo names
FLAT_SECURITY_RELEVANT = [
    # Banking - unauthorized transfers
    "/send_money/query",
    "/schedule_transaction/query",
    "/update_scheduled_transaction/query",
    "/update_password/query",
    "/update_user_info/query",
    # Workspace - data exfiltration
    "/send_email/query",
    "/delete_email/query",
    "/create_file/query",
    "/delete_file/query",
    "/share_file/query",
    "/cancel_calendar_event/query",
    # Travel - sensitive data/reservations
    "/reserve_hotel/query",
    "/reserve_car_rental/query",
    "/reserve_restaurant/query",
    # Slack - cross-channel injection
    "/send_direct_message/query",
    "/send_channel_message/query",
    "/add_user_to_channel/query",
    "/invite_user_to_slack/query",
    "/remove_user_from_slack/query",
    "/post_webpage/query",
]


# =============================================================================
# HIERARCHICAL LAYOUT (Traditional)
# Domain-based nesting, REST-style naming
# =============================================================================

HIER_TOOL_PATH_MAPPING = {
    # Banking domain
    "banking_accounts_list": "/banking/accounts/list/query",
    "banking_accounts_balance": "/banking/accounts/balance/query",
    "banking_accounts_history": "/banking/accounts/history/query",
    "banking_transfers_initiate": "/banking/transfers/initiate/query",
    "banking_transfers_schedule": "/banking/transfers/schedule/query",
    "banking_transfers_list": "/banking/transfers/list/query",

    # Workspace domain
    "workspace_email_send": "/workspace/email/send/query",
    "workspace_email_read": "/workspace/email/read/query",
    "workspace_email_search": "/workspace/email/search/query",
    "workspace_email_list": "/workspace/email/list/query",
    "workspace_calendar_create": "/workspace/calendar/create/query",
    "workspace_calendar_list": "/workspace/calendar/list/query",
    "workspace_calendar_delete": "/workspace/calendar/delete/query",
    "workspace_docs_read": "/workspace/docs/read/query",
    "workspace_docs_list": "/workspace/docs/list/query",
    "workspace_docs_write": "/workspace/docs/write/query",

    # Travel domain
    "travel_flights_search": "/travel/flights/search/query",
    "travel_flights_book": "/travel/flights/book/query",
    "travel_flights_cancel": "/travel/flights/cancel/query",
    "travel_hotels_search": "/travel/hotels/search/query",
    "travel_hotels_book": "/travel/hotels/book/query",
    "travel_hotels_cancel": "/travel/hotels/cancel/query",
    "travel_bookings_list": "/travel/bookings/list/query",
    "travel_profile_view": "/travel/profile/view/query",

    # Slack domain
    "slack_messages_send": "/slack/messages/send/query",
    "slack_messages_read": "/slack/messages/read/query",
    "slack_messages_search": "/slack/messages/search/query",
    "slack_channels_list": "/slack/channels/list/query",
    "slack_channels_create": "/slack/channels/create/query",
    "slack_channels_join": "/slack/channels/join/query",
    "slack_channels_info": "/slack/channels/info/query",
    "slack_users_list": "/slack/users/list/query",
    "slack_users_lookup": "/slack/users/lookup/query",
}

HIER_ALL_PATHS = {
    "banking": [
        "/banking/accounts/list/query",
        "/banking/accounts/balance/query",
        "/banking/accounts/history/query",
        "/banking/transfers/initiate/query",
        "/banking/transfers/schedule/query",
        "/banking/transfers/list/query",
    ],
    "workspace": [
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
    ],
    "travel": [
        "/travel/flights/search/query",
        "/travel/flights/book/query",
        "/travel/flights/cancel/query",
        "/travel/hotels/search/query",
        "/travel/hotels/book/query",
        "/travel/hotels/cancel/query",
        "/travel/bookings/list/query",
        "/travel/profile/view/query",
    ],
    "slack": [
        "/slack/messages/send/query",
        "/slack/messages/read/query",
        "/slack/messages/search/query",
        "/slack/channels/list/query",
        "/slack/channels/create/query",
        "/slack/channels/join/query",
        "/slack/channels/info/query",
        "/slack/users/list/query",
        "/slack/users/lookup/query",
    ],
}

HIER_SECURITY_RELEVANT = [
    "/banking/transfers/initiate/query",
    "/banking/transfers/schedule/query",
    "/workspace/email/send/query",
    "/workspace/docs/write/query",
    "/workspace/calendar/delete/query",
    "/travel/profile/view/query",
    "/travel/flights/book/query",
    "/travel/hotels/book/query",
    "/travel/flights/cancel/query",
    "/travel/hotels/cancel/query",
    "/slack/messages/send/query",
    "/slack/channels/create/query",
    "/slack/channels/join/query",
]


# =============================================================================
# Legacy aliases for backward compatibility
# =============================================================================

TOOL_PATH_MAPPING = HIER_TOOL_PATH_MAPPING
ALL_PATHS = HIER_ALL_PATHS


# =============================================================================
# Layout-aware functions
# =============================================================================

def get_tool_path_mapping(layout: LayoutMode = LayoutMode.FLAT) -> dict[str, str]:
    """Get tool path mapping for the specified layout."""
    if layout == LayoutMode.FLAT:
        return FLAT_TOOL_PATH_MAPPING
    return HIER_TOOL_PATH_MAPPING


def get_all_paths(layout: LayoutMode = LayoutMode.FLAT) -> dict[str, list[str]]:
    """Get all paths organized by domain for the specified layout."""
    if layout == LayoutMode.FLAT:
        return FLAT_ALL_PATHS
    return HIER_ALL_PATHS


def get_security_relevant_paths(layout: LayoutMode = LayoutMode.FLAT) -> list[str]:
    """Get security-relevant paths for the specified layout."""
    if layout == LayoutMode.FLAT:
        return FLAT_SECURITY_RELEVANT
    return HIER_SECURITY_RELEVANT


@dataclass
class NamespaceSpec:
    """
    Specification of a namespace (capability set).

    A namespace defines which paths are accessible to an agent. This is
    the core security mechanism: an agent cannot name (and therefore
    cannot access) paths outside its namespace.
    """

    name: str
    paths: list[str] = field(default_factory=list)
    layout: LayoutMode = LayoutMode.FLAT
    _path_set: set[str] = field(default_factory=set, repr=False)

    def __post_init__(self):
        """Build the path set for efficient lookup."""
        self._path_set = set(self.paths)
        # Also include parent directories
        for path in self.paths:
            parts = path.strip("/").split("/")
            for i in range(len(parts)):
                parent = "/" + "/".join(parts[:i+1])
                self._path_set.add(parent)

    def contains(self, path: str) -> bool:
        """
        Check if a path is accessible within this namespace.

        A path is accessible if:
        1. It matches exactly a path in the namespace, OR
        2. It is a parent directory of a path in the namespace, OR
        3. It is under a path in the namespace

        Args:
            path: Path to check

        Returns:
            True if path is accessible
        """
        path = self._normalize(path)

        # Direct match
        if path in self._path_set:
            return True

        # Check if path is under any allowed path
        for allowed in self.paths:
            allowed = self._normalize(allowed)
            if path.startswith(allowed + "/"):
                return True
            if allowed.startswith(path + "/"):
                return True

        return False

    def restrict(self, name: str, paths: list[str]) -> "NamespaceSpec":
        """
        Create a child namespace with a subset of this namespace's paths.

        Args:
            name: Name for the child namespace
            paths: Paths to include (must be subset of this namespace)

        Returns:
            New NamespaceSpec with restricted paths

        Raises:
            ValueError: If any path is not in this namespace
        """
        for path in paths:
            if not self.contains(path):
                raise ValueError(f"Cannot grant path {path}: not in parent namespace")

        return NamespaceSpec(name=name, paths=paths, layout=self.layout)

    def to_prompt(self) -> str:
        """
        Generate a namespace listing suitable for LLM consumption.

        For FLAT layout: simple list at root level (AgentFS-compliant)
        For HIERARCHICAL layout: grouped by directory

        Returns:
            Human-readable listing of available paths
        """
        lines = ["Available namespace:", "$ ls -R /"]

        if self.layout == LayoutMode.FLAT:
            # Flat layout: just list tool directories at root
            lines.append("\n/:")
            for path in sorted(self.paths):
                # Extract tool directory name (e.g., /get_account_balance/query -> get_account_balance)
                parts = path.strip("/").split("/")
                if parts:
                    lines.append(f"  {parts[0]}/")
        else:
            # Hierarchical layout: group by directory
            dirs: dict[str, list[str]] = {}
            for path in sorted(self.paths):
                parts = path.strip("/").split("/")
                if len(parts) >= 2:
                    dir_path = "/" + "/".join(parts[:-1])
                    if dir_path not in dirs:
                        dirs[dir_path] = []
                    dirs[dir_path].append(parts[-1])

            # Format as ls -R output
            for dir_path in sorted(dirs.keys()):
                lines.append(f"\n{dir_path}:")
                for file_name in sorted(dirs[dir_path]):
                    lines.append(f"  {file_name}")

        return "\n".join(lines)

    @staticmethod
    def _normalize(path: str) -> str:
        """Normalize a path."""
        path = path.strip()
        if not path.startswith("/"):
            path = "/" + path
        # Remove trailing slash
        while len(path) > 1 and path.endswith("/"):
            path = path[:-1]
        return path


def MinimalNamespace(
    tool_names: list[str],
    layout: LayoutMode = LayoutMode.FLAT
) -> NamespaceSpec:
    """
    Construct a minimal namespace for a specific set of tools.

    This is the key security mechanism: given the tools required for a
    task, construct the smallest namespace that allows those tools.
    Any attempt to access tools outside this namespace will fail.

    Args:
        tool_names: List of AgentDojo tool names (e.g., ["get_balance", "send_money"])
        layout: Layout mode (FLAT or HIERARCHICAL)

    Returns:
        NamespaceSpec with only the required paths
    """
    paths = []

    for tool_name in tool_names:
        if layout == LayoutMode.FLAT:
            # Use AGENTDOJO_TO_PATH mapping for actual AgentDojo tool names
            if tool_name in AGENTDOJO_TO_PATH:
                paths.append(AGENTDOJO_TO_PATH[tool_name])
            else:
                # Fallback: construct path from tool name
                paths.append(f"/{tool_name}/query")
        else:
            # Hierarchical layout - use legacy mapping or construct
            mapping = get_tool_path_mapping(layout)
            if tool_name in mapping:
                paths.append(mapping[tool_name])
            else:
                # Fallback: convert underscores to slashes
                converted = "/" + tool_name.replace("_", "/") + "/query"
                paths.append(converted)

    return NamespaceSpec(name="minimal", paths=paths, layout=layout)


def FullNamespace(layout: LayoutMode = LayoutMode.FLAT) -> NamespaceSpec:
    """
    Construct a namespace with all available tools.

    Used for utility comparison - gives the agent full access matching
    a standard MCP baseline.

    Args:
        layout: Layout mode (FLAT or HIERARCHICAL)

    Returns:
        NamespaceSpec with all paths
    """
    all_paths_dict = get_all_paths(layout)
    all_paths = []
    for domain_paths in all_paths_dict.values():
        all_paths.extend(domain_paths)
    return NamespaceSpec(name="full", paths=all_paths, layout=layout)


def DomainNamespace(domain: str, layout: LayoutMode = LayoutMode.FLAT) -> NamespaceSpec:
    """
    Construct a namespace for a specific domain.

    Args:
        domain: Domain name (banking, workspace, travel, slack)
        layout: Layout mode (FLAT or HIERARCHICAL)

    Returns:
        NamespaceSpec with paths for that domain
    """
    all_paths_dict = get_all_paths(layout)
    if domain not in all_paths_dict:
        raise ValueError(f"Unknown domain: {domain}")

    return NamespaceSpec(name=domain, paths=all_paths_dict[domain], layout=layout)


def TaskNamespace(
    task_id: str,
    required_tools: list[str],
    security_relevant_tools: Optional[list[str]] = None,
    layout: LayoutMode = LayoutMode.FLAT
) -> tuple[NamespaceSpec, NamespaceSpec]:
    """
    Construct namespaces for evaluating a specific AgentDojo task.

    Returns two namespaces:
    1. Security namespace: Minimal set required for the task (for security testing)
    2. Utility namespace: Full namespace (for fair utility comparison)

    Args:
        task_id: AgentDojo task identifier
        required_tools: Tools needed to complete the task benignly
        security_relevant_tools: Additional tools that attacks might try to access
        layout: Layout mode (FLAT or HIERARCHICAL)

    Returns:
        Tuple of (security_namespace, utility_namespace)
    """
    security_ns = MinimalNamespace(required_tools, layout)
    utility_ns = FullNamespace(layout)

    return security_ns, utility_ns
