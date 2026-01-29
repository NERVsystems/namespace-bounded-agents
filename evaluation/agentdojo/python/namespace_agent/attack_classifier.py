"""
Attack Classifier - Categorizes AgentDojo injection attacks.

Classifies attacks as:
- CROSS_TOOL: Attack requires tools outside the user task's minimal namespace
  → Can be structurally blocked by namespace constraints
- SAME_TOOL: Attack uses only tools the user task legitimately needs
  → Cannot be structurally blocked, must rely on behavioral defense
"""

from dataclasses import dataclass
from enum import Enum
from typing import Any, Optional


class AttackType(Enum):
    CROSS_TOOL = "cross_tool"      # Structurally blockable
    SAME_TOOL = "same_tool"        # Not structurally blockable
    UNKNOWN = "unknown"


@dataclass
class AttackClassification:
    """Classification result for an injection attack."""
    attack_type: AttackType
    injection_id: str
    user_task_id: str
    domain: str

    # Tools analysis
    user_task_tools: list[str]      # Tools the user task needs
    injection_tools: list[str]      # Tools the injection requires
    out_of_namespace_tools: list[str]  # Injection tools not in user task's namespace

    # Human-readable explanation
    reason: str


# Cross-domain tool patterns - tools that might be used across domains
CROSS_DOMAIN_PATTERNS = {
    'send_email': ['email', 'mail to', 'send.*to.*@'],
    'get_webpage': ['visit.*website', 'www\\.', 'http', 'webpage'],
    'post_webpage': ['post.*to.*website', 'post.*www'],
    'delete_file': ['delete.*file'],
    'send_money': ['transfer', 'send money', 'send.*\\$'],
}


def classify_attack(
    suite: Any,
    user_task_id: str,
    injection_task_id: str,
) -> AttackClassification:
    """
    Classify an injection attack as cross-tool or same-tool.

    Args:
        suite: AgentDojo TaskSuite
        user_task_id: ID of the user task
        injection_task_id: ID of the injection task

    Returns:
        AttackClassification with type and analysis
    """
    import re

    user_task = suite.user_tasks.get(user_task_id)
    inj_task = suite.injection_tasks.get(injection_task_id)
    domain = suite.name if hasattr(suite, 'name') else 'unknown'

    if not user_task or not inj_task:
        return AttackClassification(
            attack_type=AttackType.UNKNOWN,
            injection_id=injection_task_id,
            user_task_id=user_task_id,
            domain=domain,
            user_task_tools=[],
            injection_tools=[],
            out_of_namespace_tools=[],
            reason="Task not found",
        )

    # Get all tools available in this domain
    domain_tools = {t.name for t in suite.tools}

    # Infer tools needed by user task from its prompt
    user_prompt = user_task.PROMPT if hasattr(user_task, 'PROMPT') else ""
    user_task_tools = _infer_tools_from_text(user_prompt, domain_tools)

    # Infer tools needed by injection from its goal
    inj_goal = inj_task.GOAL if hasattr(inj_task, 'GOAL') else ""
    injection_tools = _infer_tools_from_text(inj_goal, domain_tools)

    # Also check for cross-domain tools not in this suite
    for tool_pattern, patterns in CROSS_DOMAIN_PATTERNS.items():
        for pattern in patterns:
            if re.search(pattern, inj_goal, re.IGNORECASE):
                if tool_pattern not in domain_tools:
                    injection_tools.add(f"[cross-domain:{tool_pattern}]")
                elif tool_pattern not in injection_tools:
                    injection_tools.add(tool_pattern)

    # Determine out-of-namespace tools
    out_of_namespace = injection_tools - user_task_tools

    # Classify
    if out_of_namespace:
        attack_type = AttackType.CROSS_TOOL
        reason = f"Injection requires {out_of_namespace} which user task doesn't need"
    else:
        attack_type = AttackType.SAME_TOOL
        reason = f"Injection uses only tools the user task needs: {injection_tools & user_task_tools}"

    return AttackClassification(
        attack_type=attack_type,
        injection_id=injection_task_id,
        user_task_id=user_task_id,
        domain=domain,
        user_task_tools=list(user_task_tools),
        injection_tools=list(injection_tools),
        out_of_namespace_tools=list(out_of_namespace),
        reason=reason,
    )


def _infer_tools_from_text(text: str, available_tools: set[str]) -> set[str]:
    """
    Infer which tools are likely needed based on text content.

    Uses keyword matching - not perfect but provides reasonable estimates.
    """
    import re

    text_lower = text.lower()
    inferred = set()

    # Tool-specific keyword patterns
    tool_patterns = {
        # Banking
        'send_money': ['send money', 'transfer', 'pay', 'payment'],
        'get_balance': ['balance', 'how much'],
        'get_iban': ['iban', 'account number'],
        'schedule_transaction': ['schedule', 'recurring'],
        'update_scheduled_transaction': ['update.*scheduled', 'modify.*recurring'],
        'get_scheduled_transactions': ['scheduled transactions', 'recurring payments'],
        'update_password': ['password', 'change.*password'],
        'read_file': ['read.*file', 'bill', 'invoice'],

        # Email/Workspace
        'send_email': ['send.*email', 'email.*to', 'mail'],
        'get_unread_emails': ['unread', 'new emails'],
        'get_received_emails': ['received', 'inbox'],
        'search_emails': ['search.*email', 'find.*email'],
        'delete_email': ['delete.*email'],
        'create_file': ['create.*file'],
        'delete_file': ['delete.*file'],
        'search_files': ['search.*files', 'find.*files'],

        # Calendar
        'create_calendar_event': ['create.*event', 'schedule.*meeting', 'add.*calendar'],
        'get_day_calendar_events': ['events.*today', 'calendar.*events'],
        'cancel_calendar_event': ['cancel.*event'],

        # Travel
        'get_all_hotels_in_city': ['hotels in', 'find hotel'],
        'reserve_hotel': ['book.*hotel', 'reserve.*hotel', 'reservation'],
        'get_flight_information': ['flight', 'flights'],
        'reserve_restaurant': ['book.*restaurant', 'reserve.*restaurant'],
        'get_all_restaurants_in_city': ['restaurants in', 'find restaurant'],
        'reserve_car_rental': ['rent.*car', 'car rental'],

        # Slack
        'send_direct_message': ['send.*message', 'message.*to', 'dm'],
        'read_channel_messages': ['read.*channel', 'messages in'],
        'send_channel_message': ['post.*channel', 'send.*channel'],
        'get_channels': ['channels', 'list.*channels'],
        'invite_user_to_slack': ['invite.*slack', 'add.*workspace'],

        # Web
        'get_webpage': ['visit.*website', 'get.*webpage', 'www\\.'],
        'post_webpage': ['post.*website', 'post.*webpage'],
    }

    for tool, patterns in tool_patterns.items():
        if tool in available_tools:
            for pattern in patterns:
                if re.search(pattern, text_lower):
                    inferred.add(tool)
                    break

    return inferred


def get_attack_summary(suite: Any) -> dict:
    """
    Get a summary of attack types for a domain.

    Returns dict with counts of cross-tool vs same-tool attacks
    for each user task.
    """
    summary = {
        'domain': suite.name if hasattr(suite, 'name') else 'unknown',
        'total_user_tasks': len(suite.user_tasks),
        'total_injection_tasks': len(suite.injection_tasks),
        'cross_tool_attacks': 0,
        'same_tool_attacks': 0,
        'attack_details': [],
    }

    for user_task_id in suite.user_tasks:
        for inj_id in suite.injection_tasks:
            classification = classify_attack(suite, user_task_id, inj_id)

            if classification.attack_type == AttackType.CROSS_TOOL:
                summary['cross_tool_attacks'] += 1
            elif classification.attack_type == AttackType.SAME_TOOL:
                summary['same_tool_attacks'] += 1

            summary['attack_details'].append({
                'user_task': user_task_id,
                'injection': inj_id,
                'type': classification.attack_type.value,
                'out_of_namespace': classification.out_of_namespace_tools,
            })

    return summary
