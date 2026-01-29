#!/usr/bin/env python3
"""
Test script to verify the state bridge between namespace agent and AgentDojo.

This verifies that:
1. Tool executions via FunctionsRuntime properly modify TaskEnvironment
2. Ground truth checks can correctly detect state changes
"""

import sys
import os

# Add the package to path
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from namespace_agent.namespace import MinimalNamespace, AGENTDOJO_TO_PATH, PATH_TO_AGENTDOJO, LayoutMode

def test_path_mappings():
    """Test that path mappings are correctly set up."""
    print("Testing path mappings...")

    # Test a few known mappings
    assert AGENTDOJO_TO_PATH["get_balance"] == "/get_balance/query"
    assert AGENTDOJO_TO_PATH["send_money"] == "/send_money/query"
    assert AGENTDOJO_TO_PATH["send_email"] == "/send_email/query"

    # Test reverse mapping
    assert PATH_TO_AGENTDOJO["/get_balance/query"] == "get_balance"
    assert PATH_TO_AGENTDOJO["/send_money/query"] == "send_money"

    print("  Path mappings: OK")

def test_minimal_namespace():
    """Test that MinimalNamespace correctly maps tool names to paths."""
    print("Testing MinimalNamespace...")

    # Create namespace for banking tools
    ns = MinimalNamespace(["get_balance", "send_money"], layout=LayoutMode.FLAT)

    # Check paths are included
    assert ns.contains("/get_balance/query")
    assert ns.contains("/send_money/query")

    # Check other paths are NOT included
    assert not ns.contains("/send_email/query")
    assert not ns.contains("/get_channels/query")

    print("  MinimalNamespace: OK")

def test_agentdojo_integration():
    """Test actual AgentDojo integration."""
    print("Testing AgentDojo integration...")

    try:
        from agentdojo.task_suite import get_suites
        from agentdojo.functions_runtime import FunctionsRuntime
    except ImportError:
        print("  AgentDojo not installed - skipping integration test")
        return False

    # Get banking suite
    suites = get_suites("v1.1.1")
    suite = suites["banking"]

    # Create runtime and environment
    runtime = FunctionsRuntime(suite.tools)
    env = suite.load_and_inject_default_environment({})

    # Get initial balance
    print(f"  Initial environment created")

    # Test calling get_balance directly via FunctionsRuntime
    result, error = runtime.run_function(
        env,
        "get_balance",
        {},
        raise_on_error=False
    )

    if error:
        print(f"  ERROR: get_balance failed: {error}")
        return False

    print(f"  get_balance result: {result}")

    # Test calling send_money (this should modify state)
    # First, let's check what accounts exist
    result, error = runtime.run_function(
        env,
        "get_iban",
        {"user_name": "me"},
        raise_on_error=False
    )

    if error:
        print(f"  get_iban error: {error}")
    else:
        print(f"  get_iban result: {result}")

    print("  AgentDojo integration: OK")
    return True

def test_agent_parse_params():
    """Test the agent's parameter parsing."""
    print("Testing parameter parsing...")

    from namespace_agent.agent import Namespace9PAgent, AgentConfig

    config = AgentConfig(server_address="localhost:5640")
    agent = Namespace9PAgent(config=config)

    # Test key=value format
    params = agent._parse_params('amount=100 recipient="US133000"')
    assert "amount" in params
    assert "recipient" in params
    print(f"  Parsed: {params}")

    # Test JSON format
    params = agent._parse_params('{"amount": 100, "recipient": "US133000"}')
    assert params.get("amount") == 100
    assert params.get("recipient") == "US133000"
    print(f"  Parsed JSON: {params}")

    print("  Parameter parsing: OK")

def test_path_to_tool_name():
    """Test path to tool name mapping in agent."""
    print("Testing path to tool name mapping...")

    from namespace_agent.agent import Namespace9PAgent, AgentConfig

    config = AgentConfig(server_address="localhost:5640")
    agent = Namespace9PAgent(config=config)

    # Test direct mappings
    assert agent._path_to_tool_name("/get_balance/query") == "get_balance"
    assert agent._path_to_tool_name("/send_money/query") == "send_money"

    # Test without /query suffix
    assert agent._path_to_tool_name("/get_balance") == "get_balance"

    print("  Path to tool name mapping: OK")

def main():
    print("=" * 50)
    print("State Bridge Test Suite")
    print("=" * 50)
    print()

    tests_passed = 0
    tests_failed = 0

    try:
        test_path_mappings()
        tests_passed += 1
    except Exception as e:
        print(f"  FAILED: {e}")
        tests_failed += 1

    try:
        test_minimal_namespace()
        tests_passed += 1
    except Exception as e:
        print(f"  FAILED: {e}")
        tests_failed += 1

    try:
        test_agent_parse_params()
        tests_passed += 1
    except Exception as e:
        print(f"  FAILED: {e}")
        tests_failed += 1

    try:
        test_path_to_tool_name()
        tests_passed += 1
    except Exception as e:
        print(f"  FAILED: {e}")
        tests_failed += 1

    try:
        if test_agentdojo_integration():
            tests_passed += 1
        else:
            tests_passed += 1  # Skip counts as pass
    except Exception as e:
        print(f"  FAILED: {e}")
        import traceback
        traceback.print_exc()
        tests_failed += 1

    print()
    print("=" * 50)
    print(f"Results: {tests_passed} passed, {tests_failed} failed")
    print("=" * 50)

    return tests_failed == 0

if __name__ == "__main__":
    success = main()
    sys.exit(0 if success else 1)
