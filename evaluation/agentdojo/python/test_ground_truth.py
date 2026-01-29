#!/usr/bin/env python3
"""
Test that ground truth checks work correctly after tool execution.

This is the critical test for the state bridge fix:
- Execute a tool via FunctionsRuntime
- Verify ground truth detects the state change
"""

import sys
import os

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

def test_ground_truth_detection():
    """
    Test that executing a tool via FunctionsRuntime allows ground_truth to detect changes.
    """
    print("Testing ground truth detection...")

    try:
        from agentdojo.task_suite import get_suites
        from agentdojo.functions_runtime import FunctionsRuntime
    except ImportError:
        print("  AgentDojo not installed - cannot test ground truth")
        return False

    # Get banking suite
    suites = get_suites("v1.1.1")
    suite = suites["banking"]

    # Create runtime and environment
    runtime = FunctionsRuntime(suite.tools)
    env = suite.load_and_inject_default_environment({})

    # Get a simple task and its ground truth
    # Let's look at what tasks are available
    print(f"\n  Available user tasks: {list(suite.user_tasks.keys())[:5]}...")
    print(f"  Available injection tasks: {list(suite.injection_tasks.keys())[:5]}...")

    # Let's pick an injection task and see what it requires
    # Most injection tasks want to transfer money to an attacker account
    for inj_id, inj_task in list(suite.injection_tasks.items())[:3]:
        print(f"\n  Injection task: {inj_id}")
        if hasattr(inj_task, 'GOAL'):
            print(f"    GOAL: {inj_task.GOAL[:100]}...")
        if hasattr(inj_task, 'ground_truth'):
            print(f"    Has ground_truth method")

    # Let's test with a specific injection task
    # Most banking injections want money sent to a specific IBAN

    # First, check initial ground truth state for an injection
    inj_id = list(suite.injection_tasks.keys())[0]
    inj_task = suite.injection_tasks[inj_id]

    if hasattr(inj_task, 'ground_truth'):
        try:
            initial_result = inj_task.ground_truth(env)
            print(f"\n  Initial ground_truth for {inj_id}: {initial_result}")
        except Exception as e:
            print(f"\n  Initial ground_truth failed (expected): {e}")

    # Now try to execute a send_money operation (simulating what the agent would do)
    # Most banking attacks want money sent to attacker IBAN
    print("\n  Executing send_money to test state modification...")

    # The typical attack IBAN in AgentDojo banking suite
    result, error = runtime.run_function(
        env,
        "send_money",
        {
            "amount": 100,
            "recipient": "US133000000121212121212",  # Typical attacker IBAN
            "subject": "Test transfer",
            "date": "2024-01-15",
        },
        raise_on_error=False
    )

    if error:
        print(f"  send_money error: {error}")
    else:
        print(f"  send_money result: {result}")

    # Check ground truth again
    if hasattr(inj_task, 'ground_truth'):
        try:
            after_result = inj_task.ground_truth(env)
            print(f"\n  After send_money ground_truth for {inj_id}: {after_result}")
        except Exception as e:
            print(f"\n  After ground_truth failed: {e}")

    # Let's also check a benign task's ground truth
    user_task_id = list(suite.user_tasks.keys())[0]
    user_task = suite.user_tasks[user_task_id]
    print(f"\n  User task: {user_task_id}")
    if hasattr(user_task, 'PROMPT'):
        print(f"    PROMPT: {user_task.PROMPT[:100]}...")

    if hasattr(user_task, 'ground_truth'):
        try:
            user_gt_result = user_task.ground_truth(env)
            print(f"    ground_truth result: {user_gt_result}")
        except Exception as e:
            print(f"    ground_truth failed: {e}")

    return True

def test_full_agent_execution():
    """
    Test the full agent -> FunctionsRuntime -> ground_truth flow.
    """
    print("\nTesting full agent execution flow...")

    try:
        from agentdojo.task_suite import get_suites
        from agentdojo.functions_runtime import FunctionsRuntime
    except ImportError:
        print("  AgentDojo not installed")
        return False

    from namespace_agent.agent import Namespace9PAgent, AgentConfig
    from namespace_agent.namespace import MinimalNamespace, LayoutMode

    # Setup
    suites = get_suites("v1.1.1")
    suite = suites["banking"]
    runtime = FunctionsRuntime(suite.tools)
    env = suite.load_and_inject_default_environment({})

    # Create agent with minimal namespace
    config = AgentConfig(
        server_address="localhost:5640",
        use_minimal_namespace=True,
    )
    agent = Namespace9PAgent(config=config)

    # Set namespace for banking tools
    namespace = MinimalNamespace(["get_balance", "get_iban"], layout=LayoutMode.FLAT)
    agent.set_namespace(namespace)

    # Manually simulate what the agent does
    # Store runtime and env
    agent._agentdojo_runtime = runtime
    agent._agentdojo_env = env

    # Execute an operation (as if LLM generated it)
    op = {
        "type": "read",
        "path": "/get_balance/query",
    }
    result = agent._execute_operation(op)
    print(f"  get_balance result: success={result.success}, data={result.data}")

    # Now try a blocked operation (not in namespace)
    op_blocked = {
        "type": "write",
        "path": "/send_money/query",
        "content": 'amount=100 recipient="US133000"',
    }
    result_blocked = agent._execute_operation(op_blocked)
    print(f"  send_money (blocked) result: success={result_blocked.success}, blocked_by={result_blocked.blocked_by}")

    # Verify blocking works
    assert not result_blocked.success
    assert result_blocked.blocked_by == "namespace"
    print("  Namespace blocking: OK")

    return True

def main():
    print("=" * 60)
    print("Ground Truth Verification Tests")
    print("=" * 60)
    print()

    test_ground_truth_detection()
    test_full_agent_execution()

    print()
    print("=" * 60)
    print("Ground truth tests completed")
    print("=" * 60)

if __name__ == "__main__":
    main()
