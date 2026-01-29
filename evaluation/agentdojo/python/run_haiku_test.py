#!/usr/bin/env python3
"""
Quick test of evaluation with Haiku model.

Haiku is more compliant with instruction prompts and may generate
the filesystem commands we need to demonstrate structural blocking.
"""

import sys
import os
import logging

sys.path.insert(0, '.')

from namespace_agent.evaluator import NamespaceEvaluator
from namespace_agent.agent import AgentConfig

logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(name)s - %(levelname)s - %(message)s')
logger = logging.getLogger(__name__)


def main():
    """Run quick evaluation with Haiku."""
    print("=" * 60)
    print("Running Quick Evaluation with Haiku Model")
    print("=" * 60)

    # Configure for Haiku
    config = AgentConfig(
        server_address="localhost:5640",
        model="claude-3-haiku-20240307",  # Use Haiku
        max_tokens=4096,
        temperature=0.0,
        use_minimal_namespace=True,
        track_defense_mode=True,
    )

    evaluator = NamespaceEvaluator(
        agent_config=config,
        output_dir="./results/haiku_test",
    )

    print("\nConfiguration:")
    print(f"  Model: {config.model}")
    print(f"  Namespace mode: minimal")
    print(f"  Layout: flat")

    # Run on just banking domain with a few tasks
    print("\nRunning evaluation on banking domain...")
    print("(This may take a few minutes)\n")

    try:
        results = evaluator.run_full_evaluation(
            domains=["banking"],
            namespace_mode="minimal",
            layout_mode="flat",
        )

        print("\n" + "=" * 60)
        print("RESULTS")
        print("=" * 60)
        print(f"\nTasks evaluated: {results.tasks_evaluated}")
        print(f"\nCore metrics:")
        print(f"  Benign Utility (BU): {results.benign_utility * 100:.1f}%")
        print(f"  Utility Under Attack (UA): {results.utility_under_attack * 100:.1f}%")
        print(f"  Attack Success Rate (ASR): {results.attack_success_rate * 100:.1f}%")

        print(f"\nDefense breakdown:")
        print(f"  Structural blocks: {results.structural_blocks}")
        print(f"  Behavioral blocks: {results.behavioral_blocks}")
        print(f"  Unblocked attacks: {results.unblocked_attacks}")

        print(f"\nAttack type breakdown:")
        print(f"  Cross-tool attacks: {results.cross_tool_attacks}")
        print(f"  Same-tool attacks: {results.same_tool_attacks}")

        # Check for structural blocking in individual results
        structural_examples = [
            r for r in results.task_results
            if r.blocked_paths
        ]
        if structural_examples:
            print(f"\nStructural blocking examples found: {len(structural_examples)}")
            for r in structural_examples[:3]:
                print(f"  Task: {r.task_id}")
                print(f"    Attempted: {r.attempted_paths}")
                print(f"    Blocked: {r.blocked_paths}")
        else:
            print("\nNo structural blocking examples found in results.")
            print("(LLM may not have generated out-of-namespace commands)")

    except Exception as e:
        print(f"\n✗ Evaluation failed: {e}")
        import traceback
        traceback.print_exc()
        return 1

    print("\n" + "=" * 60)
    print("Evaluation complete!")
    print("=" * 60)
    return 0


if __name__ == "__main__":
    sys.exit(main())
