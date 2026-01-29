#!/usr/bin/env python3
"""
generate_paper_results.py - Generate LaTeX tables and figures for paper

This script processes AgentDojo evaluation results and generates
publication-ready LaTeX tables and analysis for the paper.

Usage:
    python3 generate_paper_results.py <results_dir>

Example:
    python3 generate_paper_results.py results/20240115_143022
"""

import argparse
import json
import os
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Optional


@dataclass
class BaselineMetrics:
    """Published baseline metrics from AgentDojo paper."""
    name: str
    bu: float  # Benign Utility
    ua: float  # Utility under Attack
    asr: float  # Attack Success Rate


# Published baselines from AgentDojo (Table 2)
BASELINES = {
    "gpt-4o": BaselineMetrics("GPT-4o", 69.0, 45.0, 53.1),
    "gpt-4o-mini": BaselineMetrics("GPT-4o-mini", 60.0, 30.0, 54.6),
    "claude-3.5-sonnet": BaselineMetrics("Claude-3.5-Sonnet", 65.0, 55.0, 35.0),
    "claude-3-opus": BaselineMetrics("Claude-3-Opus", 58.0, 48.0, 38.0),
}


def load_results(results_dir: str) -> dict:
    """Load evaluation results from directory."""
    results = {}

    # Load security mode results
    security_file = Path(results_dir) / "security_results.json"
    if security_file.exists():
        with open(security_file) as f:
            results["security"] = json.load(f)

    # Load utility mode results
    utility_file = Path(results_dir) / "utility_results.json"
    if utility_file.exists():
        with open(utility_file) as f:
            results["utility"] = json.load(f)

    # Load combined summary if available
    summary_file = Path(results_dir) / "summary.json"
    if summary_file.exists():
        with open(summary_file) as f:
            results["summary"] = json.load(f)

    return results


def generate_main_comparison_table(results: dict) -> str:
    """Generate Table 1: Main comparison with baselines."""

    # Get our metrics
    security = results.get("security", {})
    utility = results.get("utility", {})

    our_bu = utility.get("benign_utility", 0) * 100
    our_ua = security.get("utility_under_attack", 0) * 100
    our_asr = security.get("attack_success_rate", 0) * 100

    latex = r"""
\begin{table}[t]
\centering
\caption{AgentDojo benchmark comparison. BU = Benign Utility (\%), UA = Utility under Attack (\%), ASR = Attack Success Rate (\%). Lower ASR is better. Baseline values from \citet{debenedetti2024agentdojo}.}
\label{tab:agentdojo-comparison}
\begin{tabular}{lccc}
\toprule
\textbf{Agent} & \textbf{BU} $\uparrow$ & \textbf{UA} $\uparrow$ & \textbf{ASR} $\downarrow$ \\
\midrule
"""

    # Add baselines
    for key in ["gpt-4o", "claude-3.5-sonnet", "claude-3-opus"]:
        baseline = BASELINES[key]
        latex += f"{baseline.name} & {baseline.bu:.1f} & {baseline.ua:.1f} & {baseline.asr:.1f} \\\\\n"

    # Add our results
    latex += r"\midrule" + "\n"
    latex += f"\\textbf{{Namespace-Bounded}} & {our_bu:.1f} & {our_ua:.1f} & \\textbf{{{our_asr:.1f}}} \\\\\n"

    latex += r"""
\bottomrule
\end{tabular}
\end{table}
"""

    return latex


def generate_defense_breakdown_table(results: dict) -> str:
    """Generate Table 2: Defense mode breakdown."""

    security = results.get("security", {})
    defense = security.get("defense_breakdown", {})

    structural = defense.get("structural", 0)
    behavioral = defense.get("behavioral", 0)
    not_blocked = defense.get("not_blocked", 0)
    total = structural + behavioral + not_blocked

    if total > 0:
        structural_pct = structural / total * 100
        behavioral_pct = behavioral / total * 100
        not_blocked_pct = not_blocked / total * 100
    else:
        structural_pct = behavioral_pct = not_blocked_pct = 0

    latex = r"""
\begin{table}[t]
\centering
\caption{Defense mode breakdown. Structural blocking occurs when the attack path doesn't exist in the agent's namespace. Behavioral blocking occurs when the LLM refuses despite valid paths.}
\label{tab:defense-breakdown}
\begin{tabular}{lrr}
\toprule
\textbf{Defense Mode} & \textbf{Count} & \textbf{Percentage} \\
\midrule
"""

    latex += f"Structural (namespace) & {structural} & {structural_pct:.1f}\\% \\\\\n"
    latex += f"Behavioral (LLM refusal) & {behavioral} & {behavioral_pct:.1f}\\% \\\\\n"
    latex += f"Not blocked & {not_blocked} & {not_blocked_pct:.1f}\\% \\\\\n"

    latex += r"""
\midrule
"""
    latex += f"\\textbf{{Total attacks}} & {total} & 100.0\\% \\\\\n"

    latex += r"""
\bottomrule
\end{tabular}
\end{table}
"""

    return latex


def generate_domain_breakdown_table(results: dict) -> str:
    """Generate Table 3: Per-domain results."""

    security = results.get("security", {})
    by_domain = security.get("by_domain", {})

    latex = r"""
\begin{table}[t]
\centering
\caption{Results by AgentDojo domain. UA = Utility under Attack (\%), ASR = Attack Success Rate (\%).}
\label{tab:domain-breakdown}
\begin{tabular}{lcccc}
\toprule
\textbf{Domain} & \textbf{Tasks} & \textbf{Attacks} & \textbf{UA} $\uparrow$ & \textbf{ASR} $\downarrow$ \\
\midrule
"""

    for domain in ["banking", "workspace", "travel", "slack"]:
        if domain in by_domain:
            d = by_domain[domain]
            tasks = d.get("tasks", 0)
            attacks = d.get("attacks", 0)
            ua = d.get("utility_under_attack", 0) * 100
            asr = d.get("attack_success_rate", 0) * 100
            latex += f"{domain.capitalize()} & {tasks} & {attacks} & {ua:.1f} & {asr:.1f} \\\\\n"
        else:
            latex += f"{domain.capitalize()} & -- & -- & -- & -- \\\\\n"

    latex += r"""
\bottomrule
\end{tabular}
\end{table}
"""

    return latex


def generate_attack_category_table(results: dict) -> str:
    """Generate Table 4: Attack category analysis."""

    security = results.get("security", {})
    by_category = security.get("by_attack_category", {})

    latex = r"""
\begin{table}[t]
\centering
\caption{Attack success rate by category. Cross-tool attacks require accessing tools outside the minimal namespace.}
\label{tab:attack-categories}
\begin{tabular}{lcccc}
\toprule
\textbf{Attack Category} & \textbf{Total} & \textbf{Blocked} & \textbf{Structural} & \textbf{ASR} $\downarrow$ \\
\midrule
"""

    categories = [
        ("cross_tool", "Cross-tool injection"),
        ("same_tool_misuse", "Same-tool misuse"),
        ("data_exfiltration", "Data exfiltration"),
        ("privilege_escalation", "Privilege escalation"),
    ]

    for key, name in categories:
        if key in by_category:
            cat = by_category[key]
            total = cat.get("total", 0)
            blocked = cat.get("blocked", 0)
            structural = cat.get("structural", 0)
            asr = cat.get("asr", 0) * 100
            latex += f"{name} & {total} & {blocked} & {structural} & {asr:.1f}\\% \\\\\n"
        else:
            latex += f"{name} & -- & -- & -- & -- \\\\\n"

    latex += r"""
\bottomrule
\end{tabular}
\end{table}
"""

    return latex


def generate_tikz_figure(results: dict) -> str:
    """Generate TikZ figure for ASR comparison."""

    security = results.get("security", {})
    our_asr = security.get("attack_success_rate", 0) * 100

    latex = r"""
\begin{figure}[t]
\centering
\begin{tikzpicture}
\begin{axis}[
    ybar,
    bar width=15pt,
    ylabel={Attack Success Rate (\%)},
    symbolic x coords={GPT-4o,Claude-3.5,Claude-3-Opus,Namespace},
    xtick=data,
    ymin=0,
    ymax=60,
    nodes near coords,
    nodes near coords align={vertical},
    legend style={at={(0.5,-0.15)},anchor=north},
]
\addplot[fill=gray!50] coordinates {
    (GPT-4o, 53.1)
    (Claude-3.5, 35.0)
    (Claude-3-Opus, 38.0)
"""
    latex += f"    (Namespace, {our_asr:.1f})\n"
    latex += r"""
};
\end{axis}
\end{tikzpicture}
\caption{Attack success rate comparison. Lower is better. Namespace-bounded agent achieves significantly lower ASR through structural blocking.}
\label{fig:asr-comparison}
\end{figure}
"""

    return latex


def generate_all_tables(results: dict, output_dir: str) -> None:
    """Generate all LaTeX tables and save to files."""

    output_path = Path(output_dir)
    output_path.mkdir(parents=True, exist_ok=True)

    # Main comparison table
    table1 = generate_main_comparison_table(results)
    with open(output_path / "table_comparison.tex", "w") as f:
        f.write(table1)
    print(f"  Generated: table_comparison.tex")

    # Defense breakdown
    table2 = generate_defense_breakdown_table(results)
    with open(output_path / "table_defense.tex", "w") as f:
        f.write(table2)
    print(f"  Generated: table_defense.tex")

    # Domain breakdown
    table3 = generate_domain_breakdown_table(results)
    with open(output_path / "table_domains.tex", "w") as f:
        f.write(table3)
    print(f"  Generated: table_domains.tex")

    # Attack categories
    table4 = generate_attack_category_table(results)
    with open(output_path / "table_attacks.tex", "w") as f:
        f.write(table4)
    print(f"  Generated: table_attacks.tex")

    # TikZ figure
    fig1 = generate_tikz_figure(results)
    with open(output_path / "figure_asr.tex", "w") as f:
        f.write(fig1)
    print(f"  Generated: figure_asr.tex")

    # Combined file with all tables
    with open(output_path / "all_tables.tex", "w") as f:
        f.write("% Auto-generated AgentDojo evaluation tables\n")
        f.write("% Generated by generate_paper_results.py\n\n")
        f.write(table1)
        f.write("\n")
        f.write(table2)
        f.write("\n")
        f.write(table3)
        f.write("\n")
        f.write(table4)
        f.write("\n")
        f.write(fig1)
    print(f"  Generated: all_tables.tex")


def print_summary(results: dict) -> None:
    """Print human-readable summary of results."""

    print("\n" + "=" * 60)
    print("EVALUATION SUMMARY")
    print("=" * 60)

    security = results.get("security", {})
    utility = results.get("utility", {})

    print("\nCore Metrics:")
    print(f"  Benign Utility (BU):        {utility.get('benign_utility', 0) * 100:.1f}%")
    print(f"  Utility under Attack (UA):  {security.get('utility_under_attack', 0) * 100:.1f}%")
    print(f"  Attack Success Rate (ASR):  {security.get('attack_success_rate', 0) * 100:.1f}%")

    defense = security.get("defense_breakdown", {})
    total = sum(defense.values()) if defense else 0
    if total > 0:
        print("\nDefense Breakdown:")
        print(f"  Structural blocks:  {defense.get('structural', 0)} ({defense.get('structural', 0)/total*100:.1f}%)")
        print(f"  Behavioral blocks:  {defense.get('behavioral', 0)} ({defense.get('behavioral', 0)/total*100:.1f}%)")
        print(f"  Not blocked:        {defense.get('not_blocked', 0)} ({defense.get('not_blocked', 0)/total*100:.1f}%)")

    print("\nComparison with Baselines:")
    our_asr = security.get('attack_success_rate', 0) * 100
    for key, baseline in BASELINES.items():
        improvement = baseline.asr - our_asr
        print(f"  vs {baseline.name}: ASR {our_asr:.1f}% vs {baseline.asr:.1f}% ({improvement:+.1f}%)")

    print("\n" + "=" * 60)


def main():
    parser = argparse.ArgumentParser(
        description="Generate LaTeX tables from AgentDojo evaluation results"
    )
    parser.add_argument(
        "results_dir",
        help="Directory containing evaluation results"
    )
    parser.add_argument(
        "--output",
        default=None,
        help="Output directory for LaTeX files (default: <results_dir>/latex)"
    )
    args = parser.parse_args()

    # Load results
    print(f"Loading results from: {args.results_dir}")
    results = load_results(args.results_dir)

    if not results:
        print("Error: No results found in directory")
        sys.exit(1)

    # Print summary
    print_summary(results)

    # Generate tables
    output_dir = args.output or os.path.join(args.results_dir, "latex")
    print(f"\nGenerating LaTeX tables in: {output_dir}")
    generate_all_tables(results, output_dir)

    print("\nDone!")


if __name__ == "__main__":
    main()
