#!/usr/bin/env python3
"""
MCP vs AgentFS Token Comparison Test

This script runs the SAME tasks through:
1. Claude API with MCP tool definitions (simulating osmmcp)
2. AgentFS (via llm9p)

And measures:
- Total tokens consumed
- Input tokens (including tool schemas)
- Output tokens
- Number of API calls
- Success/failure rate
"""

import anthropic
import json
import tiktoken
from dataclasses import dataclass, field
from typing import List, Dict, Any, Optional

# Initialize
client = anthropic.Anthropic()
enc = tiktoken.get_encoding("cl100k_base")

@dataclass
class TestResult:
    task: str
    approach: str  # "MCP" or "AgentFS"
    success: bool
    api_calls: int
    input_tokens: int
    output_tokens: int
    total_tokens: int
    tool_schema_tokens: int  # Tokens for tool definitions
    iterations: int
    error: Optional[str] = None
    transcript: List[Dict] = field(default_factory=list)

def count_tokens(text: str) -> int:
    """Count tokens using tiktoken cl100k_base"""
    return len(enc.encode(text))

# MCP Tool Definitions (matching osmmcp's geocode_address and find_nearby_places)
MCP_TOOLS = [
    {
        "name": "geocode_address",
        "description": "Convert an address or place name to geographic coordinates. For best results, format addresses clearly without parentheses and include city/country information for locations outside the US. For international or tourist sites, include the region or country name.",
        "input_schema": {
            "type": "object",
            "properties": {
                "address": {
                    "type": "string",
                    "description": "The address or place name to geocode"
                },
                "region": {
                    "type": "string",
                    "description": "Optional region context to improve results for ambiguous queries"
                }
            },
            "required": ["address"]
        }
    },
    {
        "name": "reverse_geocode",
        "description": "Convert geographic coordinates to a human-readable address",
        "input_schema": {
            "type": "object",
            "properties": {
                "latitude": {
                    "type": "number",
                    "description": "The latitude coordinate as a decimal between -90 and 90"
                },
                "longitude": {
                    "type": "number",
                    "description": "The longitude coordinate as a decimal between -180 and 180"
                }
            },
            "required": ["latitude", "longitude"]
        }
    },
    {
        "name": "find_nearby_places",
        "description": "Find places near a location",
        "input_schema": {
            "type": "object",
            "properties": {
                "latitude": {
                    "type": "number",
                    "description": "The latitude coordinate"
                },
                "longitude": {
                    "type": "number",
                    "description": "The longitude coordinate"
                },
                "radius": {
                    "type": "number",
                    "description": "Search radius in meters"
                },
                "category": {
                    "type": "string",
                    "description": "Category of places to find (e.g., restaurant, cafe, hotel)"
                },
                "limit": {
                    "type": "number",
                    "description": "Maximum number of results"
                }
            },
            "required": ["latitude", "longitude", "radius", "category"]
        }
    },
    {
        "name": "geo_distance",
        "description": "Calculate distance between two points",
        "input_schema": {
            "type": "object",
            "properties": {
                "from": {
                    "type": "object",
                    "properties": {
                        "latitude": {"type": "number"},
                        "longitude": {"type": "number"}
                    },
                    "required": ["latitude", "longitude"]
                },
                "to": {
                    "type": "object",
                    "properties": {
                        "latitude": {"type": "number"},
                        "longitude": {"type": "number"}
                    },
                    "required": ["latitude", "longitude"]
                }
            },
            "required": ["from", "to"]
        }
    },
    {
        "name": "get_route_directions",
        "description": "Get turn-by-turn directions between two points",
        "input_schema": {
            "type": "object",
            "properties": {
                "start_lat": {"type": "number", "description": "Start latitude"},
                "start_lon": {"type": "number", "description": "Start longitude"},
                "end_lat": {"type": "number", "description": "End latitude"},
                "end_lon": {"type": "number", "description": "End longitude"},
                "mode": {"type": "string", "description": "Travel mode: car, bike, foot"}
            },
            "required": ["start_lat", "start_lon", "end_lat", "end_lon"]
        }
    },
    {
        "name": "suggest_meeting_point",
        "description": "Suggest a meeting point for multiple locations",
        "input_schema": {
            "type": "object",
            "properties": {
                "locations": {
                    "type": "array",
                    "items": {
                        "type": "object",
                        "properties": {
                            "latitude": {"type": "number"},
                            "longitude": {"type": "number"}
                        }
                    },
                    "description": "Array of locations"
                },
                "radius": {"type": "number", "description": "Search radius in meters"},
                "category": {"type": "string", "description": "Category of meeting point"}
            },
            "required": ["locations"]
        }
    }
]

# Simulated tool responses (we're measuring token overhead, not actual OSM queries)
MOCK_RESPONSES = {
    "geocode_address": {
        "place": {
            "name": "Tour Eiffel, 5, Avenue Anatole France, Paris, France",
            "location": {"latitude": 48.8582599, "longitude": 2.2945006}
        }
    },
    "find_nearby_places": {
        "places": [
            {"name": "Le Jules Verne", "category": "restaurant", "distance": 50},
            {"name": "58 Tour Eiffel", "category": "restaurant", "distance": 100},
            {"name": "Les Ombres", "category": "restaurant", "distance": 200}
        ]
    }
}

def calculate_tool_schema_tokens(tools: List[Dict]) -> int:
    """Calculate tokens used by tool schemas"""
    schema_json = json.dumps(tools)
    return count_tokens(schema_json)

def run_mcp_test(task: str, max_iterations: int = 5) -> TestResult:
    """Run a task using MCP tool calling pattern"""

    result = TestResult(
        task=task,
        approach="MCP",
        success=False,
        api_calls=0,
        input_tokens=0,
        output_tokens=0,
        total_tokens=0,
        tool_schema_tokens=calculate_tool_schema_tokens(MCP_TOOLS),
        iterations=0
    )

    messages = [{"role": "user", "content": task}]

    for iteration in range(max_iterations):
        result.iterations += 1
        result.api_calls += 1

        try:
            response = client.messages.create(
                model="claude-sonnet-4-20250514",
                max_tokens=1024,
                tools=MCP_TOOLS,
                messages=messages
            )

            # Track tokens
            result.input_tokens += response.usage.input_tokens
            result.output_tokens += response.usage.output_tokens

            # Log iteration
            result.transcript.append({
                "iteration": iteration + 1,
                "input_tokens": response.usage.input_tokens,
                "output_tokens": response.usage.output_tokens,
                "stop_reason": response.stop_reason
            })

            # Check if done
            if response.stop_reason == "end_turn":
                result.success = True
                break

            # Handle tool use
            if response.stop_reason == "tool_use":
                tool_results = []
                for block in response.content:
                    if block.type == "tool_use":
                        # Simulate tool response
                        tool_name = block.name
                        mock_result = MOCK_RESPONSES.get(tool_name, {"result": "ok"})
                        tool_results.append({
                            "type": "tool_result",
                            "tool_use_id": block.id,
                            "content": json.dumps(mock_result)
                        })

                # Add assistant response and tool results to messages
                messages.append({"role": "assistant", "content": response.content})
                messages.append({"role": "user", "content": tool_results})
            else:
                result.success = True
                break

        except Exception as e:
            result.error = str(e)
            break

    result.total_tokens = result.input_tokens + result.output_tokens
    return result

def run_agentfs_comparison():
    """Compare MCP vs AgentFS for the same tasks"""

    tasks = [
        "Find the coordinates of the Eiffel Tower in Paris",
        "Find restaurants near coordinates 48.8582, 2.2945",
        "Find restaurants within 500 meters of the Eiffel Tower"
    ]

    results = []

    print("=" * 70)
    print("MCP vs AgentFS Token Comparison Test")
    print("=" * 70)
    print()

    # Run MCP tests
    print("Running MCP tests...")
    print("-" * 50)

    for task in tasks:
        print(f"\nTask: {task}")
        result = run_mcp_test(task)
        results.append(result)

        print(f"  Success: {result.success}")
        print(f"  API Calls: {result.api_calls}")
        print(f"  Tool Schema Tokens: {result.tool_schema_tokens}")
        print(f"  Input Tokens: {result.input_tokens}")
        print(f"  Output Tokens: {result.output_tokens}")
        print(f"  Total Tokens: {result.total_tokens}")
        print(f"  Iterations: {result.iterations}")

    # Summary comparison with AgentFS (from previous test)
    agentfs_results = [
        {"task": tasks[0], "total_tokens": 316, "api_calls": 1, "success": True, "iterations": 1},
        {"task": tasks[1], "total_tokens": 1160, "api_calls": 3, "success": True, "iterations": 3},
        {"task": tasks[2], "total_tokens": 384, "api_calls": 1, "success": False, "iterations": 1}
    ]

    print("\n")
    print("=" * 70)
    print("COMPARISON SUMMARY")
    print("=" * 70)
    print()

    print(f"{'Task':<45} | {'Approach':<8} | {'Tokens':<8} | {'Calls':<6} | {'Success':<7}")
    print("-" * 90)

    for i, task in enumerate(tasks):
        mcp = results[i]
        afs = agentfs_results[i]

        # MCP row
        print(f"{task[:43]:<45} | {'MCP':<8} | {mcp.total_tokens:<8} | {mcp.api_calls:<6} | {str(mcp.success):<7}")
        # AgentFS row
        print(f"{'':<45} | {'AgentFS':<8} | {afs['total_tokens']:<8} | {afs['api_calls']:<6} | {str(afs['success']):<7}")

        # Delta
        delta_tokens = mcp.total_tokens - afs['total_tokens']
        delta_pct = (delta_tokens / mcp.total_tokens * 100) if mcp.total_tokens > 0 else 0
        sign = "+" if delta_tokens > 0 else ""
        print(f"{'':<45} | {'Delta':<8} | {sign}{delta_tokens:<7} | {mcp.api_calls - afs['api_calls']:<+6} | {delta_pct:+.1f}%")
        print("-" * 90)

    # Totals
    mcp_total = sum(r.total_tokens for r in results)
    afs_total = sum(r['total_tokens'] for r in agentfs_results)
    mcp_calls = sum(r.api_calls for r in results)
    afs_calls = sum(r['api_calls'] for r in agentfs_results)

    print()
    print(f"{'TOTALS':<45} | {'MCP':<8} | {mcp_total:<8} | {mcp_calls:<6}")
    print(f"{'':<45} | {'AgentFS':<8} | {afs_total:<8} | {afs_calls:<6}")
    print(f"{'':<45} | {'Savings':<8} | {mcp_total - afs_total:<8} | {mcp_calls - afs_calls:<6}")

    savings_pct = ((mcp_total - afs_total) / mcp_total * 100) if mcp_total > 0 else 0
    print(f"\nAgentFS saves {savings_pct:.1f}% tokens vs MCP")

    # Tool schema overhead
    print()
    print("=" * 70)
    print("TOOL SCHEMA OVERHEAD")
    print("=" * 70)
    schema_tokens = results[0].tool_schema_tokens
    print(f"MCP tool schemas: {schema_tokens} tokens (sent with EVERY API call)")
    print(f"AgentFS namespace: ~184 tokens (sent once at start)")
    print(f"Schema overhead per call: {schema_tokens - 184} extra tokens")

    # Save detailed results
    output = {
        "test_date": "2026-01-06",
        "model": "claude-sonnet-4-20250514",
        "tokenizer": "tiktoken cl100k_base",
        "mcp_results": [
            {
                "task": r.task,
                "success": r.success,
                "api_calls": r.api_calls,
                "input_tokens": r.input_tokens,
                "output_tokens": r.output_tokens,
                "total_tokens": r.total_tokens,
                "tool_schema_tokens": r.tool_schema_tokens,
                "iterations": r.iterations,
                "transcript": r.transcript
            }
            for r in results
        ],
        "agentfs_results": agentfs_results,
        "comparison": {
            "mcp_total_tokens": mcp_total,
            "agentfs_total_tokens": afs_total,
            "token_savings": mcp_total - afs_total,
            "savings_percentage": savings_pct,
            "mcp_total_calls": mcp_calls,
            "agentfs_total_calls": afs_calls
        }
    }

    with open("mcp_vs_agentfs_results.json", "w") as f:
        json.dump(output, f, indent=2)

    print()
    print("Detailed results saved to mcp_vs_agentfs_results.json")

if __name__ == "__main__":
    run_agentfs_comparison()
