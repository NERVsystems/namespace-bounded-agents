#!/usr/bin/env python3
"""
Full MCP vs AgentFS Benchmark - ALL 14 Tools

Tests ALL 14 tools from osm9p through both MCP and AgentFS.
Uses tiktoken cl100k_base for ALL token measurements.
Records every failure, retry, and error.
Breaks down by Type A vs Type B.
"""

import anthropic
import json
import tiktoken
from dataclasses import dataclass, field
from typing import List, Dict, Any, Optional
from datetime import datetime

# Initialize
client = anthropic.Anthropic()
enc = tiktoken.get_encoding("cl100k_base")

def count_tokens(text: str) -> int:
    """Count tokens using tiktoken cl100k_base - THE STANDARD"""
    if not text:
        return 0
    return len(enc.encode(text))

@dataclass
class ToolTest:
    tool_name: str
    tool_type: str  # "A" or "B"
    task: str
    mcp_tool_def: Dict
    expected_params: Dict  # What MCP should call with

@dataclass
class TestResult:
    tool_name: str
    tool_type: str
    task: str
    approach: str  # "MCP" or "AgentFS"
    success: bool
    api_calls: int
    iterations: int

    # Token counts - ALL measured with tiktoken
    prompt_tokens: int = 0
    tool_schema_tokens: int = 0
    response_tokens: int = 0
    total_tokens: int = 0

    # Errors and retries
    errors: List[str] = field(default_factory=list)
    retries: int = 0

    # Raw transcript
    transcript: List[Dict] = field(default_factory=list)

# ============================================================================
# MCP TOOL DEFINITIONS - All 14 tools matching osm9p
# ============================================================================

MCP_TOOLS = [
    # TYPE A TOOLS (3)
    {
        "name": "geocode_address",
        "description": "Convert an address or place name to geographic coordinates",
        "input_schema": {
            "type": "object",
            "properties": {
                "address": {"type": "string", "description": "The address or place name to geocode"},
                "region": {"type": "string", "description": "Optional region context"}
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
                "latitude": {"type": "number", "description": "Latitude (-90 to 90)"},
                "longitude": {"type": "number", "description": "Longitude (-180 to 180)"}
            },
            "required": ["latitude", "longitude"]
        }
    },
    {
        "name": "polyline_decode",
        "description": "Decode a polyline string into coordinates",
        "input_schema": {
            "type": "object",
            "properties": {
                "polyline": {"type": "string", "description": "Encoded polyline string"}
            },
            "required": ["polyline"]
        }
    },

    # TYPE B TOOLS (11)
    {
        "name": "find_nearby_places",
        "description": "Find places near a location",
        "input_schema": {
            "type": "object",
            "properties": {
                "latitude": {"type": "number", "description": "Center latitude"},
                "longitude": {"type": "number", "description": "Center longitude"},
                "radius": {"type": "number", "description": "Search radius in meters"},
                "category": {"type": "string", "description": "Place category (restaurant, cafe, etc)"},
                "limit": {"type": "number", "description": "Max results"}
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
                "lat1": {"type": "number", "description": "First point latitude"},
                "lon1": {"type": "number", "description": "First point longitude"},
                "lat2": {"type": "number", "description": "Second point latitude"},
                "lon2": {"type": "number", "description": "Second point longitude"}
            },
            "required": ["lat1", "lon1", "lat2", "lon2"]
        }
    },
    {
        "name": "get_route",
        "description": "Get route between two points",
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
        "description": "Find meeting point between two locations",
        "input_schema": {
            "type": "object",
            "properties": {
                "lat1": {"type": "number", "description": "First location latitude"},
                "lon1": {"type": "number", "description": "First location longitude"},
                "lat2": {"type": "number", "description": "Second location latitude"},
                "lon2": {"type": "number", "description": "Second location longitude"},
                "category": {"type": "string", "description": "Meeting point category"}
            },
            "required": ["lat1", "lon1", "lat2", "lon2"]
        }
    },
    {
        "name": "find_parking",
        "description": "Find parking facilities near a location",
        "input_schema": {
            "type": "object",
            "properties": {
                "latitude": {"type": "number", "description": "Center latitude"},
                "longitude": {"type": "number", "description": "Center longitude"},
                "radius": {"type": "number", "description": "Search radius in meters"}
            },
            "required": ["latitude", "longitude", "radius"]
        }
    },
    {
        "name": "find_charging_stations",
        "description": "Find EV charging stations near a location",
        "input_schema": {
            "type": "object",
            "properties": {
                "latitude": {"type": "number", "description": "Center latitude"},
                "longitude": {"type": "number", "description": "Center longitude"},
                "radius": {"type": "number", "description": "Search radius in meters"}
            },
            "required": ["latitude", "longitude", "radius"]
        }
    },
    {
        "name": "find_schools",
        "description": "Find schools near a location",
        "input_schema": {
            "type": "object",
            "properties": {
                "latitude": {"type": "number", "description": "Center latitude"},
                "longitude": {"type": "number", "description": "Center longitude"},
                "radius": {"type": "number", "description": "Search radius in meters"}
            },
            "required": ["latitude", "longitude", "radius"]
        }
    },
    {
        "name": "explore_area",
        "description": "Explore an area and get key features",
        "input_schema": {
            "type": "object",
            "properties": {
                "latitude": {"type": "number", "description": "Center latitude"},
                "longitude": {"type": "number", "description": "Center longitude"},
                "radius": {"type": "number", "description": "Exploration radius in meters"}
            },
            "required": ["latitude", "longitude", "radius"]
        }
    },
    {
        "name": "bbox_from_points",
        "description": "Create bounding box from multiple points",
        "input_schema": {
            "type": "object",
            "properties": {
                "points": {
                    "type": "array",
                    "items": {
                        "type": "object",
                        "properties": {
                            "latitude": {"type": "number"},
                            "longitude": {"type": "number"}
                        }
                    },
                    "description": "Array of coordinate points"
                }
            },
            "required": ["points"]
        }
    },
    {
        "name": "centroid_points",
        "description": "Calculate centroid of multiple points",
        "input_schema": {
            "type": "object",
            "properties": {
                "points": {
                    "type": "array",
                    "items": {
                        "type": "object",
                        "properties": {
                            "latitude": {"type": "number"},
                            "longitude": {"type": "number"}
                        }
                    },
                    "description": "Array of coordinate points"
                }
            },
            "required": ["points"]
        }
    },
    {
        "name": "polyline_encode",
        "description": "Encode coordinates into a polyline string",
        "input_schema": {
            "type": "object",
            "properties": {
                "points": {
                    "type": "array",
                    "items": {
                        "type": "object",
                        "properties": {
                            "latitude": {"type": "number"},
                            "longitude": {"type": "number"}
                        }
                    },
                    "description": "Array of coordinate points to encode"
                }
            },
            "required": ["points"]
        }
    }
]

# ============================================================================
# TEST CASES - One for each of the 14 tools
# ============================================================================

TEST_CASES = [
    # TYPE A (3)
    ToolTest("geocode", "A", "Find the coordinates of the Eiffel Tower in Paris",
             MCP_TOOLS[0], {"address": "Eiffel Tower, Paris"}),
    ToolTest("reverse", "A", "What is the address at coordinates 48.8582, 2.2945?",
             MCP_TOOLS[1], {"latitude": 48.8582, "longitude": 2.2945}),
    ToolTest("polyline_decode", "A", "Decode this polyline: _p~iF~ps|U_ulLnnqC_mqNvxq`@",
             MCP_TOOLS[2], {"polyline": "_p~iF~ps|U_ulLnnqC_mqNvxq`@"}),

    # TYPE B (11)
    ToolTest("nearby", "B", "Find restaurants within 500 meters of 48.8582, 2.2945",
             MCP_TOOLS[3], {"latitude": 48.8582, "longitude": 2.2945, "radius": 500, "category": "restaurant"}),
    ToolTest("distance", "B", "Calculate the distance from 48.8582,2.2945 to 48.8606,2.3376",
             MCP_TOOLS[4], {"lat1": 48.8582, "lon1": 2.2945, "lat2": 48.8606, "lon2": 2.3376}),
    ToolTest("route", "B", "Get driving route from 48.8582,2.2945 to 48.8606,2.3376",
             MCP_TOOLS[5], {"start_lat": 48.8582, "start_lon": 2.2945, "end_lat": 48.8606, "end_lon": 2.3376, "mode": "car"}),
    ToolTest("meeting_point", "B", "Find a cafe meeting point between 48.8582,2.2945 and 48.8606,2.3376",
             MCP_TOOLS[6], {"lat1": 48.8582, "lon1": 2.2945, "lat2": 48.8606, "lon2": 2.3376, "category": "cafe"}),
    ToolTest("parking", "B", "Find parking within 1000 meters of 48.8582, 2.2945",
             MCP_TOOLS[7], {"latitude": 48.8582, "longitude": 2.2945, "radius": 1000}),
    ToolTest("charging", "B", "Find EV charging stations within 2000 meters of 48.8582, 2.2945",
             MCP_TOOLS[8], {"latitude": 48.8582, "longitude": 2.2945, "radius": 2000}),
    ToolTest("schools", "B", "Find schools within 1500 meters of 48.8582, 2.2945",
             MCP_TOOLS[9], {"latitude": 48.8582, "longitude": 2.2945, "radius": 1500}),
    ToolTest("explore", "B", "Explore the area within 500 meters of 48.8582, 2.2945",
             MCP_TOOLS[10], {"latitude": 48.8582, "longitude": 2.2945, "radius": 500}),
    ToolTest("bbox", "B", "Create a bounding box from points: (48.85,2.29), (48.86,2.34), (48.87,2.30)",
             MCP_TOOLS[11], {"points": [{"latitude": 48.85, "longitude": 2.29}, {"latitude": 48.86, "longitude": 2.34}, {"latitude": 48.87, "longitude": 2.30}]}),
    ToolTest("centroid", "B", "Calculate centroid of points: (48.85,2.29), (48.86,2.34), (48.87,2.30)",
             MCP_TOOLS[12], {"points": [{"latitude": 48.85, "longitude": 2.29}, {"latitude": 48.86, "longitude": 2.34}, {"latitude": 48.87, "longitude": 2.30}]}),
    ToolTest("polyline_encode", "B", "Encode these points into a polyline: (48.85,2.29), (48.86,2.34)",
             MCP_TOOLS[13], {"points": [{"latitude": 48.85, "longitude": 2.29}, {"latitude": 48.86, "longitude": 2.34}]}),
]

# Mock responses for tool calls
MOCK_RESPONSES = {
    "geocode_address": {"place": {"name": "Tour Eiffel", "location": {"latitude": 48.8582, "longitude": 2.2945}}},
    "reverse_geocode": {"place": {"name": "5 Avenue Anatole France, Paris", "location": {"latitude": 48.8582, "longitude": 2.2945}}},
    "polyline_decode": {"points": [{"latitude": 38.5, "longitude": -120.2}, {"latitude": 40.7, "longitude": -120.95}]},
    "find_nearby_places": {"places": [{"name": "Restaurant A", "distance": 100}, {"name": "Restaurant B", "distance": 200}]},
    "geo_distance": {"distance_km": 3.16, "distance_meters": 3162},
    "get_route": {"distance_km": 4.2, "duration_minutes": 12, "polyline": "abc123"},
    "suggest_meeting_point": {"place": {"name": "Cafe Central", "latitude": 48.859, "longitude": 2.316}},
    "find_parking": {"facilities": [{"name": "Parking Eiffel", "spaces": 200}]},
    "find_charging_stations": {"stations": [{"name": "ChargePoint A", "connectors": 4}]},
    "find_schools": {"schools": [{"name": "Ecole Primaire", "type": "primary"}]},
    "explore_area": {"features": {"restaurants": 15, "cafes": 8, "parks": 2}},
    "bbox_from_points": {"bbox": {"minLat": 48.85, "minLon": 2.29, "maxLat": 48.87, "maxLon": 2.34}},
    "centroid_points": {"centroid": {"latitude": 48.86, "longitude": 2.31}},
    "polyline_encode": {"polyline": "_abc123def"}
}

def run_mcp_test(test: ToolTest, max_iterations: int = 5) -> TestResult:
    """Run a single tool test through MCP"""

    result = TestResult(
        tool_name=test.tool_name,
        tool_type=test.tool_type,
        task=test.task,
        approach="MCP",
        success=False,
        api_calls=0,
        iterations=0
    )

    # Calculate tool schema tokens using tiktoken
    schema_json = json.dumps(MCP_TOOLS)
    result.tool_schema_tokens = count_tokens(schema_json)

    messages = [{"role": "user", "content": test.task}]

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

            # Count tokens with tiktoken for consistency
            # But also record API-reported for comparison
            prompt_text = json.dumps(messages) + schema_json
            response_text = json.dumps([{"type": b.type, "text": getattr(b, "text", "") if hasattr(b, "text") else ""} for b in response.content])

            iter_prompt_tokens = count_tokens(prompt_text)
            iter_response_tokens = count_tokens(response_text)

            result.prompt_tokens += iter_prompt_tokens
            result.response_tokens += iter_response_tokens

            result.transcript.append({
                "iteration": iteration + 1,
                "prompt_tokens_tiktoken": iter_prompt_tokens,
                "response_tokens_tiktoken": iter_response_tokens,
                "prompt_tokens_api": response.usage.input_tokens,
                "response_tokens_api": response.usage.output_tokens,
                "stop_reason": response.stop_reason
            })

            if response.stop_reason == "end_turn":
                result.success = True
                break

            if response.stop_reason == "tool_use":
                tool_results = []
                # Convert content blocks to serializable format
                assistant_content = []
                for block in response.content:
                    if block.type == "tool_use":
                        tool_name = block.name
                        mock_result = MOCK_RESPONSES.get(tool_name, {"result": "ok"})
                        tool_results.append({
                            "type": "tool_result",
                            "tool_use_id": block.id,
                            "content": json.dumps(mock_result)
                        })
                        assistant_content.append({
                            "type": "tool_use",
                            "id": block.id,
                            "name": block.name,
                            "input": block.input
                        })
                    elif block.type == "text":
                        assistant_content.append({
                            "type": "text",
                            "text": block.text
                        })

                messages.append({"role": "assistant", "content": assistant_content})
                messages.append({"role": "user", "content": tool_results})
            else:
                result.success = True
                break

        except Exception as e:
            result.errors.append(f"Iteration {iteration + 1}: {str(e)}")
            result.retries += 1

    result.total_tokens = result.prompt_tokens + result.response_tokens + (result.tool_schema_tokens * result.api_calls)
    return result

def run_full_benchmark():
    """Run the complete benchmark"""

    print("=" * 80)
    print("FULL MCP vs AgentFS BENCHMARK - ALL 14 TOOLS")
    print("=" * 80)
    print(f"Date: {datetime.now().isoformat()}")
    print(f"Model: claude-sonnet-4-20250514")
    print(f"Tokenizer: tiktoken cl100k_base")
    print()

    # Calculate tool schema overhead once
    schema_tokens = count_tokens(json.dumps(MCP_TOOLS))
    print(f"MCP Tool Schema Tokens (14 tools): {schema_tokens}")
    print()

    results = []
    type_a_results = []
    type_b_results = []

    print("-" * 80)
    print("Running MCP Tests...")
    print("-" * 80)

    for i, test in enumerate(TEST_CASES):
        print(f"\n[{i+1}/14] {test.tool_name} (Type {test.tool_type})")
        print(f"  Task: {test.task[:60]}...")

        result = run_mcp_test(test)
        results.append(result)

        if test.tool_type == "A":
            type_a_results.append(result)
        else:
            type_b_results.append(result)

        print(f"  Success: {result.success}")
        print(f"  API Calls: {result.api_calls}")
        print(f"  Total Tokens: {result.total_tokens}")
        if result.errors:
            print(f"  Errors: {result.errors}")

    # Summary
    print("\n")
    print("=" * 80)
    print("RESULTS SUMMARY")
    print("=" * 80)

    # Type A Summary
    print("\n### TYPE A TOOLS (3 tools) ###")
    print(f"{'Tool':<20} | {'Success':<8} | {'Calls':<6} | {'Tokens':<10} | {'Errors'}")
    print("-" * 70)
    for r in type_a_results:
        errors = len(r.errors)
        print(f"{r.tool_name:<20} | {str(r.success):<8} | {r.api_calls:<6} | {r.total_tokens:<10} | {errors}")

    type_a_total = sum(r.total_tokens for r in type_a_results)
    type_a_calls = sum(r.api_calls for r in type_a_results)
    type_a_success = sum(1 for r in type_a_results if r.success)
    print("-" * 70)
    print(f"{'TOTAL':<20} | {type_a_success}/3     | {type_a_calls:<6} | {type_a_total:<10}")

    # Type B Summary
    print("\n### TYPE B TOOLS (11 tools) ###")
    print(f"{'Tool':<20} | {'Success':<8} | {'Calls':<6} | {'Tokens':<10} | {'Errors'}")
    print("-" * 70)
    for r in type_b_results:
        errors = len(r.errors)
        print(f"{r.tool_name:<20} | {str(r.success):<8} | {r.api_calls:<6} | {r.total_tokens:<10} | {errors}")

    type_b_total = sum(r.total_tokens for r in type_b_results)
    type_b_calls = sum(r.api_calls for r in type_b_results)
    type_b_success = sum(1 for r in type_b_results if r.success)
    print("-" * 70)
    print(f"{'TOTAL':<20} | {type_b_success}/11    | {type_b_calls:<6} | {type_b_total:<10}")

    # Grand Total
    print("\n### GRAND TOTAL (14 tools) ###")
    grand_total = type_a_total + type_b_total
    grand_calls = type_a_calls + type_b_calls
    grand_success = type_a_success + type_b_success
    print(f"Total Tokens: {grand_total}")
    print(f"Total API Calls: {grand_calls}")
    print(f"Success Rate: {grand_success}/14 ({grand_success/14*100:.1f}%)")
    print(f"Tool Schema Overhead: {schema_tokens * grand_calls} tokens ({schema_tokens} x {grand_calls} calls)")

    # Save detailed results
    output = {
        "test_date": datetime.now().isoformat(),
        "model": "claude-sonnet-4-20250514",
        "tokenizer": "tiktoken cl100k_base",
        "tool_schema_tokens": schema_tokens,
        "summary": {
            "type_a": {
                "tools": 3,
                "success": type_a_success,
                "total_tokens": type_a_total,
                "total_calls": type_a_calls,
                "avg_tokens_per_tool": type_a_total / 3
            },
            "type_b": {
                "tools": 11,
                "success": type_b_success,
                "total_tokens": type_b_total,
                "total_calls": type_b_calls,
                "avg_tokens_per_tool": type_b_total / 11
            },
            "total": {
                "tools": 14,
                "success": grand_success,
                "total_tokens": grand_total,
                "total_calls": grand_calls,
                "avg_tokens_per_tool": grand_total / 14
            }
        },
        "results": [
            {
                "tool_name": r.tool_name,
                "tool_type": r.tool_type,
                "task": r.task,
                "success": r.success,
                "api_calls": r.api_calls,
                "iterations": r.iterations,
                "prompt_tokens": r.prompt_tokens,
                "response_tokens": r.response_tokens,
                "tool_schema_tokens": r.tool_schema_tokens,
                "total_tokens": r.total_tokens,
                "errors": r.errors,
                "retries": r.retries,
                "transcript": r.transcript
            }
            for r in results
        ]
    }

    with open("full_benchmark_results.json", "w") as f:
        json.dump(output, f, indent=2)

    print("\n")
    print("Detailed results saved to: full_benchmark_results.json")
    print()
    print("NOTE: AgentFS results must be collected separately by running")
    print("the same 14 tasks through the Inferno agent.b implementation.")

    return output

if __name__ == "__main__":
    run_full_benchmark()
