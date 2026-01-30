#!/usr/bin/env python3
"""
Token Comparison: MCP vs 9P Filesystem

Using OpenAI's tiktoken (cl100k_base) for accurate token counting.

Citation:
  OpenAI. tiktoken: A fast BPE tokenizer for use with OpenAI's models.
  https://github.com/openai/tiktoken
  Encoding: cl100k_base (GPT-4, GPT-3.5-turbo)

This provides a citable, reproducible token count for academic purposes.
"""

import tiktoken
import json

# Use cl100k_base - the encoding for GPT-4 and GPT-3.5-turbo
# This is the industry standard for LLM token counting
ENCODING = "cl100k_base"

def count_tokens(text: str) -> int:
    """Count tokens using tiktoken cl100k_base encoding."""
    enc = tiktoken.get_encoding(ENCODING)
    return len(enc.encode(text))

# MCP Tool Schemas - 14 tools matching full_benchmark.py
# These are the exact definitions used in the benchmark
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

# 9P Namespace listing - 14 tools matching osm9p server
# This is the complete namespace sent to the LLM
NAMESPACE_14_TOOLS = """/n/osm:
geocode/
reverse/
polyline_decode/
nearby/
distance/
route/
meeting_point/
parking/
charging/
schools/
explore/
bbox/
centroid/
polyline_encode/

/n/osm/geocode:
query
region

/n/osm/reverse:
lat
lon
result

/n/osm/polyline_decode:
polyline
result

/n/osm/nearby:
lat
lon
radius
category
limit
result

/n/osm/distance:
lat1
lon1
lat2
lon2
result

/n/osm/route:
start_lat
start_lon
end_lat
end_lon
mode
result

/n/osm/meeting_point:
lat1
lon1
lat2
lon2
category
result

/n/osm/parking:
lat
lon
radius
result

/n/osm/charging:
lat
lon
radius
result

/n/osm/schools:
lat
lon
radius
result

/n/osm/explore:
lat
lon
radius
result

/n/osm/bbox:
points
result

/n/osm/centroid:
points
result

/n/osm/polyline_encode:
points
result"""

def main():
    # Calculate token counts using tiktoken
    mcp_json = json.dumps(MCP_TOOLS)  # No indent - matches actual API usage
    mcp_tokens = count_tokens(mcp_json)
    namespace_tokens = count_tokens(NAMESPACE_14_TOOLS)

    print("=" * 70)
    print("TOKEN COMPARISON: MCP vs 9P Filesystem (14 tools)")
    print("Tokenizer: tiktoken cl100k_base (GPT-4/GPT-3.5-turbo)")
    print("=" * 70)
    print()
    print(f"Tools compared: {len(MCP_TOOLS)}")
    print()
    print("RESULTS:")
    print("-" * 50)
    print(f"{'Method':<30} {'Tokens':>10} {'Chars':>10}")
    print("-" * 50)
    print(f"{'MCP (JSON schemas)':<30} {mcp_tokens:>10,} {len(mcp_json):>10,}")
    print(f"{'9P Namespace':<30} {namespace_tokens:>10,} {len(NAMESPACE_14_TOOLS):>10,}")
    print("-" * 50)
    print()

    reduction = ((mcp_tokens - namespace_tokens) / mcp_tokens * 100)

    print("TOKEN REDUCTION:")
    print(f"  9P vs MCP: {reduction:.1f}% reduction ({mcp_tokens - namespace_tokens:,} tokens saved)")
    print()

    # Context window impact
    CONTEXT_128K = 128_000
    CONTEXT_200K = 200_000

    print("CONTEXT WINDOW IMPACT:")
    print(f"  128K context (GPT-4):")
    print(f"    MCP:      {mcp_tokens / CONTEXT_128K * 100:.3f}%")
    print(f"    9P:       {namespace_tokens / CONTEXT_128K * 100:.3f}%")
    print()
    print(f"  200K context (Claude):")
    print(f"    MCP:      {mcp_tokens / CONTEXT_200K * 100:.3f}%")
    print(f"    9P:       {namespace_tokens / CONTEXT_200K * 100:.3f}%")
    print()

    # Per-tool breakdown
    print("PER-TOOL AVERAGE:")
    mcp_per_tool = mcp_tokens / len(MCP_TOOLS)
    ns_per_tool = namespace_tokens / len(MCP_TOOLS)
    print(f"  MCP:  {mcp_per_tool:.1f} tokens/tool")
    print(f"  9P:   {ns_per_tool:.1f} tokens/tool")
    print()

    # Scaling projection
    print("SCALING PROJECTION:")
    for n in [25, 50, 100]:
        print(f"  {n} tools:")
        print(f"    MCP:      {n * mcp_per_tool:,.0f} tokens")
        print(f"    9P:       {n * ns_per_tool:,.0f} tokens")
        print(f"    Savings:  {n * (mcp_per_tool - ns_per_tool):,.0f} tokens")
    print()

    # Citation
    print("=" * 70)
    print("CITATION:")
    print("-" * 70)
    print("OpenAI. tiktoken: A fast BPE tokenizer for use with OpenAI's models.")
    print("GitHub repository: https://github.com/openai/tiktoken")
    print("Encoding used: cl100k_base")
    print("=" * 70)

if __name__ == "__main__":
    main()
