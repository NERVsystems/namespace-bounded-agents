#!/usr/bin/env python3
"""
Token Comparison: MCP vs AgentFS
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

# MCP Tool Schemas (from osmmcp registry - 14 tools)
MCP_TOOLS = [
    {
        "name": "geocode_address",
        "description": "Convert an address or place name to geographic coordinates",
        "inputSchema": {
            "type": "object",
            "properties": {
                "address": {
                    "type": "string",
                    "description": "The address or place name to geocode. For best results, format addresses clearly without parentheses and include city/country information for locations outside the US."
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
        "description": "Convert geographic coordinates to a street address",
        "inputSchema": {
            "type": "object",
            "properties": {
                "latitude": {"type": "number", "description": "The latitude coordinate"},
                "longitude": {"type": "number", "description": "The longitude coordinate"}
            },
            "required": ["latitude", "longitude"]
        }
    },
    {
        "name": "find_nearby_places",
        "description": "Find points of interest near a specific location",
        "inputSchema": {
            "type": "object",
            "properties": {
                "latitude": {"type": "number", "description": "The latitude coordinate of the center point"},
                "longitude": {"type": "number", "description": "The longitude coordinate of the center point"},
                "radius": {"type": "number", "description": "Search radius in meters (max 10000)", "default": 1000},
                "category": {"type": "string", "description": "Optional category filter (e.g., restaurant, hotel, park)"},
                "limit": {"type": "number", "description": "Maximum number of results to return", "default": 10}
            },
            "required": ["latitude", "longitude"]
        }
    },
    {
        "name": "geo_distance",
        "description": "Calculate distance between two points",
        "inputSchema": {
            "type": "object",
            "properties": {
                "from": {"type": "object", "description": "Starting point with latitude/longitude"},
                "to": {"type": "object", "description": "Ending point with latitude/longitude"}
            },
            "required": ["from", "to"]
        }
    },
    {
        "name": "route_fetch",
        "description": "Fetch a route between two points",
        "inputSchema": {
            "type": "object",
            "properties": {
                "start": {"type": "object", "description": "Starting point with latitude/longitude"},
                "end": {"type": "object", "description": "Ending point with latitude/longitude"},
                "mode": {"type": "string", "description": "Transport mode: car, bike, foot", "default": "car"}
            },
            "required": ["start", "end"]
        }
    },
    {
        "name": "suggest_meeting_point",
        "description": "Suggest a meeting point for multiple locations",
        "inputSchema": {
            "type": "object",
            "properties": {
                "locations": {"type": "array", "description": "Array of latitude/longitude objects"},
                "radius": {"type": "number", "description": "Search radius in meters"},
                "category": {"type": "string", "description": "Type of venue (cafe, restaurant, park)"}
            },
            "required": ["locations"]
        }
    },
    {
        "name": "explore_area",
        "description": "Explore an area and get key features",
        "inputSchema": {
            "type": "object",
            "properties": {
                "latitude": {"type": "number", "description": "Center latitude"},
                "longitude": {"type": "number", "description": "Center longitude"},
                "radius": {"type": "number", "description": "Search radius in meters"}
            },
            "required": ["latitude", "longitude"]
        }
    },
    {
        "name": "find_parking_facilities",
        "description": "Find parking facilities near a location",
        "inputSchema": {
            "type": "object",
            "properties": {
                "latitude": {"type": "number", "description": "Center latitude"},
                "longitude": {"type": "number", "description": "Center longitude"},
                "radius": {"type": "number", "description": "Search radius in meters"},
                "type": {"type": "string", "description": "Parking type filter"},
                "include_private": {"type": "boolean", "description": "Include private parking"},
                "limit": {"type": "number", "description": "Max results"}
            },
            "required": ["latitude", "longitude"]
        }
    },
    {
        "name": "find_charging_stations",
        "description": "Find EV charging stations near a location",
        "inputSchema": {
            "type": "object",
            "properties": {
                "latitude": {"type": "number", "description": "Center latitude"},
                "longitude": {"type": "number", "description": "Center longitude"},
                "radius": {"type": "number", "description": "Search radius in meters"},
                "limit": {"type": "number", "description": "Max results"}
            },
            "required": ["latitude", "longitude"]
        }
    },
    {
        "name": "find_schools_nearby",
        "description": "Find schools near a location",
        "inputSchema": {
            "type": "object",
            "properties": {
                "latitude": {"type": "number", "description": "Center latitude"},
                "longitude": {"type": "number", "description": "Center longitude"},
                "radius": {"type": "number", "description": "Search radius in meters"},
                "limit": {"type": "number", "description": "Max results"}
            },
            "required": ["latitude", "longitude"]
        }
    },
    {
        "name": "centroid_points",
        "description": "Calculate the centroid of multiple points",
        "inputSchema": {
            "type": "object",
            "properties": {
                "points": {"type": "array", "description": "Array of latitude/longitude objects"}
            },
            "required": ["points"]
        }
    },
    {
        "name": "bbox_from_points",
        "description": "Create a bounding box from multiple points",
        "inputSchema": {
            "type": "object",
            "properties": {
                "points": {"type": "array", "description": "Array of latitude/longitude objects"}
            },
            "required": ["points"]
        }
    },
    {
        "name": "polyline_decode",
        "description": "Decode a polyline string into coordinates",
        "inputSchema": {
            "type": "object",
            "properties": {
                "polyline": {"type": "string", "description": "Encoded polyline string"}
            },
            "required": ["polyline"]
        }
    },
    {
        "name": "polyline_encode",
        "description": "Encode coordinates into a polyline string",
        "inputSchema": {
            "type": "object",
            "properties": {
                "points": {"type": "array", "description": "Array of latitude/longitude objects"}
            },
            "required": ["points"]
        }
    }
]

# AgentFS v0 Namespace (from actual Inferno `ls -R /n/osm` output)
AGENTFS_NAMESPACE = """/n/osm:
bbox/
centroid/
charging/
distance/
explore/
geocode/
meeting_point/
nearby/
parking/
polyline_decode/
polyline_encode/
reverse/
route/
schools/

/n/osm/geocode:
_clear
_example
_ttl
_types
error
poll
query

/n/osm/nearby:
_clear
_example
_ttl
_types
category
error
lat
lon
poll
radius
result

/n/osm/distance:
_clear
_ttl
_types
error
lat1
lat2
lon1
lon2
poll
result

/n/osm/route:
_clear
_ttl
_types
end_lat
end_lon
error
mode
poll
result
start_lat
start_lon

/n/osm/meeting_point:
_clear
_ttl
_types
category
error
lat1
lat2
lon1
lon2
poll
result"""

# Bare namespace (no metadata files - just functional files)
BARE_NAMESPACE = """/n/osm:
bbox/
centroid/
charging/
distance/
explore/
geocode/
meeting_point/
nearby/
parking/
polyline_decode/
polyline_encode/
reverse/
route/
schools/

/n/osm/geocode:
query

/n/osm/nearby:
category
lat
lon
radius
result

/n/osm/distance:
lat1
lat2
lon1
lon2
result

/n/osm/route:
end_lat
end_lon
mode
result
start_lat
start_lon

/n/osm/meeting_point:
category
lat1
lat2
lon1
lon2
result"""

def main():
    # Calculate token counts using tiktoken
    mcp_json = json.dumps(MCP_TOOLS, indent=2)
    mcp_tokens = count_tokens(mcp_json)

    agentfs_tokens = count_tokens(AGENTFS_NAMESPACE)
    bare_tokens = count_tokens(BARE_NAMESPACE)

    print("=" * 70)
    print("TOKEN COMPARISON: MCP vs AgentFS")
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
    print(f"{'AgentFS v0 (with metadata)':<30} {agentfs_tokens:>10,} {len(AGENTFS_NAMESPACE):>10,}")
    print(f"{'Bare namespace':<30} {bare_tokens:>10,} {len(BARE_NAMESPACE):>10,}")
    print("-" * 50)
    print()

    reduction_agentfs = ((mcp_tokens - agentfs_tokens) / mcp_tokens * 100)
    reduction_bare = ((mcp_tokens - bare_tokens) / mcp_tokens * 100)

    print("TOKEN REDUCTION vs MCP:")
    print(f"  AgentFS v0:    {reduction_agentfs:.1f}% reduction ({mcp_tokens - agentfs_tokens:,} tokens saved)")
    print(f"  Bare:          {reduction_bare:.1f}% reduction ({mcp_tokens - bare_tokens:,} tokens saved)")
    print()

    # Context window impact
    CONTEXT_128K = 128_000
    CONTEXT_200K = 200_000

    print("CONTEXT WINDOW IMPACT:")
    print(f"  128K context (GPT-4):")
    print(f"    MCP:      {mcp_tokens / CONTEXT_128K * 100:.3f}%")
    print(f"    AgentFS:  {agentfs_tokens / CONTEXT_128K * 100:.3f}%")
    print(f"    Bare:     {bare_tokens / CONTEXT_128K * 100:.3f}%")
    print()
    print(f"  200K context (Claude):")
    print(f"    MCP:      {mcp_tokens / CONTEXT_200K * 100:.3f}%")
    print(f"    AgentFS:  {agentfs_tokens / CONTEXT_200K * 100:.3f}%")
    print(f"    Bare:     {bare_tokens / CONTEXT_200K * 100:.3f}%")
    print()

    # Scaling projection
    print("SCALING PROJECTION (tools → tokens):")
    mcp_per_tool = mcp_tokens / len(MCP_TOOLS)
    agentfs_per_tool = agentfs_tokens / len(MCP_TOOLS)
    bare_per_tool = bare_tokens / len(MCP_TOOLS)
    print(f"  Per-tool average:")
    print(f"    MCP:      {mcp_per_tool:.1f} tokens/tool")
    print(f"    AgentFS:  {agentfs_per_tool:.1f} tokens/tool")
    print(f"    Bare:     {bare_per_tool:.1f} tokens/tool")
    print()

    # Project to 50 tools
    print(f"  Projected at 50 tools:")
    print(f"    MCP:      {50 * mcp_per_tool:,.0f} tokens")
    print(f"    AgentFS:  {50 * agentfs_per_tool:,.0f} tokens")
    print(f"    Savings:  {50 * (mcp_per_tool - agentfs_per_tool):,.0f} tokens")
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
