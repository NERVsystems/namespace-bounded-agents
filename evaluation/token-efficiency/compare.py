#!/usr/bin/env python3
"""
Token Comparison: MCP vs AgentFS

Compares token consumption for tool discovery across:
1. MCP (JSON schemas with descriptions)
2. AgentFS v0 (namespace with metadata files)
3. Bare namespace (just file paths)
"""

import json

# Approximate token counting (1 token ≈ 4 chars for English text)
def count_tokens(text):
    # Rough approximation - actual tokenizers vary
    # GPT-4/Claude typically: 1 token ≈ 4 characters
    return len(text) // 4

# MCP Tool Schemas (from osmmcp registry)
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

# AgentFS v0 Namespace (from actual server output)
AGENTFS_NAMESPACE = """
/n/osm:
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
result
"""

# Bare namespace (no metadata files)
BARE_NAMESPACE = """
/n/osm:
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
result
"""

def main():
    # Calculate MCP token count
    mcp_json = json.dumps(MCP_TOOLS, indent=2)
    mcp_tokens = count_tokens(mcp_json)

    # Calculate AgentFS token count
    agentfs_tokens = count_tokens(AGENTFS_NAMESPACE)

    # Calculate bare namespace token count
    bare_tokens = count_tokens(BARE_NAMESPACE)

    print("=" * 60)
    print("TOKEN COMPARISON: MCP vs AgentFS")
    print("=" * 60)
    print()
    print(f"Tools compared: {len(MCP_TOOLS)}")
    print()
    print("RESULTS:")
    print("-" * 40)
    print(f"MCP (JSON schemas):      {mcp_tokens:,} tokens")
    print(f"AgentFS v0 (with meta):  {agentfs_tokens:,} tokens")
    print(f"Bare namespace:          {bare_tokens:,} tokens")
    print("-" * 40)
    print()
    print("REDUCTION vs MCP:")
    print(f"  AgentFS v0: {((mcp_tokens - agentfs_tokens) / mcp_tokens * 100):.1f}% reduction")
    print(f"  Bare:       {((mcp_tokens - bare_tokens) / mcp_tokens * 100):.1f}% reduction")
    print()
    print("CHARACTERS:")
    print(f"  MCP:        {len(mcp_json):,} chars")
    print(f"  AgentFS:    {len(AGENTFS_NAMESPACE):,} chars")
    print(f"  Bare:       {len(BARE_NAMESPACE):,} chars")
    print()

    # Show MCP sample
    print("=" * 60)
    print("SAMPLE MCP SCHEMA (geocode_address):")
    print("-" * 60)
    print(json.dumps(MCP_TOOLS[0], indent=2))
    print()

    # Show AgentFS sample
    print("=" * 60)
    print("SAMPLE AgentFS NAMESPACE (geocode):")
    print("-" * 60)
    print("""/n/osm/geocode:
  _clear   (w)  - clear state
  _example (r)  - usage example
  _ttl     (r)  - cache TTL
  _types   (r)  - "query:string"
  error    (r)  - last error
  poll     (r)  - fresh fetch with provenance
  query    (rw) - write address, read coordinates""")
    print()

    # Context window impact
    print("=" * 60)
    print("CONTEXT WINDOW IMPACT (128K tokens):")
    print("-" * 60)
    print(f"  MCP:      {mcp_tokens / 128000 * 100:.2f}% of context")
    print(f"  AgentFS:  {agentfs_tokens / 128000 * 100:.2f}% of context")
    print(f"  Bare:     {bare_tokens / 128000 * 100:.2f}% of context")
    print()

if __name__ == "__main__":
    main()
