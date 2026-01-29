# Multi-Format Query Shim Results

## Summary

The universal query shim accepts three input formats for Type B tools:
1. **Comma-separated** (in param order): `48.8,2.2,500,restaurant`
2. **Key=value pairs**: `lat=48.8 lon=2.2 radius=500 category=restaurant`
3. **JSON object**: `{"lat": 48.8, "lon": 2.2, "radius": 500, "category": "restaurant"}`

When parsing fails, error messages include helpful hints showing both formats.

## Test Results (Benchmark v4)

### Type A Tools (3) - 100% First-Try Success
| Tool | Tokens | Iterations |
|------|--------|------------|
| geocode | 316 | 1 |
| reverse | 320 | 1 |
| polyline_decode | 351 | 1 |
| **Total** | **987** | **3** |

### Type B Tools (with Multi-Format Shim)
| Tool | Tokens | Iterations | Method Used |
|------|--------|------------|-------------|
| distance | 1,257 | 3 | CSV after discovery |
| nearby | 328 | 1 | **CSV direct!** |

## Key Findings

### 1. LLM Can Use CSV Format Directly
When coordinates are clearly separated in the prompt ("latitude 48.8582 longitude 2.2945"), the LLM correctly infers comma-separated format:

```
Task: Find restaurants within 500 meters of latitude 48.8582 longitude 2.2945
LLM Response: echo '48.8582,2.2945,500,restaurant' > /n/osm/nearby/query
Result: SUCCESS (single iteration, 328 tokens)
```

### 2. Error Hints Help Recovery
When the LLM makes mistakes, the error message includes actionable hints:

```json
{
  "error": true,
  "code": "missing_param",
  "message": "required parameter 'lat1' not set. Use: echo 'lat1=... lon1=... lat2=... lon2=...' > query OR echo '...,...,...,...' > query (params: lat1, lon1, lat2, lon2)",
  "retryable": true
}
```

### 3. Discovery Pattern Still Works
Even when the LLM tries wrong approaches first, it can recover:
- Iteration 1: Try `start`/`end` files → fail
- Iteration 2: `ls` to discover available files
- Iteration 3: Use comma-separated format → success

## Comparison with Baseline

### Before (No Query Shim)
- Type B tools required 3+ iterations
- LLM had to discover individual param files
- No hints when errors occurred
- Average: ~1,300 tokens per Type B tool

### After (Multi-Format Query Shim)
- Type B tools can succeed in 1 iteration
- LLM can use familiar Type A pattern
- Helpful error hints guide recovery
- Best case: 328 tokens (nearby)
- Worst case: 1,257 tokens (distance with wrong initial guess)

## Token Efficiency

| Scenario | Type A | Type B (best) | Type B (worst) |
|----------|--------|---------------|----------------|
| AgentFS v4 | 329 avg | 328 | 1,257 |
| MCP Baseline | 6,091 avg | 6,145 avg | 6,145 avg |
| **Savings** | **94.6%** | **94.7%** | **79.5%** |

## Recommendations

1. **Prompt Engineering**: Clear separation of parameters in task prompts improves first-try success
2. **System Prompt**: Could mention "tools accept comma-separated parameters"
3. **_example File**: Provide usage examples in the namespace for complex tools

## Implementation Details

The multi-format shim in `agentfs.go`:
1. Tries JSON parsing first (if input starts with `{`)
2. Tries key=value parsing (if input contains `=`)
3. Tries comma-separated parsing (if part count matches param count)
4. Returns helpful error with format examples on failure
