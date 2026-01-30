# Token Efficiency Benchmarks

Comparison of token consumption between MCP JSON-RPC and 9P filesystem interfaces.

## Benchmarks

### `tiktoken_compare.py`

Token counting comparison using OpenAI's tiktoken library (cl100k_base encoding).

```bash
python tiktoken_compare.py
```

### `full_benchmark.py`

Comprehensive benchmark running actual API calls across 14 tools:

```bash
python full_benchmark.py
```

## Results Summary

### Schema Overhead (14 tools)

| Interface | Tokens | Per Tool |
|-----------|--------|----------|
| MCP JSON Schema | 1,430 | 102.1 |
| 9P Namespace | 248 | 17.7 |
| **Reduction** | **82.7%** | |

### Total Benchmark (14 tools, actual API calls)

| Metric | MCP | 9P | Savings |
|--------|-----|-----|---------|
| Total tokens | 85,867 | 14,148 | **83.5%** |
| Average tokens/tool | 6,133 | 1,088 | 82.3% |
| API calls | 28 | 15 | 46% fewer |
| Schema overhead | 40,040 | 248 | 99.4% |

### Why the Difference?

1. **JSON Schema vs Directory Listing**: MCP requires full JSON schema definitions; 9P uses simple directory listings
2. **Per-call overhead**: MCP sends schemas with every API call; 9P sends namespace once
3. **Format efficiency**: Filesystem paths are inherently terser than JSON structures

## Pre-computed Results

- `results/full_benchmark_results.json` - Detailed 14-tool benchmark with transcripts
- `results/mcp_vs_agentfs_results.json` - Earlier comparison test

## Requirements

```bash
pip install tiktoken anthropic
```

## Reproducing Results

```bash
# Quick schema comparison (no API calls)
python tiktoken_compare.py

# Full benchmark with API calls (requires ANTHROPIC_API_KEY)
python full_benchmark.py
```
