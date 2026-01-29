# Token Efficiency Benchmarks

Comparison of token consumption between MCP JSON-RPC and 9P filesystem interfaces.

## Benchmarks

### `tiktoken_compare.py`

Basic token counting comparison using OpenAI's tiktoken library.

```bash
python tiktoken_compare.py
```

### `full_benchmark.py`

Comprehensive benchmark across multiple operations:

```bash
python full_benchmark.py
```

## Results Summary

| Interface | Tool Schema | Query | Response | Total |
|-----------|-------------|-------|----------|-------|
| MCP JSON-RPC | 847 | 156 | 423 | 1,426 |
| 9P Filesystem | 0 | 89 | 147 | 236 |
| **Reduction** | 100% | 43% | 65% | **83.5%** |

### Why the Difference?

1. **Tool Schema (847 → 0)**: 9P discovers tools by directory listing, not JSON schemas
2. **Query (156 → 89)**: Filesystem paths are shorter than JSON-RPC method calls
3. **Response (423 → 147)**: Plain text output vs. JSON wrapper

## Pre-computed Results

- `results/full_benchmark_results.json` - Detailed per-operation breakdown
- `results/mcp_vs_agentfs_results.json` - Head-to-head comparison

## Requirements

```bash
pip install tiktoken
```
