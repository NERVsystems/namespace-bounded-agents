# Namespace-Bounded Agents

Artifacts for the paper: **"Namespace-Bounded Agents: Capability-Based Security for LLM Systems via 9P Filesystem Semantics"**

[![DOI](https://zenodo.org/badge/1145282350.svg)](https://doi.org/10.5281/zenodo.18419122)

## Abstract

We present a defense against prompt injection and tool misuse attacks on LLM-based agents by confining each agent to a per-process namespace derived from the Inferno operating system's 9P filesystem protocol. Unlike permission-based defenses that rely on runtime authorization decisions, our approach leverages Plan 9's capability-based model: an agent can only access resources explicitly bound into its namespace at initialization. Attackers cannot reference resources outside the namespace boundary regardless of prompt manipulation.

We evaluate our prototype against 629 prompt injection attacks from the AgentDojo benchmark and a custom 31-attack corpus, achieving **0% attack success rate** (ASR) under both. Formal verification using SPIN model checking (2,035 states) and CBMC bounded model checking (113 checks) confirms the isolation properties. Additionally, our filesystem-semantic tool interface reduces context token consumption by **83.5%** compared to JSON-RPC tool calling, while providing stateful query composition without extra LLM round-trips.

## Results Summary

| Evaluation | Attacks | 9P-Namespace ASR | MCP Baseline ASR |
|------------|---------|------------------|------------------|
| AgentDojo (full) | 629 | **0.0%** | 37.8% |
| Custom corpus | 31 | **0.0%** | 25.8% |
| Token efficiency | - | **83.5% reduction** | baseline |

## Repository Structure

```
namespace-bounded-agents/
├── paper/                      # arXiv manuscript source
│   ├── main-arxiv.tex         # LaTeX source
│   ├── references.bib         # Bibliography
│   └── arxiv.sty              # Style file
│
├── prototype/                  # 9P server implementation
│   ├── cmd/                   # Command-line tools
│   │   ├── llm9p/            # LLM-facing 9P server
│   │   ├── osm9p/            # OpenStreetMap 9P server
│   │   └── agent/            # Agent driver
│   ├── pkg/nerv9p/           # Core 9P implementation
│   └── go.mod                # Go module definition
│
├── evaluation/                 # Experimental evaluation
│   ├── security-eval/         # 31-attack custom corpus
│   │   ├── attacks/          # Attack definitions
│   │   ├── cmd/              # Evaluation harness
│   │   ├── pkg/              # Evaluation library
│   │   └── results/          # Multi-model results
│   │
│   ├── agentdojo/            # AgentDojo benchmark (629 attacks)
│   │   ├── cmd/              # Go 9P server
│   │   ├── python/           # Python agent + evaluator
│   │   ├── configs/          # Benchmark configurations
│   │   └── results/          # Evaluation results
│   │
│   └── token-efficiency/     # Token consumption benchmarks
│       ├── *.py              # Benchmark scripts
│       └── results/          # Comparison data
│
├── verification/              # Formal verification artifacts
│   ├── spin/                 # SPIN model checking
│   │   ├── namespace_isolation.pml
│   │   ├── namespace_isolation_extended.pml
│   │   └── namespace_locks.pml
│   │
│   ├── cbmc/                 # CBMC bounded model checking
│   │   ├── harness_refcount.c
│   │   ├── harness_mnthash_bounds.c
│   │   └── verify-all.sh
│   │
│   └── tla+/                 # TLA+ specifications
│       └── Namespace.tla
│
├── docs/                      # Additional documentation
├── LICENSE                    # MIT License
├── CITATION.cff              # Machine-readable citation
└── README.md                 # This file
```

## Requirements

### Core Requirements
- **Go 1.21+** - For prototype and evaluation harness
- **Python 3.10+** - For AgentDojo integration

### For Formal Verification (optional)
- **SPIN 6.5.2+** - Model checking
- **CBMC 5.95+** - Bounded model checking
- **TLC (TLA+ Toolbox)** - TLA+ model checking

### API Keys (for evaluation)
- OpenAI API key (GPT-4o, GPT-5)
- Anthropic API key (Claude Haiku, Sonnet)

## Quick Start

### 1. Clone the repository

```bash
git clone https://github.com/NERVsystems/namespace-bounded-agents.git
cd namespace-bounded-agents
```

### 2. Build the prototype

```bash
cd prototype
go mod tidy
go build -o bin/llm9p ./cmd/llm9p
go build -o bin/osm9p ./cmd/osm9p
```

### 3. Run SPIN verification

```bash
cd verification/spin
spin -a namespace_isolation_extended.pml
gcc -o pan pan.c -DSAFETY
./pan
# Expected: 2,035 states, 0 errors
```

### 4. Run CBMC verification

```bash
cd verification/cbmc
./verify-all.sh
# Expected: 113 checks, 0 failures
```

### 5. Run security evaluation

```bash
cd evaluation/security-eval
export OPENAI_API_KEY="your-key"
go build -o bin/seceval ./cmd/seceval
./bin/seceval --model gpt-4o --attack-set all
```

### 6. Run AgentDojo evaluation

```bash
cd evaluation/agentdojo/python
python -m venv .venv
source .venv/bin/activate
pip install agentdojo anthropic openai
python -m namespace_agent.evaluator --config ../configs/minimal_flat.yaml
```

## Reproducing Paper Results

### Table 2: Security Evaluation (31 attacks)

```bash
cd evaluation/security-eval
go build -o bin/seceval ./cmd/seceval
./bin/seceval --model gpt-4o --attack-set all --runs 4
./bin/seceval --model claude-3-5-haiku-20241022 --attack-set all --runs 4
./bin/seceval --model gpt-5 --attack-set all --runs 4
```

Results are in `evaluation/security-eval/results/`.

### Table 3: AgentDojo Benchmark (629 attacks)

```bash
cd evaluation/agentdojo/python
python -m namespace_agent.evaluator \
    --config ../configs/minimal_flat.yaml \
    --model claude-3-5-haiku-20241022
```

Full results: `evaluation/agentdojo/results/full_evaluation_20260125_153218/`

### Table 5: Token Efficiency

```bash
cd evaluation/token-efficiency
python tiktoken_compare.py
python full_benchmark.py
```

Results: `evaluation/token-efficiency/results/full_benchmark_results.json`

### Formal Verification Claims

| Claim | Command | Expected Output |
|-------|---------|-----------------|
| SPIN: 2,035 states, 0 errors | `./pan` (in spin/) | "State-vector 60 byte, depth reached 79, errors: 0" |
| CBMC: 113 checks, 0 failures | `./verify-all.sh` | "VERIFICATION SUCCESSFUL" |

## Models Evaluated

The following models were tested in our security evaluation:

| Model ID | Provider | API Endpoint |
|----------|----------|--------------|
| `gpt-4o-2024-08-06` | OpenAI | api.openai.com |
| `gpt-5-20250127` | OpenAI | api.openai.com |
| `claude-3-5-haiku-20241022` | Anthropic | api.anthropic.com |

## External Dependencies

- **InferNode**: Our fork of the Inferno kernel (not included in this repo)
  - Repository: [github.com/NERVsystems/infernode](https://github.com/NERVsystems/infernode)
  - Required for production deployment with kernel-enforced namespace isolation

- **AgentDojo**: ETH Zurich's benchmark framework
  - Repository: [github.com/ethz-spylab/agentdojo](https://github.com/ethz-spylab/agentdojo)
  - Install via: `pip install agentdojo`

## Citation

If you use this work, please cite:

```bibtex
@article{finn2026namespace,
  title={Namespace-Bounded Agents: Capability-Based Security for LLM Systems via 9P Filesystem Semantics},
  author={Finn, P. D.},
  journal={arXiv preprint},
  year={2026}
}
```

Or use the [CITATION.cff](CITATION.cff) file.

## License

This project is licensed under the MIT License - see the [LICENSE](LICENSE) file for details.

## Contact

For questions about this research, please open an issue on this repository.
