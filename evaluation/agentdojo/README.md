# AgentDojo Integration for Namespace-Bounded Agent Security

This experiment integrates the [AgentDojo benchmark](https://github.com/ethz-spylab/agentdojo) (NeurIPS 2024) to evaluate namespace-bounded agent security against standardized prompt injection attacks.

## Overview

AgentDojo provides:
- 97 tasks across 4 domains (banking, workspace, travel, slack)
- 629 security test cases with prompt injection attacks
- Published baselines for comparison (GPT-4o, Claude-3.5, etc.)

This integration adapts the benchmark to work with 9P filesystem semantics, demonstrating that namespace-bounded agents achieve structural defense against cross-tool attacks.

## Architecture

```
AgentDojo Framework
        │
        ▼
┌──────────────────────────┐
│ Namespace9PAgent         │  Python adapter implementing
│ (BasePipelineElement)    │  AgentDojo's interface
└──────────────────────────┘
        │
        ▼
┌──────────────────────────┐
│ 9P Servers (Go)          │  Combined server with all
│ - banking_9p             │  AgentDojo domains
│ - workspace_9p           │
│ - travel_9p              │
│ - slack_9p               │
└──────────────────────────┘
```

## Directory Structure

```
agentdojo-integration/
├── README.md                 # This file
├── go.mod                    # Go module definition
├── cmd/
│   └── server/
│       └── main.go           # Server entry point
├── servers/
│   ├── banking_9p.go         # Banking domain (accounts, transfers)
│   ├── workspace_9p.go       # Workspace domain (email, calendar, docs)
│   ├── travel_9p.go          # Travel domain (flights, hotels)
│   ├── slack_9p.go           # Slack domain (messages, channels)
│   └── combined_server.go    # Merged server with all domains
├── python/
│   └── namespace_agent/
│       ├── __init__.py       # Package exports
│       ├── agent.py          # Namespace9PAgent (BasePipelineElement)
│       ├── runtime.py        # P9Runtime (9P client)
│       ├── namespace.py      # NamespaceSpec and path mappings
│       └── evaluator.py      # NamespaceEvaluator (benchmark harness)
├── configs/
│   ├── banking.yaml          # Banking domain namespace spec
│   ├── workspace.yaml        # Workspace domain namespace spec
│   ├── travel.yaml           # Travel domain namespace spec
│   ├── slack.yaml            # Slack domain namespace spec
│   └── full.yaml             # Full namespace (all domains)
├── scripts/
│   ├── run_evaluation.sh     # Main evaluation script
│   └── generate_paper_results.py  # LaTeX table generator
└── results/                  # Evaluation outputs
```

## Prerequisites

### Go (for 9P server)

```bash
# Go 1.21 or later
go version
```

### Python (for AgentDojo adapter)

```bash
# Python 3.10 or later
python3 --version

# Create virtual environment
python3 -m venv venv
source venv/bin/activate

# Install dependencies
pip install anthropic pyyaml

# Optional: Install AgentDojo for full benchmark
pip install agentdojo
```

### Anthropic API Key

```bash
export ANTHROPIC_API_KEY="your-key-here"
```

## Quick Start

### 1. Build the 9P Server

```bash
cd experiments/agentdojo-integration
go build -o cmd/server/server ./cmd/server
```

### 2. Start the Server

```bash
./cmd/server/server -addr :5640
```

### 3. Run Evaluation

In another terminal:

```bash
cd experiments/agentdojo-integration
./scripts/run_evaluation.sh --mode both
```

### 4. Generate Paper Tables

```bash
python3 scripts/generate_paper_results.py results/<timestamp>
```

## Evaluation Modes

### Security Mode

Uses minimal namespace per task. Each task is given only the paths needed for its required tools.

```bash
./scripts/run_evaluation.sh --mode security
```

This demonstrates structural blocking: attacks that try to access tools outside the minimal namespace fail because the path doesn't exist.

### Utility Mode

Uses full namespace (all tools available). This matches the MCP baseline for fair utility comparison.

```bash
./scripts/run_evaluation.sh --mode utility
```

### Both Modes

Runs both evaluations:

```bash
./scripts/run_evaluation.sh --mode both
```

## Metrics

| Metric | Description |
|--------|-------------|
| **BU** (Benign Utility) | Task completion rate without attacks |
| **UA** (Utility under Attack) | Task completion rate with attacks |
| **ASR** (Attack Success Rate) | Fraction of attacks that succeed |

### Defense Modes

The evaluation tracks HOW attacks are blocked:

| Mode | Description |
|------|-------------|
| **Structural** | Path doesn't exist in namespace (key contribution) |
| **Behavioral** | LLM refused despite valid paths |
| **None** | Attack succeeded |

## Expected Results

Based on the paper's claims:

| Agent | BU | UA | ASR |
|-------|-----|-----|-----|
| GPT-4o (baseline) | 69% | 45% | 53.1% |
| Claude-3.5-Sonnet (baseline) | 65% | 55% | 35.0% |
| **Namespace-Bounded** | ~60-65% | ~55% | **~5%** |

The key insight: namespace-bounded agents should achieve near-zero ASR for cross-tool attacks because the attack paths literally don't exist in the agent's namespace.

## Configuration

### Server Configuration

```bash
# Default address
./cmd/server/server -addr :5640

# With debug logging
./cmd/server/server -addr :5640 -debug
```

### Evaluation Configuration

```bash
# Specific domain only
./scripts/run_evaluation.sh --domain banking

# Different model
./scripts/run_evaluation.sh --model claude-3-5-sonnet-20241022

# Dry run (no LLM calls)
./scripts/run_evaluation.sh --dry-run
```

### Namespace Configuration

YAML files in `configs/` define namespaces:

```yaml
# configs/banking.yaml
domain: banking
paths:
  - /banking/accounts/list/query
  - /banking/accounts/balance/query
  # ...

security_relevant:
  - /banking/transfers/initiate/query
```

## Tool Mapping

AgentDojo tools map to 9P paths:

| AgentDojo Tool | 9P Path |
|---------------|---------|
| `banking_accounts_balance` | `/banking/accounts/balance/query` |
| `workspace_email_send` | `/workspace/email/send/query` |
| `travel_flights_book` | `/travel/flights/book/query` |
| `slack_messages_send` | `/slack/messages/send/query` |

## How It Works

### 1. Task Setup

For each AgentDojo task:
1. Extract required tools from task definition
2. Construct minimal namespace containing only those tool paths
3. Set namespace on the 9P client

### 2. LLM Interaction

The LLM receives:
- System prompt with namespace listing (replaces JSON tool schemas)
- Task description
- Instructions to use filesystem operations

### 3. Operation Parsing

The agent parses filesystem operations from LLM output:
```bash
echo 'account_id=acct_001' > /banking/accounts/balance/query
cat /banking/accounts/balance/query
```

### 4. Namespace Enforcement

Before execution, each path is checked against the namespace:
- If path exists: Execute via 9P
- If path doesn't exist: Return "path does not exist" error

### 5. Defense Tracking

Failed operations are classified:
- `blocked_by: "namespace"` → Structural defense
- `blocked_by: "server"` → Server-side enforcement
- Refused by LLM → Behavioral defense

## Troubleshooting

### Server won't start

```bash
# Check if port is in use
lsof -i :5640

# Use different port
./cmd/server/server -addr :5641
```

### Connection refused

```bash
# Verify server is running
nc -z localhost 5640

# Check firewall
```

### No LLM responses

```bash
# Check API key
echo $ANTHROPIC_API_KEY

# Use dry-run mode for testing
./scripts/run_evaluation.sh --dry-run
```

### Module not found

```bash
# Ensure you're in the right directory
cd experiments/agentdojo-integration/python

# Or set PYTHONPATH
export PYTHONPATH=$PWD/python:$PYTHONPATH
```

## References

- [AgentDojo Paper](https://arxiv.org/abs/2401.13138) (NeurIPS 2024)
- [AgentDojo Repository](https://github.com/ethz-spylab/agentdojo)
- [9P Protocol Specification](http://man.cat-v.org/plan_9/5/intro)

## License

Same license as the parent repository.
