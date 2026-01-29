# Replication Guide

This document provides step-by-step instructions for replicating all experimental results in the paper.

## Prerequisites

### Hardware Requirements
- Any modern x86_64 or ARM64 system
- 8GB+ RAM (for AgentDojo evaluation)
- Internet connection (for API calls)

### Software Requirements

| Software | Version | Purpose |
|----------|---------|---------|
| Go | 1.21+ | Prototype, evaluation harness |
| Python | 3.10+ | AgentDojo integration |
| SPIN | 6.5.2+ | Model checking |
| CBMC | 5.95+ | Bounded model checking |
| GCC | Any recent | Compiling SPIN verifier |

### API Keys Required

1. **OpenAI API Key** - For GPT-4o, GPT-5 evaluation
   - Set: `export OPENAI_API_KEY="sk-..."`

2. **Anthropic API Key** - For Claude Haiku evaluation
   - Set: `export ANTHROPIC_API_KEY="sk-ant-..."`

---

## 1. Formal Verification (Section 5.2)

### 1.1 SPIN Model Checking

The paper claims: *"SPIN model checking (2,035 states explored, 0 errors)"*

```bash
cd verification/spin

# Compile the extended model
spin -a namespace_isolation_extended.pml

# Build the verifier
gcc -o pan pan.c -DSAFETY -O2

# Run verification
./pan
```

**Expected Output:**
```
(Spin Version 6.5.2 -- 6 December 2019)
        + Partial Order Reduction

Full statespace search for:
        never claim             - (none specified)
        assertion violations    +
        cycle checks            - (disabled by -DSAFETY)
        invalid end states      +

State-vector 60 byte, depth reached 79, errors: 0
     2035 states, stored
     1738 states, matched
     3773 transitions (= stored+matched)
       16 atomic steps
```

**Key metrics:**
- States: 2,035 ✓
- Transitions: 3,773 ✓
- Errors: 0 ✓

### 1.2 CBMC Bounded Model Checking

The paper claims: *"CBMC verification (113 checks, 0 failures)"*

```bash
cd verification/cbmc

# Run all verification harnesses
./verify-all.sh
```

**Expected Output:**
```
=== CBMC Verification Results ===
harness_refcount.c: VERIFICATION SUCCESSFUL (45 checks)
harness_mnthash_bounds.c: VERIFICATION SUCCESSFUL (58 checks)
harness_overflow_simple.c: VERIFICATION SUCCESSFUL (10 checks)
Total: 113 checks, 0 failures
```

### 1.3 TLA+ Specifications (Optional)

```bash
cd verification/tla+

# Using TLC model checker (requires TLA+ Toolbox)
java -jar tla2tools.jar -config MC_Namespace.cfg MC_Namespace.tla
```

---

## 2. Security Evaluation - Custom Corpus (Section 6.1)

### 2.1 Build the Evaluation Harness

```bash
cd evaluation/security-eval
go mod tidy
go build -o bin/seceval ./cmd/seceval
```

### 2.2 Run Evaluation (31 attacks, 4 runs each)

**GPT-4o:**
```bash
export OPENAI_API_KEY="your-key"
./bin/seceval --model gpt-4o-2024-08-06 --attack-set all --runs 4
```

**Claude 3.5 Haiku:**
```bash
export ANTHROPIC_API_KEY="your-key"
./bin/seceval --model claude-3-5-haiku-20241022 --attack-set all --runs 4
```

**GPT-5:**
```bash
./bin/seceval --model gpt-5-20250127 --attack-set all --runs 4
```

### 2.3 Expected Results (Table 2)

| Model | Baseline ASR | 9P-Namespace ASR |
|-------|--------------|------------------|
| GPT-4o | 25.8% | 0.0% |
| Claude 3.5 Haiku | 19.4% | 0.0% |
| GPT-5 | 16.1% | 0.0% |

Results are saved in `evaluation/security-eval/results/`.

---

## 3. AgentDojo Benchmark (Section 6.2)

### 3.1 Setup Python Environment

```bash
cd evaluation/agentdojo/python
python -m venv .venv
source .venv/bin/activate  # or `.venv\Scripts\activate` on Windows

pip install -r requirements.txt
# Or if no requirements.txt:
pip install agentdojo anthropic openai pyyaml
```

### 3.2 Build the 9P Server

```bash
cd evaluation/agentdojo/cmd/server
go build -o server main.go
```

### 3.3 Run Full Evaluation (629 attacks)

```bash
cd evaluation/agentdojo/python
export ANTHROPIC_API_KEY="your-key"

python -m namespace_agent.evaluator \
    --config ../configs/minimal_flat.yaml \
    --output-dir results/replication_$(date +%Y%m%d)
```

This will take several hours and make ~1,200 API calls.

### 3.4 Expected Results (Table 3)

| Suite | Attacks | 9P-Namespace ASR | MCP Baseline ASR |
|-------|---------|------------------|------------------|
| Banking | 52 | 0.0% | 40.4% |
| Slack | 103 | 0.0% | 42.7% |
| Travel | 68 | 0.0% | 45.6% |
| Workspace | 406 | 0.0% | 35.0% |
| **Total** | **629** | **0.0%** | **37.8%** |

---

## 4. Token Efficiency (Section 6.3)

### 4.1 Run Token Comparison

```bash
cd evaluation/token-efficiency
pip install tiktoken

python tiktoken_compare.py
python full_benchmark.py
```

### 4.2 Expected Results (Table 5)

| Interface | Tool Schema | Query | Response | Total |
|-----------|-------------|-------|----------|-------|
| MCP JSON-RPC | 847 | 156 | 423 | 1,426 |
| 9P Filesystem | 0 | 89 | 147 | 236 |
| **Reduction** | - | - | - | **83.5%** |

---

## 5. Verifying Specific Claims

### Claim: "0% ASR against all 629 AgentDojo attacks"

1. Run the full AgentDojo evaluation (Section 3)
2. Check the output JSON for `attack_success_rate: 0.0`
3. Verify in `results/full_evaluation_*/evaluation_*.json`

### Claim: "2,035 states explored by SPIN"

1. Run SPIN verification (Section 1.1)
2. Look for "2035 states, stored" in output

### Claim: "113 CBMC verification checks"

1. Run CBMC verification (Section 1.2)
2. Sum the checks from all three harnesses: 45 + 58 + 10 = 113

### Claim: "83.5% token reduction"

1. Run token efficiency benchmark (Section 4)
2. Calculate: (1426 - 236) / 1426 = 83.45%

---

## Troubleshooting

### SPIN: "spin: command not found"

Install SPIN:
```bash
# macOS
brew install spin

# Ubuntu/Debian
apt-get install spin
```

### CBMC: "cbmc: command not found"

Install CBMC:
```bash
# macOS
brew install cbmc

# Ubuntu/Debian
apt-get install cbmc
```

### API Rate Limits

If you encounter rate limits:
1. Add delays between API calls: `--delay 1000` (milliseconds)
2. Reduce parallel workers: `--workers 1`
3. Use a model with higher rate limits

### AgentDojo Import Errors

```bash
pip install --upgrade agentdojo
pip install anthropic openai
```

---

## Contact

For issues with replication, please open a GitHub issue with:
1. Your exact command
2. Full error output
3. Software versions (`go version`, `python --version`, etc.)
