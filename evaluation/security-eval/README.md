# Security Evaluation - Custom Corpus

31-attack corpus for evaluating namespace isolation against prompt injection.

## Attack Categories

| Category | Attacks | Description |
|----------|---------|-------------|
| Direct Injection | 8 | Explicit malicious instructions |
| Indirect/Tool-based | 12 | Attacks via tool responses |
| Capability Escalation | 6 | Attempts to access unauthorized tools |
| Social Engineering | 5 | Context manipulation attacks |

## Running the Evaluation

### Build

```bash
go mod tidy
go build -o bin/seceval ./cmd/seceval
```

### Run

```bash
# Single model, all attacks
export OPENAI_API_KEY="your-key"
./bin/seceval --model gpt-4o --attack-set all

# Multiple runs for statistical significance
./bin/seceval --model gpt-4o --attack-set all --runs 4

# Specific attack category
./bin/seceval --model gpt-4o --attack-set capability_escalation
```

### Options

| Flag | Description |
|------|-------------|
| `--model` | Model ID (gpt-4o, claude-3-5-haiku-20241022, etc.) |
| `--attack-set` | Attack category or "all" |
| `--runs` | Number of runs per attack |
| `--output` | Output file path |

## Results Format

```json
{
  "model": "gpt-4o",
  "total_attacks": 31,
  "successful_attacks": 0,
  "attack_success_rate": 0.0,
  "results": [
    {
      "attack_id": "DI-1",
      "category": "direct_injection",
      "success": false,
      "blocked_by": "namespace_boundary"
    }
  ]
}
```

## Pre-computed Results

Results from our paper are in `results/`:

| File | Model | ASR |
|------|-------|-----|
| `gpt4o_4runs.json` | GPT-4o | 0.0% |
| `claude_4runs.json` | Claude 3.5 Haiku | 0.0% |
| `gpt5_4runs.json` | GPT-5 | 0.0% |
| `full_baseline.json` | MCP Baseline | 25.8% |
