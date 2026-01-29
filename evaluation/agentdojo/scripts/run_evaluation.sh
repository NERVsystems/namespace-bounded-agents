#!/bin/bash
# run_evaluation.sh - Run AgentDojo evaluation with namespace-bounded agent
#
# Usage:
#   ./run_evaluation.sh [options]
#
# Options:
#   --mode <security|utility|both>   Evaluation mode (default: both)
#   --domain <domain>                Run only specific domain (banking, workspace, travel, slack)
#   --output <dir>                   Output directory for results (default: results/)
#   --server-addr <addr>             9P server address (default: localhost:5640)
#   --model <model>                  LLM model to use (default: claude-3-5-sonnet-20241022)
#   --dry-run                        Run without LLM calls (for testing)
#   --help                           Show this help message

set -e

# Default configuration
MODE="both"
DOMAIN=""
OUTPUT_DIR="results"
SERVER_ADDR="localhost:5640"
MODEL="claude-3-5-sonnet-20241022"
DRY_RUN=false

# Script directory
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_DIR="$(dirname "$SCRIPT_DIR")"

# Parse arguments
while [[ $# -gt 0 ]]; do
    case $1 in
        --mode)
            MODE="$2"
            shift 2
            ;;
        --domain)
            DOMAIN="$2"
            shift 2
            ;;
        --output)
            OUTPUT_DIR="$2"
            shift 2
            ;;
        --server-addr)
            SERVER_ADDR="$2"
            shift 2
            ;;
        --model)
            MODEL="$2"
            shift 2
            ;;
        --dry-run)
            DRY_RUN=true
            shift
            ;;
        --help)
            head -20 "$0" | tail -18
            exit 0
            ;;
        *)
            echo "Unknown option: $1"
            exit 1
            ;;
    esac
done

# Validate mode
if [[ "$MODE" != "security" && "$MODE" != "utility" && "$MODE" != "both" ]]; then
    echo "Error: Invalid mode '$MODE'. Must be 'security', 'utility', or 'both'"
    exit 1
fi

# Validate domain if specified
if [[ -n "$DOMAIN" ]]; then
    if [[ "$DOMAIN" != "banking" && "$DOMAIN" != "workspace" && "$DOMAIN" != "travel" && "$DOMAIN" != "slack" ]]; then
        echo "Error: Invalid domain '$DOMAIN'. Must be 'banking', 'workspace', 'travel', or 'slack'"
        exit 1
    fi
fi

echo "=============================================="
echo "AgentDojo Namespace-Bounded Agent Evaluation"
echo "=============================================="
echo ""
echo "Configuration:"
echo "  Mode:        $MODE"
echo "  Domain:      ${DOMAIN:-all}"
echo "  Output:      $OUTPUT_DIR"
echo "  Server:      $SERVER_ADDR"
echo "  Model:       $MODEL"
echo "  Dry run:     $DRY_RUN"
echo ""

# Create output directory
TIMESTAMP=$(date +%Y%m%d_%H%M%S)
RESULT_DIR="$PROJECT_DIR/$OUTPUT_DIR/$TIMESTAMP"
mkdir -p "$RESULT_DIR"

echo "Results will be saved to: $RESULT_DIR"
echo ""

# Check if 9P server is running
check_server() {
    echo "Checking 9P server at $SERVER_ADDR..."
    if nc -z "${SERVER_ADDR%:*}" "${SERVER_ADDR#*:}" 2>/dev/null; then
        echo "  Server is running"
        return 0
    else
        echo "  Server is not running"
        return 1
    fi
}

# Start 9P server if not running
start_server() {
    echo "Starting 9P server..."

    # Build server if needed
    if [[ ! -f "$PROJECT_DIR/cmd/server/server" ]]; then
        echo "  Building server..."
        cd "$PROJECT_DIR"
        go build -o cmd/server/server ./cmd/server
    fi

    # Start server in background
    "$PROJECT_DIR/cmd/server/server" -addr "$SERVER_ADDR" &
    SERVER_PID=$!
    echo "  Started server with PID $SERVER_PID"

    # Wait for server to be ready
    sleep 2

    if ! check_server; then
        echo "Error: Failed to start server"
        exit 1
    fi
}

# Stop server if we started it
stop_server() {
    if [[ -n "$SERVER_PID" ]]; then
        echo "Stopping 9P server (PID $SERVER_PID)..."
        kill "$SERVER_PID" 2>/dev/null || true
        wait "$SERVER_PID" 2>/dev/null || true
    fi
}

# Trap to ensure cleanup
trap stop_server EXIT

# Check/start server
if ! check_server; then
    start_server
fi

echo ""

# Build Python command
PYTHON_CMD="python3 -m namespace_agent.evaluator"
PYTHON_ARGS="--server-addr $SERVER_ADDR --model $MODEL --output $RESULT_DIR"

if [[ -n "$DOMAIN" ]]; then
    PYTHON_ARGS="$PYTHON_ARGS --domain $DOMAIN"
fi

if [[ "$DRY_RUN" == "true" ]]; then
    PYTHON_ARGS="$PYTHON_ARGS --dry-run"
fi

# Run evaluation
cd "$PROJECT_DIR/python"

case $MODE in
    security)
        echo "Running security evaluation..."
        echo "  (Minimal namespace per task)"
        $PYTHON_CMD $PYTHON_ARGS --mode security
        ;;
    utility)
        echo "Running utility evaluation..."
        echo "  (Full namespace, MCP-equivalent)"
        $PYTHON_CMD $PYTHON_ARGS --mode utility
        ;;
    both)
        echo "Running security evaluation..."
        echo "  (Minimal namespace per task)"
        $PYTHON_CMD $PYTHON_ARGS --mode security

        echo ""
        echo "Running utility evaluation..."
        echo "  (Full namespace, MCP-equivalent)"
        $PYTHON_CMD $PYTHON_ARGS --mode utility
        ;;
esac

echo ""
echo "=============================================="
echo "Evaluation complete!"
echo "=============================================="
echo ""
echo "Results saved to: $RESULT_DIR"
echo ""
echo "Generated files:"
ls -la "$RESULT_DIR"
echo ""
echo "To generate paper tables, run:"
echo "  python3 scripts/generate_paper_results.py $RESULT_DIR"
