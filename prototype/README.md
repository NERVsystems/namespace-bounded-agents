# 9P Server Prototype

Go implementation of the 9P filesystem server for LLM agent namespace isolation.

## Components

### `pkg/nerv9p/`

Core 9P implementation:

| File | Description |
|------|-------------|
| `server.go` | 9P server with namespace binding |
| `protocol.go` | 9P message types and encoding |
| `fs.go` | Virtual filesystem abstraction |
| `agentfs.go` | Agent-specific filesystem operations |
| `executor.go` | Tool execution within namespace |
| `rewriter.go` | Query path rewriting |

### `cmd/`

Command-line tools:

- `llm9p/` - LLM-facing 9P server
- `osm9p/` - OpenStreetMap data server (example)
- `agent/` - Agent driver for testing

## Building

```bash
go mod tidy
go build -o bin/llm9p ./cmd/llm9p
go build -o bin/osm9p ./cmd/osm9p
go build -o bin/agent ./cmd/agent
```

## Usage

Start the 9P server:
```bash
./bin/llm9p --port 5640
```

In another terminal, mount the namespace:
```bash
9pfuse localhost:5640 /mnt/agent
ls /mnt/agent/tools/
```

## Architecture

```
Agent Process
     │
     ▼
┌─────────────────┐
│  9P Client      │
│  (namespace)    │
└────────┬────────┘
         │ 9P protocol
         ▼
┌─────────────────┐
│  9P Server      │
│  (llm9p)        │
└────────┬────────┘
         │
         ▼
┌─────────────────┐
│  Backend Tools  │
│  (APIs, DBs)    │
└─────────────────┘
```

The agent only sees files bound into its namespace at initialization.
