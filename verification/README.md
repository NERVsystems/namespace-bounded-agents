# Formal Verification Artifacts

This directory contains formal verification of the namespace isolation properties.

## SPIN Model Checking (`spin/`)

Promela models verifying namespace isolation:

| File | Description | States |
|------|-------------|--------|
| `namespace_isolation.pml` | Basic isolation model | 83 |
| `namespace_isolation_extended.pml` | Extended with unmount | 2,035 |
| `namespace_locks.pml` | Locking protocol | 4,830 |

### Running SPIN Verification

```bash
cd spin
spin -a namespace_isolation_extended.pml
gcc -o pan pan.c -DSAFETY -O2
./pan
```

Expected: `errors: 0`, `2035 states, stored`

## CBMC Bounded Model Checking (`cbmc/`)

C harnesses verifying implementation safety:

| File | Checks | Description |
|------|--------|-------------|
| `harness_refcount.c` | 45 | Reference count safety |
| `harness_mnthash_bounds.c` | 58 | Array bounds (MOUNTH macro) |
| `harness_overflow_simple.c` | 10 | Integer overflow safety |

### Running CBMC Verification

```bash
cd cbmc
./verify-all.sh
```

Expected: `113 checks, 0 failures`

## TLA+ Specifications (`tla+/`)

High-level specifications for design verification:

- `Namespace.tla` - Core namespace model
- `NamespaceProperties.tla` - Safety/liveness properties
- `IsolationProof.tla` - Isolation proof outline

### Requirements

- SPIN 6.5.2+ (`spin --version`)
- CBMC 5.95+ (`cbmc --version`)
- TLA+ Toolbox (for TLA+ specs)
