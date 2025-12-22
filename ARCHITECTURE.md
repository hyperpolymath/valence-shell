# Architecture

**Status:** This is a SACRED FILE. Do not modify without explicit human approval.

## Overview

Valence Shell is a reversible shell implementing the Saga pattern. Every command is a transaction with an inverse function.

```
F⁻¹(F(s)) = s  — Full reversibility without losing POSIX compliance
```

## Core Architecture

```
┌─────────────────────────────────────────────────────────────┐
│                     User / Agent                             │
└─────────────────────────┬───────────────────────────────────┘
                          │ Command
                          ▼
┌─────────────────────────────────────────────────────────────┐
│                    Valence.Saga                              │
│   Orchestrates multi-step transactions with compensation     │
└─────────────────────────┬───────────────────────────────────┘
                          │
          ┌───────────────┼───────────────┐
          │               │               │
          ▼               ▼               ▼
┌─────────────┐   ┌─────────────┐   ┌─────────────┐
│   Journal   │   │   History   │   │   Command   │
│ Idempotency │   │   Zipper    │   │  Behaviour  │
│  + Recovery │   │  Undo/Redo  │   │  4 Callbacks│
└─────────────┘   └─────────────┘   └─────────────┘
```

## The Three Phases

### Phase 1: Hypervisor (Current)

```
┌─────────────────────────────────────────┐
│           Valence Shell                  │
│  ┌─────────────────────────────────┐    │
│  │     Native Reversible Commands   │    │
│  │   (mkdir, touch, cp, mv, etc.)   │    │
│  └─────────────────────────────────┘    │
│                   │                      │
│                   │ Fallthrough          │
│                   ▼                      │
│  ┌─────────────────────────────────┐    │
│  │          /bin/sh                 │    │
│  │    (Unrecognized commands)       │    │
│  └─────────────────────────────────┘    │
└─────────────────────────────────────────┘
```

- Native commands execute with full transaction semantics
- Unknown commands pass through to underlying shell
- All output captured for history

### Phase 2: Hybrid Shim (Future)

```
┌─────────────────────────────────────────┐
│           Valence Shell                  │
│                   │                      │
│                   ▼                      │
│  ┌─────────────────────────────────┐    │
│  │   LD_PRELOAD / ptrace / eBPF    │    │
│  │    Syscall Interception Layer    │    │
│  └─────────────────────────────────┘    │
│                   │                      │
│                   ▼                      │
│  ┌─────────────────────────────────┐    │
│  │    Copy-on-Write Enforcement     │    │
│  └─────────────────────────────────┘    │
└─────────────────────────────────────────┘
```

- Intercept filesystem syscalls from any binary
- Transparent to the command being run
- Extends reversibility to ALL commands

### Phase 3: AST Transpiler (Dream)

```
┌─────────────────────────────────────────┐
│           Shell Script                   │
│   for f in *.txt; do mv $f $f.bak; done │
└─────────────────────────┬───────────────┘
                          │ Parse
                          ▼
┌─────────────────────────────────────────┐
│           Elixir AST                     │
│   Enum.each(glob("*.txt"), &move/1)     │
└─────────────────────────┬───────────────┘
                          │ Analyze
                          ▼
┌─────────────────────────────────────────┐
│        Side Effect Analysis              │
│   - Files affected: *.txt               │
│   - Operation: rename                    │
│   - Compensation: reverse rename         │
└─────────────────────────────────────────┘
```

## Component Details

### Valence.Command Behaviour

Every reversible operation implements four callbacks:

```elixir
@callback describe(args) :: :safe | :warn | :danger
@callback execute(args, key) :: {:ok, result, compensation} | {:error, reason}
@callback compensate(args, key) :: :ok | {:error, reason}
@callback verify(args) :: :ok | {:drift, expected, actual}
```

### Valence.History.Zipper

O(1) undo/redo using a functional zipper structure:

```
       Past (reversed)      │      Future
     [cmd3, cmd2, cmd1]     │    [cmd4, cmd5]
                            │
    ◄── back()         cursor        forward() ──►
```

- `push/1` — Add to history, clear redo stack
- `back/1` — Move cursor backward (undo)
- `forward/1` — Move cursor forward (redo)

### Valence.Journal

Idempotency and crash recovery:

```
Key: UUID ─────► Entry: {state, command, args, compensation}
                        │
                        ├── :pending (started)
                        ├── :completed (success)
                        ├── :compensated (rolled back)
                        └── :failed (error)
```

On restart, pending entries are recovered via `verify/1`.

### Valence.Saga

Compensating transaction orchestration:

```
Step 1 ──► Step 2 ──► Step 3 ──► FAIL!
                                   │
                                   ▼
Comp 1 ◄── Comp 2 ◄── Comp 3 ◄────┘
```

All-or-nothing semantics: either every step succeeds, or all are rolled back.

## Technology Choices

| Component | Choice | Rationale |
|-----------|--------|-----------|
| Runtime | Elixir/OTP | Supervision trees, pattern matching, no Python |
| Transactions | Ecto | Changeset semantics without database coupling |
| History | Zipper | O(1) navigation, functional, immutable |
| Proofs | Coq | Machine-checked, ECHIDNA integration |
| Containers | Podman | OCI-compliant, rootless, no Docker daemon |

## Security Model

### Trust Boundaries

```
┌─────────────────────────────────────┐
│ Formal Proofs (HIGH TRUST)          │  Mathematical guarantees
│ Coq/Lean/Agda/Isabelle/Mizar        │
└─────────────┬───────────────────────┘
              │ Extraction (GAP)
┌─────────────▼───────────────────────┐
│ Elixir Implementation (MEDIUM)      │  Type safe, pattern matching
└─────────────┬───────────────────────┘
              │ FFI (GAP)
┌─────────────▼───────────────────────┐
│ POSIX Syscalls (LOW TRUST)          │  Kernel guarantees only
└──────────────────────────────────────┘
```

### Agent Capabilities

Tier 0: Read-only (ls, cat, pwd)
Tier 1: Safe reversible (mkdir, touch)
Tier 2: Warn reversible (write, chmod)
Tier 3: Dangerous (rm, external APIs)
Tier 4: Forbidden (sudo, mount)

## Integration Points

- **ECHIDNA** — Multi-solver proof verification
- **Svalinn** — Container base images
- **Cerro Torre** — Orchestration patterns
- **Conative Gating** — AI enforcement layer

## Decision Log

### ADR-001: Elixir over Rust

**Context:** Need a runtime for the shell core.

**Decision:** Use Elixir/OTP.

**Rationale:**
- OTP supervision trees handle crashes gracefully
- Pattern matching ideal for command parsing
- Ecto provides transaction semantics
- No Python contamination risk

### ADR-002: Zipper over Stack

**Context:** Need undo/redo data structure.

**Decision:** Use Zipper instead of two stacks.

**Rationale:**
- Single coherent data structure
- O(1) for all navigation operations
- Well-understood from Haskell/Clojure
- Immutable, easy to reason about

### ADR-003: Coq for Proofs

**Context:** Need formal verification of reversibility.

**Decision:** Use Coq as primary, cross-validate with ECHIDNA.

**Rationale:**
- Mature ecosystem
- Extraction to OCaml
- ECHIDNA supports multi-solver validation
- Academic credibility for MAA Framework

---

**Last Updated:** 2025-12-18
**Version:** 0.1.0-alpha
