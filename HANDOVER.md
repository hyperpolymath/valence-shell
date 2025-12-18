# Valence Shell — Handover Document

**Date:** 2025-12-18
**Purpose:** Complete context for AI coding assistants working on this project
**Status:** Project vision recovered after catastrophic loss

---

## CRITICAL: READ CLAUDE.md FIRST

This project experienced **catastrophic data loss** when a previous AI session "helpfully" overwrote the README with framework boilerplate.

**Before doing ANYTHING:**
1. Read `CLAUDE.md` completely
2. Understand which files are SACRED
3. Never modify sacred files without explicit human approval + diff review

---

## Project Summary

**Valence Shell** is a reversible shell where every command is a transaction with an inverse function.

### The Core Insight

Traditional shells destroy information. `rm file` cannot be undone. `mv a b` leaves no trace. Pipelines fail halfway and leave debris.

Valence Shell treats commands as **Sagas** (distributed transaction pattern):
- Every operation has a compensation (inverse)
- External mutations get compensating transactions
- Crashes are recoverable via idempotency journal
- Full undo/redo via Zipper data structure

### The Goal

```
F⁻¹(F(s)) = s  — Full reversibility without losing POSIX compliance
```

---

## Architecture

### The Three Phases

| Phase | Name | Description | Status |
|-------|------|-------------|--------|
| 1 | Hypervisor | Supervise `/bin/sh`, intercept known commands | **Current** |
| 2 | Hybrid Shim | `LD_PRELOAD` syscall interception | Future |
| 3 | AST Transpiler | Parse shell → Elixir AST | Dream |

### Core Components

```
lib/valence/
├── command.ex           # Valence.Command behaviour (4 callbacks)
├── commands/            # Native reversible implementations
│   ├── file_ops.ex      # cp, mv, rm, touch, etc.
│   ├── directory.ex     # mkdir, rmdir, cd
│   └── ...
├── history/
│   ├── zipper.ex        # In-memory undo/redo (O(1))
│   └── journal.ex       # Idempotency + crash recovery
├── saga.ex              # Compensating transaction orchestration
└── supervisor.ex        # OTP supervision tree
```

### The Command Contract

Every reversible operation implements:

```elixir
@callback describe(args) :: :safe | :warn | :danger
# How risky is this operation?

@callback execute(args, idempotency_key) :: {:ok, result, compensation} | {:error, reason}
# Do the thing, return its inverse

@callback compensate(args, idempotency_key) :: :ok | {:error, reason}
# Undo the thing

@callback verify(args) :: :ok | {:drift, expected, actual}
# Did reality match expectations?
```

---

## Technology Decisions

### Stack

| Component | Choice | Rationale |
|-----------|--------|-----------|
| Runtime | Elixir/OTP | Supervision trees, pattern matching, no Python |
| Transactions | Ecto | Changesets without database coupling |
| History | Zipper | O(1) undo/redo, functional |
| Proofs | Coq | Machine-checked, ECHIDNA integration |
| Containers | Svalinn/Cerro Torre | Project standards |
| HTTP | Bandit | Optional API/GUI interface |

### Banned (RSR Policy)

- Python (if you see .py files, they're contamination)
- TypeScript
- Docker (use Podman)
- npm (use Deno if JS needed)
- GitHub Actions (use GitLab CI)

---

## Integration Points

### MAA Framework

Valence Shell implements:
- **RMR (Reversible Mutation Record)** — Every command generates a record with its inverse
- **RMO (Reversible Mutation Obliteration)** — Secure deletion with proof (when needed)

### ECHIDNA

The formal proof (`proofs/coq/rmr.v`) proving `F⁻¹(F(s)) = s` is verified by ECHIDNA's multi-solver integration (12+ solvers, neurosymbolic).

### Container Standards

- Base images: Svalinn (`github.com/hyperpolymath/svalinn`)
- Orchestration: Cerro Torre (`github.com/hyperpolymath/cerro-torre`)

---

## Current State

**As of 2025-12-18:**

- README.adoc: Recovered (was destroyed)
- Project structure: Not scaffolded yet
- Elixir code: Not written
- Coq proofs: Not written
- Tests: Not written

**Next Steps:**

1. Scaffold Elixir project with `mix new valence_shell --sup`
2. Create `Valence.Command` behaviour
3. Implement `Valence.History.Zipper`
4. Implement first native command (`file_ops.ex`)
5. Add property tests with StreamData

---

## Files in This Recovery Package

| File | Purpose |
|------|---------|
| `README.adoc` | Vision document — **SACRED** |
| `CLAUDE.md` | AI protection rules |
| `STATE.adoc` | Cross-conversation context — append only |
| `META.scm` | Machine-readable metadata |
| `ECOSYSTEM.scm` | Entry for /overview |
| `HANDOVER.md` | This file |

---

## Commands

Once scaffolded:

```bash
just deps      # mix deps.get
just verify    # mix test + property tests
just prove     # Run Coq proofs
just run       # Start the shell
```

---

## Questions to Resolve

1. **Phase 2 syscall interception:** `LD_PRELOAD` vs `ptrace` vs eBPF?
2. **Shell parser for Phase 3:** Tree-sitter? Custom PEG?
3. **Compensation storage:** SQLite? Mnesia? Plain files?
4. **GUI:** LiveView dashboard for history visualisation?

---

## Recovery Context

This README was destroyed on 2025-12-18 when an AI assistant overwrote it with generic RSR framework content. The project vision was reconstructed from:

- Conversation fragments across multiple Claude sessions
- User's notes about thermodynamic shell concept
- Saga pattern documentation
- MAA Framework integration details

Some original wording and specific implementation decisions were lost forever. This reconstruction represents the best recovery possible from available fragments.

**Lesson:** AI assistants will "helpfully" destroy your work. Use CLAUDE.md, git hooks, file permissions, and branch protection to prevent this.

---

## Contact

Jonathan D.A. Jewell
jonathan.jewell@open.ac.uk
The Open University
