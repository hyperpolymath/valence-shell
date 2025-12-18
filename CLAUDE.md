# CLAUDE.md - Valence Shell

## Project Identity

**Valence Shell** is a reversible shell implementing the Saga pattern at the command level. Every operation has an inverse. Every mutation is a transaction.

**Stack:** Elixir (OTP) + Ecto + Coq proofs
**NO:** Python, TypeScript, npm, Docker

## SACRED FILES — DO NOT MODIFY

The following files represent months of refined thinking. They are **VISION DOCUMENTS**, not implementation details.

```
README.adoc        — Project vision and architecture
STATE.adoc         — Cross-conversation context
ARCHITECTURE.md    — Design decisions
META.scm           — Project metadata
```

### Rules for Sacred Files:

1. **NEVER** modify without explicit human confirmation **in the same message**
2. **NEVER** "improve", "clean up", or "update" these files proactively
3. **ALWAYS** show a full diff before any proposed change
4. **ALWAYS** wait for explicit approval before applying changes
5. If asked to "update the README" — **ASK FIRST**, show the diff, wait

### Why This Matters:

Previous AI sessions destroyed the original README by "helpfully" updating it with framework details that overwrote the project vision. This lost months of work. **Do not repeat this.**

## Language Policy (RSR — Rhodium Standard Repository)

### Banned (Zero Tolerance):
- Python (except Salt provisioning)
- TypeScript
- CoffeeScript
- Go

### Required:
- Elixir for core runtime
- Coq for formal proofs
- ReScript if browser code ever needed

### Tooling:
- Podman, nerdctl (containers)
- Deno (if JS runtime needed)
- GitLab, Codeberg (hosting)
- justfile (task running)
- Docker
- npm
- GitHub Actions (use GitLab CI)

## Project Context

### What Valence Shell IS:
- A shell where every command is a reversible transaction
- Ecto-backed transactional semantics for shell operations
- POSIX-compatible (Phase 1 wraps `/bin/sh`)
- Part of the MAA Framework (RMR/RMO primitives)

### What Valence Shell is NOT:
- A fork of Oils shell (inspired by structure, clean-room implementation)
- Another Nushell/Fish/Elvish (those aren't reversible)
- A Python project (if you see Python, it's contamination — delete it)

### The Three Phases:
1. **Hypervisor** — Supervise `/bin/sh`, intercept reversible commands
2. **Hybrid Shim** — `LD_PRELOAD` syscall interception
3. **AST Transpiler** — Parse shell → Elixir AST

## Key Files

```
lib/valence/command.ex     — The Valence.Command behaviour (4 callbacks)
lib/valence/history/zipper.ex — In-memory undo/redo structure
lib/valence/saga.ex        — Compensating transaction orchestration
proofs/coq/rmr.v           — Reversibility axiom formal proof
justfile                   — Build/test/prove automation
```

## Commands

```bash
just deps      # Fetch dependencies
just verify    # Run tests + property checks
just prove     # Run Coq proofs (requires Coq)
just run       # Start the shell
```

## Integration Points

- **ECHIDNA** (`github.com/hyperpolymath/echidna`) — Multi-solver proof verification
- **Svalinn** (`github.com/hyperpolymath/svalinn`) — Container base images
- **Cerro Torre** (`github.com/hyperpolymath/cerro-torre`) — Orchestration
- **Conative Gating** (`github.com/hyperpolymath/conative-gating`) — AI enforcement

## When Starting a Session

1. Read this file first
2. Check STATE.adoc for current progress
3. Do NOT modify README.adoc without explicit permission
4. If you see Python files — they are contamination, flag for deletion

## Reporting Violations

If you (the AI) find yourself about to violate these rules, STOP and tell the human:

> "I was about to [action] which would violate the CLAUDE.md policy on [rule]. Should I proceed anyway?"

This is not optional. The human has experienced catastrophic data loss from AI "helpfulness".
