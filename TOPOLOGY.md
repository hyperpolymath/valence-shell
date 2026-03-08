<!-- SPDX-License-Identifier: PMPL-1.0-or-later -->
<!-- TOPOLOGY.md — Project architecture map and completion dashboard -->
<!-- Last updated: 2026-03-08 -->

# Valence Shell (vsh) — Project Topology

## System Architecture

```
                        ┌─────────────────────────────────────────┐
                        │              OPERATOR / ADMIN           │
                        │        (Interactive REPL / Compliance)  │
                        └───────────────────┬─────────────────────┘
                                            │ Command / Pipeline
                                            ▼
                        ┌─────────────────────────────────────────┐
                        │           VALENCE SHELL (RUST)          │
                        │  Parser → Executor → State → Undo/Redo │
                        │  Pipelines, Redirections, Variables     │
                        │  Control Structures, Job Control        │
                        │  chmod/chown, cp/mv/ln -s               │
                        └──────────┬───────────────────┬──────────┘
                                   │                   │
                                   ▼                   ▼
                        ┌───────────────────────┐  ┌────────────────────────────────┐
                        │ FORMAL PROOFS (6 SYS) │  │ IMPLEMENTATION LAYER           │
                        │ - Lean 4 (primary)    │  │ - Zig FFI (builds, unlinked)   │
                        │ - Coq (CIC)           │  │ - Rust FFI (preconditions)     │
                        │ - Agda (ITT)          │  │ - libc direct (chown/getpw*)   │
                        │ - Isabelle/HOL        │  │ - Audit Logging (MAA)          │
                        │ - Mizar (set theory)  │  └──────────┬─────────────────────┘
                        │ - Z3 (SMT)            │             │
                        │ ~250+ theorems        │             │
                        │ 4 gaps, 4 axioms      │             │
                        └──────────┬────────────┘             │
                                   │                          │
                                   └────────────┬─────────────┘
                                                ▼
                        ┌─────────────────────────────────────────┐
                        │           TARGET FILESYSTEM             │
                        │      (Provably Reversible State)        │
                        └─────────────────────────────────────────┘

                        ┌─────────────────────────────────────────┐
                        │          REPO INFRASTRUCTURE            │
                        │  Justfile / Nix     .machine_readable/  │
                        │  RSR PLATINUM       0-AI-MANIFEST.a2ml  │
                        │  24 CI workflows    .well-known/        │
                        └─────────────────────────────────────────┘
```

## Completion Dashboard

```
COMPONENT                          STATUS              NOTES
─────────────────────────────────  ──────────────────  ─────────────────────────────────
SHELL FEATURES (v0.9.0)
  Pipelines / Redirections         ██████████ 100%    All 8 redirect types, multi-stage pipes
  Process Substitution             ██████████ 100%    FIFO implementation verified
  Arithmetic / Variables           ██████████ 100%    Expansion, arrays, parameter ops
  Control Structures               ██████████ 100%    if/elif/else, while, for, case/esac
  Glob / Quote / Command Sub       ██████████ 100%    POSIX compliant
  Job Control (bg/fg/kill)         ████████░░  80%    Missing SIGCHLD, Ctrl+Z
  Shell Builtins                   ████████░░  80%    30 implemented, ~15 POSIX missing
  Reversible Builtins (8 ops)      ██████████ 100%    mkdir/rmdir/touch/rm/cp/mv/ln/chmod/chown
  Functions                        ░░░░░░░░░░   0%    Not started
  Shell Script Execution           ░░░░░░░░░░   0%    Not started

FORMAL VERIFICATION
  Polyglot Proofs (6 systems)      █████████░  90%    ~250+ theorems, 4 gaps remain
  Reversibility Proofs             ██████████ 100%    All 8 ops proven in all 6 systems
  Permission Proofs (chmod/chown)  ██████████ 100%    NEW — 42 theorems across 6 systems
  MAA Framework (RMR)              ██████████ 100%    Reversible ops with audit trails
  MAA Framework (RMO)              ██░░░░░░░░  20%    Irreversibility proofs, stubs only
  Extraction Gap (Lean → Rust)     ██████░░░░  60%    ~95% confidence via property testing

IMPLEMENTATION LAYERS
  Rust CLI (primary)               ████████░░  82%    15,720 lines, 602 tests, v0.9.0
  Zig FFI                          █████░░░░░  50%    Builds, not integrated
  Elixir NIF                       ███░░░░░░░  30%    Stale, broken build
  OCaml Extraction                 ██░░░░░░░░  20%    Design only

REPO INFRASTRUCTURE
  Justfile Automation              ██████████ 100%    Standard build/verify tasks
  .machine_readable/               ██████████ 100%    STATE, ECOSYSTEM, META tracking
  RSR PLATINUM Compliance          ██████████ 100%    105/100 score certified
  CI/CD (24 workflows)             █████████░  90%    Lean verification, fuzzing, quality

─────────────────────────────────────────────────────────────────────────────
OVERALL:                            ███████░░░  72%    v0.9.0 Research Prototype
```

## Key Dependencies

```
Lean 4 Proofs ──────► lakefile.lean ──────► Lake build ──────► CI verification
                          │
                          ▼
Coq Proofs ─────────► _CoqProject ──────► coq_makefile ──────► (manual)
                          │
                          ▼
Agda/Isabelle/Mizar ► (no build sys) ──► (manual verification)

Rust CLI ───────────► Cargo.toml ──────► cargo test (602) ──► CI (rust-cli.yml)
                          │
                          ▼
                     proof_refs.rs ────► Maps ops to theorems across 6 systems
                          │
                          ▼
                     correspondence ───► 59 tests validate Lean↔Rust (~95%)
```

## Seam Map (Proximal)

| From | To | Seam File | Status |
|------|----|-----------|--------|
| Lean 4 proofs | Lake build | `lakefile.lean` | 10 libs registered |
| Coq proofs | Coq build | `_CoqProject` | 11 files listed |
| Rust operations | Proof theorems | `proof_refs.rs` | 11 op types mapped |
| Rust impl | Lean validation | `correspondence_tests.rs` | 28 tests |
| Rust impl | Property validation | `lean4_proptest_correspondence.rs` | 16 tests |
| Rust impl | Extended validation | `property_correspondence_tests.rs` | 15 tests |
| Zig FFI | Rust CLI | Not linked | **GAP** |
| Elixir NIF | Rust CLI | Broken | **GAP** |

## Update Protocol

This file is maintained by both humans and AI agents. When updating:

1. **After completing a component**: Change its bar and percentage
2. **After adding a component**: Add a new row in the appropriate section
3. **After architectural changes**: Update the ASCII diagram
4. **Date**: Update the `Last updated` comment at the top of this file

Progress bars use: `█` (filled) and `░` (empty), 10 characters wide.
Percentages: 0%, 10%, 20%, ... 100% (in 10% increments).
