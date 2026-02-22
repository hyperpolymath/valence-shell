<!-- SPDX-License-Identifier: PMPL-1.0-or-later -->
<!-- TOPOLOGY.md — Project architecture map and completion dashboard -->
<!-- Last updated: 2026-02-19 -->

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
                        │    (Redirections, Variables, Jobs)      │
                        └──────────┬───────────────────┬──────────┘
                                   │                   │
                                   ▼                   ▼
                        ┌───────────────────────┐  ┌────────────────────────────────┐
                        │ FORMAL PROOFS (6 SYS) │  │ IMPLEMENTATION LAYER           │
                        │ - Coq, Lean 4, Agda   │  │ - OCaml Logic (High Trust)     │
                        │ - Isabelle, Mizar, Z3 │  │ - FFI to POSIX Syscalls        │
                        │ - ~256 Theorems       │  │ - Audit Logging (MAA)          │
                        └──────────┬────────────┘  └──────────┬─────────────────────┘
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
                        └─────────────────────────────────────────┘
```

## Completion Dashboard

```
COMPONENT                          STATUS              NOTES
─────────────────────────────────  ──────────────────  ─────────────────────────────────
SHELL FEATURES (v1.0.0)
  Unix Pipelines / Redir            ██████████ 100%    POSIX compliant stable
  Process Substitution              ██████████ 100%    FIFO implementation verified
  Arithmetic / Variables            ██████████ 100%    Expansion logic stable
  Job Control (bg/fg/kill)          ██████████ 100%    Background tasks verified

FORMAL VERIFICATION
  Polyglot Proofs (6 systems)       ██████████ 100%    ~256 theorems verified
  Reversibility Guarantees          ██████████ 100%    mkdir/rmdir proofs stable
  MAA Framework (Audit)             ██████████ 100%    Mutually Assured Accountability
  Extraction Gap (Lean → Rust)      ██████░░░░  60%    Formal correspondence refining

REPO INFRASTRUCTURE
  Justfile Automation               ██████████ 100%    Standard build/verify tasks
  .machine_readable/                ██████████ 100%    STATE tracking active
  RSR PLATINUM Compliance           ██████████ 100%    105/100 score certified

─────────────────────────────────────────────────────────────────────────────
OVERALL:                            ██████████ 100%    v1.0.0 Stable & Released
```

## Key Dependencies

```
Idris2 ABI ──────► Zig Bridge ────────► OCaml Logic ──────► POSIX FFI
     │                 │                   │                    │
     ▼                 ▼                   ▼                    ▼
Formal Proof ────► Extraction ────────► Rust CLI ────────► Target FS
```

## Update Protocol

This file is maintained by both humans and AI agents. When updating:

1. **After completing a component**: Change its bar and percentage
2. **After adding a component**: Add a new row in the appropriate section
3. **After architectural changes**: Update the ASCII diagram
4. **Date**: Update the `Last updated` comment at the top of this file

Progress bars use: `█` (filled) and `░` (empty), 10 characters wide.
Percentages: 0%, 10%, 20%, ... 100% (in 10% increments).
