<!--
SPDX-License-Identifier: CC-BY-SA-4.0
Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
-->
# For Developers

You want to build Valence Shell, read or extend the proofs, or contribute code.
This page orients you; the canonical developer guide is
[`QUICKSTART-DEV.adoc`](https://github.com/hyperpolymath/valence-shell/blob/main/QUICKSTART-DEV.adoc).

---

## The stack at a glance

| Layer | Language | Location |
|-------|----------|----------|
| Interactive shell (primary deliverable) | **Rust** (crate `vsh`) | `impl/rust-cli/` |
| Formal proofs (6 systems) | **Coq, Lean 4, Agda, Isabelle/HOL, Mizar, Z3** | `proofs/` |
| ABI / proof carrier | **Idris2** | `proofs/idris2/`, `src/abi/` |
| C-ABI FFI boundary | **Zig** (exports `valence_shell_*`) | `ffi/zig/` |
| Verified POSIX helper library | **Rust** (`vsh-ffi`) | `ffi/rust/` |
| Reference impl / MCP server | **Elixir / ReScript** | `impl/elixir/`, `impl/mcp/` |

Architecture deep-dive: [`docs/ARCHITECTURE.md`](https://github.com/hyperpolymath/valence-shell/blob/main/docs/ARCHITECTURE.md)
and the evidence-backed [`EXPLAINME.adoc`](https://github.com/hyperpolymath/valence-shell/blob/main/EXPLAINME.adoc).

## Build & test

> **Tooling policy:** this project uses **`just`** as its task runner (`make` is
> banned). Environments are provided via **Guix** (preferred) or **Nix**
> (fallback).

```bash
# Environment
guix shell            # preferred
nix develop           # fallback

# The shell (only needs a Rust toolchain)
cd impl/rust-cli
cargo build --release
cargo test            # 791 passing, 0 failures, 14 ignored (2026-08-24)

# Re-check the proofs (needs the proof assistants installed)
just verify-proofs    # all systems
just build-lean4      # or one at a time: coq / agda / isabelle / mizar / z3
```

Run the ignored slow/stress tests explicitly with `cargo test -- --ignored`.

## The proof systems and their roles

Agda is the theory source of truth (owner ruling 2026-11-09, under standards
`3-practice/PROOF-POLICY.adoc`). Lean 4 and Coq are recheck legs: their proofs
build, but their statements have not yet been compared one by one with the
Agda source, so they are target-only evidence until that comparison is done.
Isabelle/HOL and Mizar were archived unchecked on 2026-11-09
(`archive/proofs/`) and are not current evidence.

| System | Foundation | Role |
|--------|-----------|------|
| Agda | Intensional type theory | Theory source of truth (`--safe --without-K --cubical-compatible`) |
| Lean 4 | Dependent type theory | Recheck leg; executable model oracle |
| Coq | Calculus of Inductive Constructions | Recheck leg; extraction path to OCaml |
| Z3 SMT | First-order logic + theories | Solver checks (PROOF-POLICY §5 `ASSUMED`) |
| Isabelle/HOL | Higher-order logic | Archived, unchecked |
| Mizar | Tarski–Grothendieck set theory | Archived, unchecked |

**Read the honest status first:** the project maintains a single source of truth
for open proof holes —
[`docs/PROOF_HOLES_AUDIT.adoc`](https://github.com/hyperpolymath/valence-shell/blob/main/docs/PROOF_HOLES_AUDIT.adoc).
As of this writing: **0 real gaps** (the former Coq `obliterate_overwrites_all_blocks`
gap is CLOSED — re-verified 2026-07-16 via `Print Assumptions` as *Closed under
the global context* under Coq 8.18.0), plus 1 justified classical dependency
(Coq `is_empty_dir_dec`, a theorem proved with classical logic, not a custom
axiom). The Agda `funext` postulate was removed 2026-11-09.
The Idris2 ABI layer is **hole-free** (closed under `--total`) with 2 registered
primitive-equality axioms gated by CI.

## Contributing

Contribution rules are enforced by machine, not just convention. Before you open
a PR, read:

- [`CONTRIBUTING.md`](https://github.com/hyperpolymath/valence-shell/blob/main/CONTRIBUTING.md)
  — the Tri-Perimeter Contribution Framework (core / extensions / community).
- `.machine_readable/MUST.contractile` — the hard invariants. Highlights:
  - No `believe_me`/`assert_total` (Idris2), no new `Admitted.` (Coq), no `sorry`
    (Lean), no `Obj.magic` (OCaml).
  - No `unsafe {}` block in Rust without an inline `// SAFETY:` comment.
  - Language policy (see `.claude/CLAUDE.md`): no new TypeScript/Go/general
    Python; Deno over Node; `just` over `make`.
  - Commits must be GPG-signed.
- K9 validators in `contractiles/k9/` run these checks on every PR.

Pre-PR checklist:

```bash
just lint             # format + lint
just test             # all tests pass
just panic-scan       # panic-safety scan
```

## Fuzzing

Seven `cargo-fuzz` targets live in `impl/rust-cli/fuzz/fuzz_targets/` (parser,
arith, job-spec, signal-parse, path-ops, glob-expansion, state-machine). CI runs
them via ClusterFuzzLite (`.clusterfuzzlite/`, `.github/workflows/cflite_*.yml`)
using the **address** sanitizer — the one cargo-fuzz reliably supports for Rust.

## AI-assisted development

If you use an AI assistant, load the project context first: `just llm-context`,
or read `0-AI-MANIFEST.a2ml` and `.claude/CLAUDE.md`. The `.machine_readable/`
tree holds structured state/meta/ecosystem files.

---

## Where to go next

- Packaging & deployment → [For Platform Maintainers](For-Platform-Maintainers)
- The ABI/FFI boundary → [`docs/ABI-FFI-BOUNDARY.md`](https://github.com/hyperpolymath/valence-shell/blob/main/docs/ABI-FFI-BOUNDARY.md)
- Honest limits → [Verification Status](Verification-Status)
