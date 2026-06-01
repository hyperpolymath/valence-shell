# PROOF-NEEDS.md
<!-- SPDX-License-Identifier: MPL-2.0 -->
<!-- Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk> -->

> **Reconciled 2026-06-01.** This file used to list 7 open Agda postulates
> from a pre-2026-04-03 snapshot — all 7 were closed during that session
> (see `docs/PROOF_HOLES_AUDIT.md`). The actual current state below.
>
> Canonical detail: **[docs/PROOF-NARRATIVE.adoc](docs/PROOF-NARRATIVE.adoc)**
> (assumption registry, cross-system witness matrix) and
> **[docs/PROOF-OPEN-FRONTIER.adoc](docs/PROOF-OPEN-FRONTIER.adoc)**
> (every valuable but unproven theorem, with tractability classification).

## Current State (2026-06-01)

- **LOC**: ~11,000 lines of formal proof (Coq 4,500 + Lean 4 2,400 + Agda 2,250 + Isabelle 1,800)
- **Languages**: Rust, ReScript, Agda, Idris2, Lean 4, Coq, Isabelle/HOL, Mizar, Z3, Zig
- **Proof systems**: 6 closed-core (Coq, Lean 4, Agda, Isabelle, Mizar, Z3) + 1 ABI-stub tier (Idris2)
- **Named theorems**: ~478 across the 7 systems (see narrative §3)

### Assumption Registry (live)

| Layer | Item | Location | Nature |
|---|---|---|---|
| Agda | `postulate funext` | `proofs/agda/FilesystemModel.agda:161-162` | Standard intensional-TT axiom; provable under `--cubical` |
| Coq | `admit.` mid-`single_op_reversible`, OpRmdir branch | `proofs/coq/filesystem_composition.v:199` | Model gap — `mkdir` writes `default_perms`, original may have had non-default |
| Coq | `Axiom is_empty_dir_dec` (justified) | `proofs/coq/posix_errors.v` | Infinite-domain universal quantification |
| Idris2 | 23 `?holes` across 4 files | `proofs/idris2/src/Filesystem/*.idr` | Type-stated, body un-discharged |

Idris2 holes by file:
- `Operations.idr`: 11 holes (mkdir/rmdir, touch/rm, write, op-independence, CNO)
- `RMO.idr`: 6 holes (secureDelete, overwrite, GDPR, hardwareErase, audit log)
- `Composition.idr`: 4 holes (sequence + composition + undo/redo)
- `Model.idr`: 2 holes (equivalence sym + trans)

### Foundational Closure (history)

| Date | Session | Closed |
|---|---|---|
| 2026-03-08 | P5 — Core reversibility | 4 priority-1 theorems |
| 2026-03-08 | P5 — Equivalence relations | 4 priority-2 theorems |
| 2026-03-22 | RMO closure | `obliterate_not_injective` (Lean 4) via 3 aux lemmas |
| 2026-04-03 | Agda closure session | All 7 Agda postulates eliminated (only `funext` remains, annotated) |
| 2026-04-03 | ReScript closure | All 24 `Obj.magic` in `impl/mcp/src/Server.res` replaced with `toolResultToJson` |
| 2026-04-12 | Coq well-formedness | `well_formed_ancestor_exists`, `mkdir_preserves_well_formed`, 5/6 decidability axioms proven |
| 2026-06-01 | Narrative reconciliation | `obliterate_overwrites_all_blocks` (which PROOF_HOLES_AUDIT listed as the gap) confirmed closed; actual gap identified as model-perm gap in composition.v |

### What Needs Proving (current, prioritised)

See `docs/PROOF-OPEN-FRONTIER.adoc` for the full Tier-S/A/B/C/D catalogue.
Highlights:

**Tier S (foundational)**:
1. Lean → Rust mechanised refinement
2. Close the `single_op_reversible` admit (Coq) — Tier A overlap; tractable
3. Crash-consistency for begin/commit/rollback
4. Concurrency safety (two `vsh` invocations on shared filesystem)

**Tier A (single-PR, <1 day each)**:
- Idris2: 11 of the 23 holes are purely-structural and could land in one porting PR
- Glob expansion termination + complexity bound
- Pratt-style precedence test corpus (POSIX shell `&&`/`||`/`!`)
- Path-traversal containment proof (`resolve_path` cannot escape sandbox)

**Tier B (multi-day)**:
- POSIX 2024 conformance proofs per M-feature
- Subshell `(...)` scoping
- Word splitting under quote-context
- Audit log HMAC signing + verification (impl + proof)

### Recommended Provers

- **Coq** — primary truth source for filesystem model
- **Lean 4** — canonical RMO proofs (`obliterate_not_injective` chain)
- **Agda** — minimum-axiom witness (eliminate funext via cubical)
- **Idris2** — ABI-level type expression (per estate convention `Zig=APIs+FFIs, Idris2=ABIs`)
- **Isabelle/HOL** — Sledgehammer cross-validation
- **Mizar** — set-theoretic third opinion
- **Z3 SMT** — counterexample search for non-existent recovery functions

### Priority

**HIGH** — Single Coq admit + 23 Idris2 holes are visible and closeable;
the bigger frontier (Lean→Rust refinement, crash-consistency, concurrency)
is real research-level work.

The MAA/GDPR claims depend on `?secureDeleteIrreversibleProof`,
`?overwriteIrreversibleProof`, and `?gdprDeletionCompliantProof` being
discharged. Until they are, the externally-facing "formally verified"
claim leans on the closed Coq/Lean 4 layer plus axiomatic NIST SP 800-88
/ Shannon-entropy / physical-world assumptions which should be made
explicit (see narrative §10).
