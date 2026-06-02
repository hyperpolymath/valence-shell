# PROOF-NEEDS.md
<!-- SPDX-License-Identifier: MPL-2.0 -->
<!-- Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk> -->

> **Reconciled 2026-06-02 (afternoon).** Earlier sweeps closed the
> Agda postulates (2026-04-03). This pass closed the remaining 3 Coq
> admits (#56 / #57 / #58 — see "Foundational Closure" below) and
> reconciled the Idris2-hole inventory against the live source. The
> actual current state below.
>
> Canonical detail: **[docs/PROOF-NARRATIVE.adoc](docs/PROOF-NARRATIVE.adoc)**
> (assumption registry, cross-system witness matrix) and
> **[docs/PROOF-OPEN-FRONTIER.adoc](docs/PROOF-OPEN-FRONTIER.adoc)**
> (every valuable but unproven theorem, with tractability classification).

## Current State (2026-06-02)

- **LOC**: ~11,000 lines of formal proof (Coq 4,500 + Lean 4 2,400 + Agda 2,250 + Isabelle 1,800)
- **Languages**: Rust, ReScript, Agda, Idris2, Lean 4, Coq, Isabelle/HOL, Mizar, Z3, Zig
- **Proof systems**: 6 closed-core (Coq, Lean 4, Agda, Isabelle, Mizar, Z3) + 1 ABI-stub tier (Idris2)
- **Named theorems**: ~478 across the 7 systems (see narrative §3)

### Assumption Registry (live)

| Layer | Item | Location | Nature |
|---|---|---|---|
| Agda | `postulate funext` | `proofs/agda/FilesystemModel.agda:161-162` | Standard intensional-TT axiom; provable under `--cubical` |
| Coq | `Axiom is_empty_dir_dec` (justified) | `proofs/coq/posix_errors.v` | Infinite-domain universal quantification |
| Coq | (closed) `mkdir_two_dirs_reversible` | `filesystem_composition.v` | Closed via LIFO restate — only standard funext (#56 closed) |
| Coq | (closed) `overwrite_pass_equalizes_storage` | `rmo_operations.v` | Closed via `Hgeom` strengthened with `block_overwritten` (#57 closed — zero axioms) |
| Coq | (closed) `obliterate_not_injective` | `rmo_operations.v` | Closed via threaded strengthened `Hgeom` through `multi_pass_same_start_same_result` (#58 closed — only standard funext) |
| Idris2 | `axStringEqRefl` (primitive-eq axiom) | `proofs/idris2/src/Filesystem/Axioms.idr:42` | `believe_me`-backed; registered in `.machine_readable/IDRIS2_AXIOMS.a2ml`; CI-gated via `.github/scripts/check-idris2-believe-me.sh` (Q1-C pilot 2026-06-02 PM) |
| Idris2 | `axBits8EqRefl` (primitive-eq axiom) | `proofs/idris2/src/Filesystem/Axioms.idr:55` | `believe_me`-backed; registered in `.machine_readable/IDRIS2_AXIOMS.a2ml`; CI-gated (same pilot) |
| Idris2 | 15 `?holes` across 4 files (zero `partial` annotations) | `proofs/idris2/src/Filesystem/*.idr` | Type-stated, body un-discharged; classification per issue #119; `equivReflProof` closed via Q1-C pilot |

**Idris2 holes by file (verified by grep against `proofs/idris2/src/Filesystem/*.idr`, 2026-06-02 PM):**

| File | Top-level proof holes | Sub-holes (clause `prf` args) |
|---|---|---|
| `Operations.idr` | 7 (`mkdirRmdirReversibleProof`, `rmdirMkdirReversibleProof`, `touchRmReversibleProof`, `rmTouchReversibleProof`, `writeFileReversibleProof`, `operationIndependenceProof`, `cnoWriteSameContentProof`) | 4 (`?rmdirPrfAfterMkdir`, `?mkdirPrfAfterRmdir`, `?rmPrfAfterTouch`, `?touchPrfAfterRm`) |
| `Composition.idr` | 4 (`sequenceReversibleProof`, `compositionReversibleProof`, `undoRedoIdentityProof`, `undoRedoCompositionProof`) | 0 |
| `Model.idr` | 1 (`equivTransProof`; `equivSymProof` closed via `andCommutative`; `equivReflProof` closed via Q1-C pilot using `Filesystem.Axioms`) | 0 |
| `RMO.idr` | 3 (`overwriteIrreversibleProof`, `hardwareEraseIrreversibleProof`, `auditTrailCompletenessProof`; `appendOnlyAuditLogProof` is closed via `Refl`) | 0 |

Drift from previous PROOF-NEEDS.md tally (22 holes) to current (16 holes) is mechanical: `equivSymProof` and `appendOnlyAuditLogProof` closed silently during the 2026-06-02 morning sweep (visible by grep but the inventory text was not updated). No body changes — this paragraph reconciles the count.

All `partial` markers in `proofs/idris2/src/Filesystem/*.idr` were cleared 2026-06-02 (PRs #108 + #109, closing #89). The total `partial` count is zero.

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
| 2026-06-01 | `single_op_reversible` OpRmdir branch | Closed Qed via `OpMkdirWithPerms` + `OpCreateFileWithPerms` constructor-variant approach (PR #67); zero new axioms |
| 2026-06-02 | Idris2 RMO theorem-shape redesigns | `secureDeleteNotInjective` (closes #60) + `gdprDeletionCompliant` structural redesign (closes #61) via PR #105 |
| 2026-06-02 | Idris2 partial-marker sweep | All 10 `partial` annotations on `RMO.idr` + `Composition.idr` cleared (PRs #108 + #109, closing #89) |
| 2026-06-02 | Idris2 build oracle | `idris-verification.yml` workflow + Justfile recipes shipped (PR #106, closes #70) |
| 2026-06-02 | Idris2 0.8.0 parse fixes | `AuditEntry.proof` keyword-clash rename (PR #112); `hardwareEraseIrreversible` multi-line signature fix (PR #113); `reverseConcat` closed via `Data.List.revAppend` (PR #115) |
| 2026-06-02 PM | Coq admit triumvirate | `mkdir_two_dirs_reversible` restated to LIFO and closed (#56); `overwrite_pass_equalizes_storage` strengthened with `block_overwritten` constraint, closed with zero new axioms (#57); `obliterate_not_injective` threaded through the strengthened lemma + `multi_pass_same_start_same_result`, closed with only standard funext (#58). Coq layer now has **zero `Admitted` markers** (only the justified `Axiom is_empty_dir_dec` remains). |

### What Needs Proving (current, prioritised by tractability × value)

See `docs/PROOF-OPEN-FRONTIER.adoc` for the full Tier-S/A/B/C/D
catalogue. The list below is the **session-2026-06-02 PM** prioritised
attack-list, reconciled against actual file state and ranked against
prior-session findings (memory: `feedback_proven_overly_cautious_owed_pattern`
+ `reference_idris2_0_8_0_reduction_map` indicate that several
ostensibly-tractable holes are blocked on primitive eq-reflexivity).

#### Priority 1 — visible, tractable groundwork (no quick wins)

**Reclassification finding (2026-06-02 PM)**: closer reading of every
remaining hole shows there are **zero** "single-PR closeable" items left
that don't require either (a) primitive-eq groundwork or (b)
theorem-shape redesign. The original Cat-D classification of the 3 RMO
holes was wrong — none of them are sound axiom shapes.

**`cnoWriteSameContent`** (`Operations.idr:254`) — the signature
restate (`equiv` instead of `=`) was already landed in a prior pass.
The body is still blocked by primitive-eq: closure needs reasoning
about `(q == p)` on opaque `Path` values inside `elem`, which Idris2
0.8.0 only reduces on literals.

**3 ostensibly-Cat-D RMO holes are Cat-A non-theorems-as-stated**:
- `overwriteIrreversibleProof` (`RMO.idr:130`): conclusion
  `recovery randomData = Nothing` is refuted by `recovery = Just`.
  Correct shape needs "no UNIVERSAL recovery" — quantifier flip into
  a non-existence claim with an explicit counter-witness.
- `hardwareEraseIrreversibleProof` (`RMO.idr:215`): type
  `HardwareEraseProof -> (Unit -> Filesystem) -> Void` is refuted by
  any non-empty `recovery` (the function exists trivially). Correct
  shape needs the recovery to take the post-erase state as input.
- `auditTrailCompletenessProof` (`RMO.idr:270`): conclusion
  `Elem p (map AuditEntry.path entries)` is refuted by `entries = []`.
  Correct shape needs an "entry was appended" precondition naming the
  insertion event in the log.

These three should be filed as **`#119` sub-issues** with the
non-theorem refutations, in line with the #60 / #61 precedent.

**4 Operations.idr sub-holes** (`?rmdirPrfAfterMkdir`,
`?mkdirPrfAfterRmdir`, `?rmPrfAfterTouch`, `?touchPrfAfterRm`) — same
primitive-eq blocker as the Cat-B set above. Each requires showing
that the post-operation precondition holds, which reduces to
`(p == p) = True` on opaque `Path` — blocked.

#### Priority 2 — primitive-eq groundwork (foundational, owner-decision required)

Every remaining tractable hole reduces to a `(s == s) = True` step on
opaque `String` or `Bits8` — Idris2 0.8.0 only reduces these on
literals. `DecEq Path` does NOT help because it transitively depends
on `DecEq String`, which itself depends on primitive `==`.

Three closure paths, each requiring owner sign-off:

1. **Add `String` / `Bits8` reflexivity axioms** — `axStringEqRefl :
   (s : String) -> (s == s) = True := believe_me Refl`, gated by CI
   allow-list (per the Cat-D `believe_me` pattern). Smallest change,
   but introduces `believe_me` into the proof system which prior
   sessions explicitly avoided.
2. **Migrate `Path` to a structural representation** — replace
   `String`-component paths with `Nat`-encoded interned identifiers.
   `Nat == Nat` IS reducible on opaque values. Bigger migration but
   no `believe_me`.
3. **Reformulate every blocked theorem to use `decEq`-style branches**
   rather than `==`-style booleans. Avoids touching the `Eq` instance
   but ripples through ~20 theorem statements.

Until one path is chosen, the following holes are **frozen**:

- `equivReflProof` (Model.idr:216)
- `equivTransProof` (Model.idr:244)
- `cnoWriteSameContentProof` (Operations.idr:254)
- 4 `?XXXPrfAfter` sub-holes in Operations.idr
- 7 reversibility theorems in Operations.idr (mkdirRmdir, rmdirMkdir,
  touchRm, rmTouch, writeFile, operationIndependence,
  cnoWriteSameContent)

Separately, `undoRedoIdentityProof` and `undoRedoCompositionProof`
need a Cat-A redesign (missing `isReversible op = True` precondition;
provably refuted for non-reversible `op`) before primitive-eq is even
relevant.

#### Priority 3 — Tier-S foundational (research-level)

1. **Lean → Rust mechanised refinement** (F-1) — biggest verification
   gap; today's link is property tests at ~85% confidence. Tractable
   slice: `mkdir` + `rmdir` only, ~1 week.
2. **Crash-consistency for begin/commit/rollback** (F-3) — gated on
   modelling `Filesystem × UndoLog` first.
3. **Concurrency safety** (F-4) — Iris-in-Coq is the strongest match.

#### Priority 4 — Tier-A single-PR proofs from the frontier

These are independent of the proof-hole inventory and can land any time:

- Glob expansion termination + complexity bound (A-6)
- Pratt-style short-circuit `&&`/`||` precedence proof (A-8)
- Quote-context preservation matrix (A-11)
- Path traversal containment lemma (A-12, regression-guard for the
  2026-02-12 audit fix)
- Pipe associativity property test → Lean lemma (A-9)

#### Priority 5 — Tier-B multi-day

POSIX-2024 per-M-feature (B-1), Subshell scoping (B-2), Word splitting
under quote-context (B-3), Pipeline data-flow (B-4), Job-control state
machine (B-5), Symlink-loop detection (B-6), Audit-log HMAC (B-7),
MCP-response conformance (B-8).

#### Priority 6 — Tier-C marginal-but-named

Ten items in `docs/PROOF-OPEN-FRONTIER.adoc§Tier-C`. Each is minutes to
state and seconds to check; cumulative effect is a much harder system
to regress.

#### Priority 7 — Tier-D tooling

`Print Assumptions` CI guard (D-1, load-bearing — without it any
re-introduced admit is silent drift), Idris2 `--check-hole` CI (D-2),
cross-system theorem-name alignment (D-3), proof-narrative
auto-generation (D-4), witness-coverage compile-time test (D-5).

### Recommended Provers

- **Coq** — primary truth source for filesystem model
- **Lean 4** — canonical RMO proofs (`obliterate_not_injective` chain)
- **Agda** — minimum-axiom witness (eliminate funext via cubical)
- **Idris2** — ABI-level type expression (per estate convention `Zig=APIs+FFIs, Idris2=ABIs`)
- **Isabelle/HOL** — Sledgehammer cross-validation
- **Mizar** — set-theoretic third opinion
- **Z3 SMT** — counterexample search for non-existent recovery functions

### Priority Summary

**HIGH (closeable now)** — Idris2 Cat-A redesigns (`cnoWriteSameContentProof`)
+ Cat-D axiomatic markers (3 RMO physical claims) — both are
single-PR.

**MEDIUM (needs infrastructure)** — the 4 ostensibly-Cat-B holes
(equivRefl/Trans + undoRedoIdentity/Composition) are blocked on
primitive-eq reflexivity OR theorem-shape redesign. Closure needs (a)
a `Path`-equality reflexivity lemma + threading, or (b) a model
migration sidestepping primitive `==`. Filing under #119 reclassified.

**LOW BUT BLOCKING THE BIG CLAIMS** — Lean→Rust mechanised refinement,
crash-consistency under WAL/undo-log model, concurrency safety. These
are research-level work; the bigger frontier is real.

`secureDeleteNotInjective` (closes #60) and `gdprDeletionCompliant`
(closes #61) shipped 2026-06-02 via PR #105 with corrected theorem
shapes (the prior holes had non-theorem signatures refutable by
`recovery = id` / `recovery = const empty`). The MAA/GDPR claims now
rest on these closed theorems plus `?overwriteIrreversibleProof`
(still open as Cat-D placeholder) and axiomatic NIST SP 800-88 /
Shannon-entropy / physical-world assumptions which should be made
explicit (see narrative §10).

The three Coq admits (#56 / #57 / #58) closed in the 2026-06-02 PM
session bring the Coq layer to **zero `Admitted` markers** — only the
single justified `Axiom is_empty_dir_dec` remains. `obliterate_not_injective`
— the formal grounding for the "mathematically irreversible secure
deletion" marketing claim — is now soundly proven (under the
strengthened `block_overwritten`-aware geometry hypothesis, which is
trivially satisfied for first-time obliteration).
