<!--
SPDX-License-Identifier: CC-BY-SA-4.0
Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
-->
# Verification Status & Honest Limits

This is the single honest-status page the rest of the wiki links to. It
summarises what is proven, what is merely tested, and what is not built. For the
authoritative, machine-checked accounting see
[`docs/PROOF_HOLES_AUDIT.md`](https://github.com/hyperpolymath/valence-shell/blob/main/docs/PROOF_HOLES_AUDIT.md)
and the deep-audit log in
[`docs/audits/`](https://github.com/hyperpolymath/valence-shell/tree/main/docs/audits).

**Bottom line:** Valence Shell is **v0.9.0, an advanced research prototype (~78%
of the roadmap), NOT production-ready.**

---

## The three trust levels

Valence Shell's claims live at three very different levels of assurance. Keeping
them apart is the whole point.

| Level | What it covers | Assurance | Status |
|-------|----------------|-----------|--------|
| **1. The proofs** | Abstract mathematical model of filesystem operations | Machine-checked, reproducible offline, in 6 systems | ✅ Solid |
| **2. Proof ⇄ code correspondence** | That the running Rust matches the proven model | **Property-tested, ~85% confidence** | ⚠️ Not mechanically proven — the v1.0.0 blocker |
| **3. POSIX / OS reality** | Real syscalls, real kernel, concurrency, crashes | Kernel guarantees only | ⚠️ Outside the proofs |

The gap between level 1 and level 2 is the honest heart of the project. The math
is proven; wiring it irrefutably to the code is the remaining research problem.

## What IS guaranteed (by proof)

- If preconditions hold, `rmdir(mkdir(p, fs)) = fs`.
- If preconditions hold, `write(p, old, write(p, new, fs)) = fs`.
- Operations on distinct paths don't interfere.
- Composition: sequences of reversible operations reverse correctly.
- ~478 theorem candidates across 6 systems + the Idris2 ABI layer.

## What is NOT guaranteed

- That the implementation matches the proofs (manual review + property tests only).
- POSIX behaviour beyond the modeled operations.
- Performance (not optimized or benchmarked in CI).
- Correctness under concurrent multi-process access.
- Filesystem integrity after crashes.

## Open proof holes (as of the latest audit)

**0 real gaps.** Re-verified 2026-07-16 with `coqc` + `Print Assumptions` under
Coq 8.18.0: the full Coq tree compiles with zero `admit`/`Admitted`/`Axiom`
markers, and the load-bearing theorems are *Closed under the global context* or
depend only on standard `functional_extensionality`. The two remaining items are
standard/justified axioms, not gaps:

| Item | System | Nature |
|------|--------|--------|
| `obliterate_overwrites_all_blocks` | Coq | **CLOSED** (was the one real gap) — *Closed under the global context* |
| `is_empty_dir_dec` | Coq | Justified axiom (infinite-domain decidability) |
| `funext` | Agda | Structural axiom (function extensionality; standard in intensional type theory) |

The **Idris2 ABI layer is hole-free** (builds under `--total`, closed via issue
#151 / PR #152), with 2 registered primitive-equality axioms (`axStringEqRefl`,
`axBits8EqRefl`) gated by `.github/scripts/check-idris2-believe-me.sh`.

## Feature reality check

| Capability | Status |
|-----------|--------|
| Reversible ops (**RMR**): undo/redo, checkpoint/restore, transactions | ✅ Working & proven |
| Interactive shell surface (pipelines, redirs, glob, control structures, jobs, variables) | ✅ Working |
| Secure deletion (**RMO** / `obliterate`) | ⚠️ Implemented & wired (3-pass overwrite + unlink + audit residue); best-effort on in-place FS only (CoW/SSD need HW erase); not a full GDPR framework |
| Full POSIX compliance | ⚠️ Subset only (no external-arg word-splitting, subshells, `~user`) |
| Mechanized Lean → Rust correspondence | ⚠️ Differential oracle vs compiled proven model (`just test-correspondence-model`); full refinement proof still the v1.0.0 blocker |

## Test posture

- **736 tests passing, 0 failures, 14 ignored** (`cargo test` in `impl/rust-cli/`).
- 7 `cargo-fuzz` targets, run in CI via ClusterFuzzLite (address sanitizer).
- Property-based correspondence tests against the Lean model.

## How to check any of this yourself

```bash
# The tests
cd impl/rust-cli && cargo test

# The proofs (reproducible, offline)
just verify-proofs
```

If a claim in this repository doesn't reproduce, that's a bug — please
[file an issue](https://github.com/hyperpolymath/valence-shell/issues) tagged
`docs` and cite the reality (`cargo test` output, prover version, etc.).

---

## Where to go next

- Back to the [Wiki Home](Home)
- The reasoning behind the design → [`EXPLAINME.adoc`](https://github.com/hyperpolymath/valence-shell/blob/main/EXPLAINME.adoc)
