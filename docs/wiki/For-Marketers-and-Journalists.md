<!--
SPDX-License-Identifier: CC-BY-SA-4.0
Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
-->
# For Marketers & Journalists — Press & Accuracy Kit

This page exists so that anyone writing about Valence Shell can be **accurate
and quotable without over-claiming.** The project's single most important
reputational asset is its honesty about what is and isn't proven. Please help us
protect it.

**Golden rule:** when in doubt, under-claim. Everything below is checkable
against the source repository, and we would much rather be described as "an
honest research prototype" than as anything we can't yet back up.

---

## The project in one line (pick by length)

- **Twitter-length:** *Valence Shell is a Unix shell whose core operations are
  backed by machine-checked mathematical proofs — a shell with a provable undo
  button. (Research prototype, not production-ready.)*
- **One sentence:** *Valence Shell (`vsh`) is an interactive command-line shell
  whose fundamental filesystem operations are formally verified across six
  independent proof systems, giving mathematically-proven reversibility (undo/redo)
  — currently an advanced research prototype, not for production use.*
- **Paragraph:** see [the wiki home page](Home).

## Accurate facts you can quote (all verifiable)

| Claim | Where to verify |
|-------|-----------------|
| Version **0.9.0**, an **advanced research prototype**, ~**78%** of its roadmap complete | `impl/rust-cli/Cargo.toml`, `README.adoc`, `CHANGELOG.adoc` |
| **NOT production-ready** (the project says so itself) | `README.adoc`, `FAQ.adoc`, `CLAUDE.md` |
| **736 tests passing, 0 failures** (14 slow tests ignored by default) | `cargo test` in `impl/rust-cli/` |
| Proofs span **6 independent proof systems** (Coq, Lean 4, Agda, Isabelle/HOL, Mizar, Z3) plus an Idris2 ABI layer | `proofs/` directory |
| **~478 theorem candidates** across those systems | `docs/audits/2026-06-01-deep-audit.adoc` |
| Reversibility (**RMR**) is **proven and working** in the shell | `proofs/`, and `explain`/`checkpoint`/`undo` in the running CLI |
| Proofs are **reproducible offline** by anyone | `just verify-proofs` |
| Licensed **MPL-2.0** | `LICENSE` |
| Same "prove-it, don't-just-test-it" lineage as **seL4** and **CompCert** | industry-standard comparison, cited in `README.adoc` |

## Claims you may make ✅ vs. claims to avoid ❌

This is the heart of this page. Please read it before publishing.

| ✅ Accurate | ❌ Inaccurate / premature |
|-------------|---------------------------|
| "A shell with **formally proven** reversible operations." | "A **fully verified** shell." (The proof-to-code link isn't mechanically verified yet.) |
| "Reversibility is **proven in the mathematical model**." | "Every line of the program is **proven correct**." |
| "**Property-tested** correspondence between proofs and code (~85% confidence)." | "The Rust code is **proven** to match the proofs." (This is the explicit v1.0.0 blocker, not yet done.) |
| "**Designed** for GDPR-style provable secure deletion." | "**GDPR-compliant** secure deletion." (RMO is a stub; not implemented.) |
| "An **advanced research prototype**." | "**Production-ready** / enterprise-ready / ready to ship." |
| "Proven for its **modeled filesystem operations**." | "A **full POSIX / bash replacement**." (POSIX coverage is a subset.) |
| "**Six proof systems** cross-validate the same theorems." | "**Impossible to have bugs.**" (Proofs cover the model, not the whole stack.) |
| "Algorithmic reversibility: `undo(do(x)) = x`." | "**Thermodynamically** reversible / zero-energy computing." (Different, unclaimed thing.) |

## The single most important nuance

There are **two different things** that could be called "verified", and conflating
them is the most common mistake:

1. **The proofs** — mathematical theorems about an *abstract model* of a
   filesystem. These are **done and reproducible**. ✅
2. **The connection** between those proofs and the *actual Rust program that
   runs*. This is currently established by **extensive testing (~85% confidence),
   not by an end-to-end mechanical proof.** This gap is the explicit thing
   standing between v0.9.0 and a future v1.0.0. ⚠️

A fair, accurate framing: **"The math is proven; wiring the math irrefutably to
the running code is the remaining research problem the project is honest about."**

## Why it's newsworthy (the honest angle)

- **Formal verification is usually reserved for kernels, compilers, and
  aerospace.** Applying that discipline to something as everyday as a *shell* is
  an unusual and pedagogically vivid choice.
- **Radical honesty as an engineering value.** The project ships its own
  "here's exactly what isn't finished" audit (`docs/PROOF_HOLES_AUDIT.md`) and
  refused to inflate its own status — an interesting counter-story to typical
  software hype.
- **The GDPR / "right to be forgotten" angle.** The deeper research question —
  *can you mathematically prove to a regulator that data was truly destroyed?* —
  is genuinely important, even though that feature isn't built yet.
- **Reproducibility.** Readers can re-run the proofs themselves, offline. That's
  a rare thing to be able to say to an audience.

## Suggested attributed quote

> "Ordinary shells assume their own undo button works. We wanted one where you
> don't have to assume — where the reversibility is a theorem you can check
> yourself. We're not production-ready, and we say so loudly; the interesting
> work is exactly in the honesty about what's proven and what isn't."
> — *Valence Shell project*

(If you need a named, on-the-record human quote, use the fact-check contact
below rather than attributing an invented spokesperson.)

## Visual / demo suggestions

- The `explain` command performs a **proof-annotated dry run** — good for a
  screenshot showing a command alongside the theorem that justifies its
  reversibility.
- `checkpoint` / `restore` and `replay` (animated history) demonstrate the
  reversibility story visually.
- The `proofs/` directory re-compiling under `just verify-proofs` makes the
  "check it yourself" point concretely.

## Fact-checking & contact

**Please fact-check before publishing.** The maintainers would genuinely rather
answer a question than correct a story.

- **Maintainers:** see [`MAINTAINERS.adoc`](https://github.com/hyperpolymath/valence-shell/blob/main/MAINTAINERS.adoc)
- **Security / responsible disclosure:** [`.well-known/security.txt`](https://github.com/hyperpolymath/valence-shell/blob/main/.well-known/security.txt) and [`SECURITY.md`](https://github.com/hyperpolymath/valence-shell/blob/main/SECURITY.md)
- **Repository (canonical mirror):** <https://github.com/hyperpolymath/valence-shell>
- **Primary development:** <https://gitlab.com/non-initiate/rhodinised/vsh>
- **Open an accuracy question:** file an issue tagged `docs` on the repository.

## Boilerplate (copy-paste)

> **Valence Shell (`vsh`)** is an open-source, formally-verified interactive
> shell. Its core filesystem operations are backed by machine-checked proofs of
> reversibility across six independent proof systems, letting users mathematically
> verify — offline — that operations can be undone. Valence Shell is an advanced
> research prototype (v0.9.0), is not production-ready, and is released under the
> MPL-2.0 license.

---

## Where to go next

- The honest limits, in full → [Verification Status](Verification-Status)
- The plain-language explainer → [For Lay People](For-Lay-People)
- The technical claims-vs-evidence file → [`EXPLAINME.adoc`](https://github.com/hyperpolymath/valence-shell/blob/main/EXPLAINME.adoc)
