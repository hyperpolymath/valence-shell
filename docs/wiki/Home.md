<!--
SPDX-License-Identifier: CC-BY-SA-4.0
Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
-->
# Valence Shell Wiki

**A shell you can prove things about — with a mathematically-guaranteed undo button.**

Valence Shell (`vsh`) is an interactive Unix-style shell whose core filesystem
operations are backed by machine-checked mathematical proofs across six
independent proof systems. Where an ordinary shell *hopes* that undo works,
Valence Shell *proves* it.

> **Status — please read before quoting us.**
> Valence Shell is **v0.9.0, an advanced research prototype (~78% of the roadmap complete). It is NOT production-ready.** The shell runs, is
> extensively tested (736 tests passing, 0 failures), and the reversibility
> proofs are real. What is *not* finished is the mechanically-verified link
> between the proofs and the running Rust code (today that link is
> property-tested, ~85% confidence), and the GDPR secure-deletion features are
> still stubs. Do not use it as your daily login shell. Full honesty page:
> [Verification Status & Honest Limits](Verification-Status).

---

## Start here — who are you?

Pick the track that fits. Each one is self-contained and links back to the
canonical files in the repository.

| If you are… | Go to | You'll get |
|-------------|-------|------------|
| 🧑‍🌾 **Curious, non-technical** — you heard "a shell you can prove things about" and want to know what that *means* | **[For Lay People](For-Lay-People)** | A plain-language explanation, no jargon, real-world analogies |
| 💻 **A user** — you want to install it and drive the shell | **[For Users](For-Users)** | Install, first run, everyday commands, undo/redo, checkpoints |
| 🛠️ **A developer** — you want to build it, read the proofs, or contribute | **[For Developers](For-Developers)** | Toolchain, build/test, the six proof systems, contribution rules |
| 📦 **A platform maintainer** — you package or deploy software for others | **[For Platform Maintainers](For-Platform-Maintainers)** | Dependencies, packaging (Guix/Nix/container), supply-chain notes |
| 📰 **A marketer or journalist** — you're writing about the project | **[For Marketers & Journalists](For-Marketers-and-Journalists)** | Accurate one-liners, what you *may* and *may not* claim, fact-check contacts |

---

## The one-paragraph version

Every shell exposes filesystem primitives — `mkdir`, `rmdir`, `cp`, `mv`,
`ln -s`, file read/write — and every shell simply *assumes* they behave: that
`rmdir` undoes `mkdir`, that `cp` doesn't destroy the original. Valence Shell
turns those assumptions into **theorems** and proves them in six different
mathematical systems (Coq, Lean 4, Agda, Isabelle/HOL, Mizar, and the Z3 SMT
solver). Because the proofs are reproducible on your own machine — offline, if
you like — you don't have to take our word for anything. This is the same
"prove it, don't test-and-hope" discipline used by the seL4 verified kernel
and the CompCert verified C compiler.

## The MAA framework

The deeper idea behind Valence Shell is **MAA — Mutually Assured
Accountability**. Every filesystem action falls into one of two provable
categories:

- **RMR — Remove-Match-Reverse.** The operation is *reversible*: there is a
  proven inverse that restores the exact prior state. This is what powers
  undo/redo, checkpoints, and transactions. **Status: working and proven.**
- **RMO — Remove-Match-Obliterate.** The operation *provably destroys*
  information (e.g. GDPR "right to be forgotten"), and the proof is what lets a
  third party trust the deletion happened. **Status: proven in the model,
  stubbed in the runtime — not yet usable.**

"Mutually assured" means both the user *and* an independent auditor hold
machine-checkable evidence. Nobody can tell a different story than the proofs
allow.

---

## Quick links

- **Repository:** <https://github.com/hyperpolymath/valence-shell>
- **Primary development (GitLab mirror):** <https://gitlab.com/non-initiate/rhodinised/vsh>
- **FAQ:** [`FAQ.adoc`](https://github.com/hyperpolymath/valence-shell/blob/main/FAQ.adoc)
- **Show-me-the-receipts (claims vs. evidence):** [`EXPLAINME.adoc`](https://github.com/hyperpolymath/valence-shell/blob/main/EXPLAINME.adoc)
- **Honest proof-hole accounting:** [`docs/PROOF_HOLES_AUDIT.md`](https://github.com/hyperpolymath/valence-shell/blob/main/docs/PROOF_HOLES_AUDIT.md)
- **License:** MPL-2.0

---

<sub>This wiki is maintained in-repository under `docs/wiki/` and mirrored to the
GitHub wiki — see [`docs/wiki/README.md`](https://github.com/hyperpolymath/valence-shell/blob/main/docs/wiki/README.md)
for how the two stay in sync. Prose is CC-BY-SA-4.0.</sub>
