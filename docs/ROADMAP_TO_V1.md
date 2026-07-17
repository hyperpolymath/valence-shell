<!--
SPDX-License-Identifier: CC-BY-SA-4.0
Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
-->
# Valence Shell: Production Charter (Roadmap to v1.0.0)

**Current version**: 0.9.0 (advanced research prototype, ~78% complete)
**Target**: v1.0.0 — definition pending owner decision D1 (below)
**Charter date**: 2026-07-07 (supersedes the 2026-01-29 roadmap, which was
written against v0.10-era plans; roughly half its milestones have since
shipped and its claims were not audit-verified)

This charter is the working plan for an **orchestrated multi-agent project**:
one coordinating session manages parallel worker lanes, with a fan-in review
at the end of every phase. It is honest by construction — see `CLAUDE.md`
"HONEST STATUS" and `docs/PROOF_HOLES_AUDIT.md` for the ground truth this
plan builds on.

---

## Where we are (audit-verified, 2026-07-07)

- 736 tests passing, 0 failures (see CLAUDE.md test table)
- 2 proof holes, **0 real gaps**: the Coq `obliterate_overwrites_all_blocks`
  gap is CLOSED (re-verified 2026-07-16, *Closed under the global context*);
  2 documented axioms remain; Idris2 ABI layer fully closed
- Lean→Rust correspondence is **tested, not mechanized** (~85–95% confidence)
- Not a full POSIX shell: word splitting in external args, `~user`,
  subshell `(...)`, SIGCHLD/Ctrl+Z incomplete (`docs/POSIX_COMPLIANCE.md`)
- RMO `obliterate` implemented + wired (best-effort overwrite + unlink + audit residue); full GDPR not yet shippable (HW erase for CoW/SSD, HMAC signing pending)
- Backlog is decomposed fan-out-ready in Tier-S issues:
  #41→(#86,#87,#88) seams, #42→(#76–#81) proofs, #43→(#82–#85) tests,
  #45→(#63–#66, #90–#94) theory frontiers

---

## Pending owner decisions (phase gates)

These block the phases that depend on them. Recommendations are provisional
defaults — vetoable, not ratified by merging this document.

| # | Decision | Options | Provisional recommendation |
|---|----------|---------|---------------------------|
| **D1** | What "production" / v1.0.0 means | (a) daily-drivable POSIX shell; (b) verified artifact with honest POSIX deltas; (c) both | (b) gates v1.0; (a) at "scripts run, deltas documented" |
| **D2** | Correspondence approach (#93) | (i) hardened tested-correspondence for v1.0; (ii) verified-kernel architecture; (iii) full extraction pipeline | (i) for v1.0, (ii) chartered for v2.0. Cost ≈ 1× / 10× / unbounded |
| **D3** | 47/58 commits authored `Test <test@example.com>` | history rewrite + force-push (estate-forbidden) vs `.mailmap` + documentation | `.mailmap` + document; force-push only on explicit owner sanction |
| **D4** | RMO/GDPR scope for v1.0 (#92) | best-effort overwrite + proven audit residue + documented hardware boundary (per #66/#130) vs drop GDPR claims from v1.0 | the former — honest and matches the RMR/RMO bridge distinction |
| **D5** | Orchestration budget & cadence | parallel-lane count, token appetite per phase, scheduled loops vs kicked-off sessions | owner call; phases below assume 3–5 concurrent lanes |

---

## Workstream lanes

| Lane | Scope | Issues | Orchestration profile |
|------|-------|--------|----------------------|
| **A** | POSIX completeness: word splitting (quote-context threading), subshell `(...)`, `~user`, SIGCHLD/Ctrl+Z | #91, #94 | Keystone — one sustained agent; word splitting first |
| **B** | Seam sealing: 3 prod `panic!`, 10 `unreachable!`, 28 TODOs | #86, #87, #88 | Pure fan-out, one PR per file |
| **C** | Test/fuzz/bench expansion: 736→2000+ tests, 7→20 fuzz targets, 15→75 security tests, benches in CI | #82–#85 | Pure fan-out by category |
| **D** | Proof expansion: 478 theorem candidates across 6 systems; ~~close last Coq gap~~ (DONE — closed + re-verified 2026-07-16); restate #130 non-theorem | #76–#81, #130 | Fan-out by prover system |
| **E** | Lean→Rust correspondence mechanization | #93 | Keystone — blocked on **D2** |
| **F** | RMO/GDPR implementation (theory unblocked: #60/#61 closed) | #92 | Blocked on **D4**, then bounded single lane |
| **G** | Ops hygiene: CI reds, charter, issue-state drift | — | Inline, done first |

## Phases

**Phase 0 — hygiene + decisions** *(in progress)*
Fix ECHIDNA red (isabelle not in noble) and Secret Scanner startup_failure
(caller-side permissions); update #92 blocked-status; land this charter;
obtain D1–D5.

**Phase 1 — confidence floor** *(needs D5 only)*
Lanes B + C fanned out wide (low-risk, mechanical verification), while one
agent takes Lane A's word-splitting keystone. Exit: seams sealed, test count
materially up, word splitting merged. Fan-in review closes the phase.

**Phase 2 — verification core** *(needs D2)*
Lane D fan-out by prover + Lane E keystone per the D2 choice. Exit: 0 real
proof holes, foundation-pack theorems across all six systems, correspondence
story at its D2-ratified strength.

**Phase 3 — production hardening** *(needs D1, D4)*
Lane F (RMO per D4) + release engineering: 24h fuzz soak, leak checks,
perf gates in CI, user docs, `.mailmap` per D3, release notes. Exit:
v1.0.0 tag per the D1 definition.

Every fan-out phase ends with an explicit fan-in review before the next
phase opens — no orphaned parallel work.

---

## Quality gates for v1.0.0 (carried from prior roadmap, still valid)

- 100% of tests passing; no known critical bugs
- Fuzzing: 24+ hours without crashes; no resource leaks
- All reversible operations proven across the six proof systems
- Correspondence at D2-ratified strength, stated honestly in docs
- Zero known security vulnerabilities; security test suite ≥75 cases
- Documentation: user guide, proof reference, MAA guide, man page

## Non-goals for v1.0 (unless D1 says otherwise)

- Full bash/zsh replacement parity
- Windows job control / FIFOs
- BEAM daemon, Elixir NIF revival
- Hardware-level erasure guarantees (non-theorems per #66/#130 — the
  documented modelling boundary stands)

---

**Status**: Charter pending owner ratification of D1–D5.
**History**: v1 of this file (2026-01-29) is preserved in git history; it
described Phase 6–9 milestones M7–M20, of which M7–M13 and much of M16
have since shipped.
