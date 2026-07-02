<!--
SPDX-License-Identifier: CC-BY-SA-4.0
Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
-->
# For Platform Maintainers

You package, distribute, or deploy software for other people. This page
summarises what you need; the canonical guide is
[`QUICKSTART-MAINTAINER.adoc`](https://github.com/hyperpolymath/valence-shell/blob/main/QUICKSTART-MAINTAINER.adoc).

> **Before you package:** Valence Shell is **v0.9.0, a research prototype, not
> production-ready.** If you ship it, label it as such downstream. See
> [Verification Status](Verification-Status).

---

## What actually ships

The primary artifact is a single self-contained binary — the `vsh` shell — built
from `impl/rust-cli/`. The proof systems are **build/verification-time only**;
they are not runtime dependencies of the shell.

| Artifact | Built from | Notes |
|----------|-----------|-------|
| `vsh` CLI binary | `impl/rust-cli/` | The primary deliverable |
| `libvalence_shell.{so,a}` | `ffi/zig/` | C-ABI FFI library (optional) |
| `valence_shell.h` | `ffi/zig/include/` | Hand-maintained C header for the FFI |

## Dependencies

**Runtime:**

- `glibc` ≥ 2.34 (or `musl` ≥ 1.2 for static builds).
- *Optional:* `libleanshared.so` — only if the Lean-extraction FFI feature is enabled.
- *Optional:* Erlang/OTP ≥ 26 — only for the Elixir NIF daemon / MCP server features.

**Build-time (not needed at runtime):**

- Rust ≥ 1.88 for the CLI.
- Zig ≥ 0.13 for the FFI library.
- The proof assistants (Coq/Lean/Agda/Isabelle/Mizar/Z3) only if you re-verify
  proofs at package time; if CI has already verified them, packaging does not
  require them.

## Packaging paths

```bash
# Guix (preferred)
guix build -f guix.scm

# Nix (fallback)
nix build

# Container (Containerfile per repo policy — not Dockerfile)
podman build -t valence-shell .

# Manual prefix install
just install --prefix=/usr/local
```

Config resolves to `$XDG_CONFIG_HOME/valence-shell/config.toml`
(fallback `$HOME/.config/valence-shell/config.toml`).

## Supply-chain & security posture

- **License:** MPL-2.0. Third-party notices in
  [`THIRD_PARTY_NOTICES.md`](https://github.com/hyperpolymath/valence-shell/blob/main/THIRD_PARTY_NOTICES.md).
- **Dependencies are SHA-pinned**; GitHub Actions are pinned to commit SHAs.
- **OpenSSF Scorecard** runs in CI (`.github/workflows/scorecard.yml`) with
  least-privilege job permissions.
- **Continuous fuzzing** via ClusterFuzzLite (`.clusterfuzzlite/`).
- **Secret scanning** (TruffleHog) and CodeQL are wired into CI.
- **Responsible disclosure:** [`.well-known/security.txt`](https://github.com/hyperpolymath/valence-shell/blob/main/.well-known/security.txt)
  (RFC 9116) and [`SECURITY.md`](https://github.com/hyperpolymath/valence-shell/blob/main/SECURITY.md).

## Health checks

```bash
just doctor            # full diagnostic
vsh --version          # version check
```

## Multi-instance deployment

Each instance can carry isolated config/data/logs:

```bash
just install --prefix=/opt/vsh-instance1 --config=/etc/valence-shell/instance1.toml
just install --prefix=/opt/vsh-instance2 --config=/etc/valence-shell/instance2.toml
```

## Reporting issues

- Upstream issues: <https://github.com/hyperpolymath/valence-shell/issues>
- With a pre-filled diagnostic: `just help-me`

---

## Where to go next

- Build internals & proofs → [For Developers](For-Developers)
- Honest limits to relay downstream → [Verification Status](Verification-Status)
