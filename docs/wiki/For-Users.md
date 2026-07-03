<!--
SPDX-License-Identifier: CC-BY-SA-4.0
Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
-->
# For Users

You want to install Valence Shell and drive it. This page is the map; the
detailed canonical guides live in the repository and are linked throughout.

> **Reality check:** Valence Shell is a **research prototype (v0.9.0), not
> production-ready.** It is a great deal of fun to explore and genuinely useful
> for learning about reversible, verified computing — but do **not** make it your
> login shell or trust it with irreplaceable data. See
> [Verification Status](Verification-Status).

---

## Install & run (the short path)

The interactive shell is the Rust CLI in `impl/rust-cli/`. It needs only a Rust
toolchain (1.88+); the six proof systems are **optional** and only needed if you
want to re-check the proofs yourself.

```bash
git clone https://github.com/hyperpolymath/valence-shell.git
cd valence-shell/impl/rust-cli

cargo build --release            # builds the `vsh` binary
cargo run                        # start the interactive shell
./target/release/vsh --version   # or run the release binary directly
```

Canonical, longer install guide (containers, portable install, self-diagnostics):
[`QUICKSTART-USER.adoc`](https://github.com/hyperpolymath/valence-shell/blob/main/QUICKSTART-USER.adoc).

## What you can do with it

Valence Shell behaves like a familiar Unix shell, plus a proven undo/redo layer.
Working features in v0.9.0 include:

- **Everyday shell surface:** pipelines (`a | b | c`), redirections
  (`>`, `>>`, `<`, `2>`, `&>`, `2>&1`), globbing (`*.txt`, `[a-z]*`, `{1,2,3}`),
  quoting, arithmetic (`$((expr))`), here-docs/here-strings, command & process
  substitution.
- **Control structures:** `if/elif/else`, `while`, `for`, `case`, `test`/`[`,
  `[[ ]]`, `&&`/`||` short-circuiting.
- **Variables & jobs:** `$VAR`/`${VAR}`/`export`, background jobs (`&`, `bg`,
  `fg`, `jobs`, `kill`).
- **The reversibility superpowers:**
  - `undo` / `redo` — proven reversal of filesystem operations.
  - `checkpoint <name>` / `restore <name>` — named snapshots with proof
    certificates.
  - `diff` — compare state between checkpoints or against the current state.
  - `explain` — a **proof-annotated dry run**: see what a command *would* do and
    the theorem that guarantees it's reversible.
  - `replay` — animated history with proof narration.
  - `begin` / `commit` / `rollback` — transaction grouping.
- **Friendly touches:** zsh-style "did you mean?" correction, syntax
  highlighting, smart paging, 3-tier help.

Full walkthrough: [`docs/USER_GUIDE.md`](https://github.com/hyperpolymath/valence-shell/blob/main/docs/USER_GUIDE.md)
and worked examples in
[`docs/COMPREHENSIVE_EXAMPLES.md`](https://github.com/hyperpolymath/valence-shell/blob/main/docs/COMPREHENSIVE_EXAMPLES.md).

## What does *not* work yet (so you're not surprised)

- It is **not a full POSIX/bash replacement.** Word-splitting in external command
  arguments, full subshell `(...)` syntax, and `~user` tilde expansion are not
  implemented.
- **Secure deletion / GDPR (`obliterate`)** is a stub — designed and proven in
  the model, but not usable in the runtime.
- The proof-to-code correspondence is **property-tested (~85% confidence)**, not
  mechanically proven.

The authoritative "not implemented" list:
[`UNIMPLEMENTED_FEATURES.md`](https://github.com/hyperpolymath/valence-shell/blob/main/UNIMPLEMENTED_FEATURES.md)
and [`docs/POSIX_COMPLIANCE.md`](https://github.com/hyperpolymath/valence-shell/blob/main/docs/POSIX_COMPLIANCE.md).

## Getting help

- Built-in help: run `help` inside the shell, or `vsh --help`.
- Common questions: the [FAQ](https://github.com/hyperpolymath/valence-shell/blob/main/FAQ.adoc).
- Found a bug? File an issue: <https://github.com/hyperpolymath/valence-shell/issues>.

---

## Where to go next

- New to the whole idea? → [For Lay People](For-Lay-People)
- Want to build it or read the proofs? → [For Developers](For-Developers)
- Packaging it for others? → [For Platform Maintainers](For-Platform-Maintainers)
