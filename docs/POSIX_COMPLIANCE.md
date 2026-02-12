# SPDX-License-Identifier: PMPL-1.0-or-later
# POSIX Compliance Status - Valence Shell (v0.9.0)

**Goal**: Full POSIX shell compliance with formal verification at each increment

**Current Status**: Milestones 1-8 substantially complete; Milestones 9-14 not started

**Last Updated**: 2026-02-12 (Opus audit — rewritten from scratch)

---

## Milestone Status Overview

| # | Milestone | Status | Notes |
|---|-----------|--------|-------|
| 1 | Simple Command Execution | **Complete** | PATH lookup, args, exit status |
| 2 | Redirections | **Mostly complete** | `2>&1` is a no-op (TODO) |
| 3 | Pipelines | **Complete** | Multi-stage, exit code from last |
| 4 | Variables | **Complete** | Scalars, arrays, parameter expansion |
| 5 | Glob Expansion | **Complete** | POSIX-compliant + brace expansion |
| 6 | Quote Processing | **Complete** | Single, double, backslash |
| 7 | Command Substitution | **Complete** | `$(cmd)` and backticks |
| 8 | Arithmetic | **Complete** | Full operator set including `**` |
| 9 | Control Structures | **Not started** | Biggest gap — blocks all scripts |
| 10 | Job Control | **Partial** | No SIGCHLD, no Ctrl+Z |
| 11 | Shell Builtins | **Partial** | 20 implemented, ~25 missing |
| 12 | Functions | **Not started** | No `func() { ... }` syntax |
| 13 | Shell Scripts | **Not started** | No `.sh` file execution |
| 14 | Advanced Features | **Partial** | Here docs, process sub, arrays done |

---

## Detailed Feature Status

### Milestone 1: Simple Command Execution — COMPLETE

| Feature | Status | Implementation |
|---------|--------|---------------|
| Command parser with AST | Done | `parser.rs` (~2500 lines), 25+ Command variants |
| External program execution | Done | `external.rs`, PATH lookup via `which` crate |
| Argument passing | Done | Variable expansion in args |
| Exit status handling | Done | `$?` tracked in ShellState |
| PATH lookup | Done | Searches PATH directories |

### Milestone 2: Redirections — MOSTLY COMPLETE

| Feature | Status | Implementation |
|---------|--------|---------------|
| Output redirect `>` | Done | `File::create()` in `external.rs` |
| Append redirect `>>` | Done | `OpenOptions::append()` (fixed 2026-02-12) |
| Input redirect `<` | Done | `File::open()` |
| Error redirect `2>` | Done | Token-start-only detection (fixed 2026-02-12) |
| Error append `2>>` | Done | `OpenOptions::append()` |
| Both redirect `&>` | Done | Cloned file handle for stdout+stderr |
| `2>&1` fd duplication | Done | Tracks stdout file handle for `try_clone()` (fixed 2026-02-12) |
| Here documents `<<DELIM` | Done | Tab stripping, quoted delimiters, expansion |
| Here strings `<<<word` | Done | Trailing newline added |
| Undo tracking for redirections | Done | `redirection.rs` tracks file modifications |

**Known issues**:
- ~~`2>&1` does nothing~~ — **Fixed** (2026-02-12, tracks stdout file handle)
- Heredoc/herestring temp files in `/tmp/` are never cleaned up
- Temp file names are predictable (symlink attack risk)

### Milestone 3: Pipelines — COMPLETE

| Feature | Status | Implementation |
|---------|--------|---------------|
| Pipe operator `\|` | Done | `Command::Pipeline` variant |
| Multi-stage pipes | Done | `execute_pipeline()` chains stdio |
| Exit code from last stage | Done | POSIX behavior |
| Process spawning | Done | `std::process::Command` |

**Known issues**:
- SIGINT during pipeline only kills current child; others may leak

### Milestone 4: Variables — COMPLETE

| Feature | Status | Implementation |
|---------|--------|---------------|
| Assignment `VAR=value` | Done | `Command::Assignment` |
| Expansion `$VAR`, `${VAR}` | Done | `expand_variables()` in `parser.rs` |
| `export VAR=value` | Done | `Command::Export` |
| Special vars `$?`, `$$`, `$#`, `$@`, `$*` | Done | Tracked in ShellState |
| Default value `${VAR:-default}` | Done | |
| Assign default `${VAR:=default}` | **Incomplete** | Behaves like `:-` (no assignment side-effect) |
| Alternative `${VAR:+alt}` | Done | |
| Error `${VAR:?msg}` | Done | |
| Length `${#VAR}` | Done | |
| Substring `${VAR:offset:length}` | Done | |
| Array variables `arr=(...)` | Done | Sparse arrays via BTreeMap |
| Array element `arr[n]=val` | Done | |
| Array append `arr+=(...)` | Done | |

**Known issues**:
- `$@` and `$*` behave identically (should differ in quoted context)
- `${VAR:=default}` does not actually assign — same as `${VAR:-default}`
- `export VAR` on unset var errors instead of creating empty exported var

### Milestone 5: Glob Expansion — COMPLETE

| Feature | Status | Implementation |
|---------|--------|---------------|
| `*` (match any) | Done | `glob` crate |
| `?` (single char) | Done | |
| `[...]` character class | Done | |
| `[!...]` negation | Done | |
| Hidden file exclusion | Done | `require_literal_leading_dot: true` (fixed 2026-02-12) |
| Brace expansion `{a,b,c}` | Done | Nested braces supported |
| Sorted results | Done | POSIX requirement |

### Milestone 6: Quote Processing — COMPLETE

| Feature | Status | Implementation |
|---------|--------|---------------|
| Single quotes `'...'` | Done | All literal |
| Double quotes `"..."` | Done | Expansion allowed |
| Backslash escapes | Done | `$`, `` ` ``, `"`, `\`, newline in double quotes |
| Unclosed quote detection | Done | |
| Line continuation | Done | |

### Milestone 7: Command Substitution — COMPLETE

| Feature | Status | Implementation |
|---------|--------|---------------|
| `$(cmd)` | Done | `expand_command_substitution()` |
| `` `cmd` `` (backticks) | Done | |
| Nested `$(echo $(pwd))` | Done | Depth tracking |
| Trailing newline stripping | Done | POSIX behavior |

### Milestone 8: Arithmetic Expansion — COMPLETE

| Feature | Status | Implementation |
|---------|--------|---------------|
| `$((expr))` | Done | Recursive descent parser in `arith.rs` |
| `+`, `-`, `*`, `/`, `%` | Done | |
| `**` (exponentiation) | Done | Beyond POSIX, right-associative |
| Bitwise `&`, `\|`, `^`, `~`, `<<`, `>>` | Done | Shift range validated (fixed 2026-02-12) |
| Comparison operators | Done | |
| Logical `&&`, `\|\|`, `!` | Done | Short-circuit |
| Parentheses | Done | |
| Variable references | Done | |
| Division by zero | Done | Returns error |

### Milestone 9: Control Structures — NOT STARTED

**This is the single biggest gap preventing practical shell use.**

| Feature | Status |
|---------|--------|
| `if`/`then`/`else`/`elif`/`fi` | Not implemented |
| `while`/`do`/`done` | Not implemented |
| `until`/`do`/`done` | Not implemented |
| `for`/`in`/`do`/`done` | Not implemented |
| `case`/`esac` | Not implemented |
| `select` (bashism) | Not implemented |

No traces of control structure parsing exist in the codebase.

### Milestone 10: Job Control — PARTIAL

| Feature | Status | Implementation |
|---------|--------|---------------|
| Background `&` | Done | `Command::External` with `background: true` |
| `jobs` | Done | `Command::Jobs` |
| `fg` | Done | `Command::Fg` |
| `bg` | Done | `Command::Bg` |
| `kill` | Done | `Command::Kill` |
| Job specs `%1`, `%+`, `%-`, `%name`, `%?pattern` | Done | `job.rs` |
| **SIGCHLD handler** | **Not implemented** | Job states not auto-updated |
| **Ctrl+Z (SIGTSTP)** | **Not implemented** | Cannot suspend foreground jobs |
| **Process groups** | **Not implemented** | |

### Milestone 11: Shell Builtins — PARTIAL

**Implemented**:
`cd`, `pwd`, `ls`, `mkdir`, `rmdir`, `touch`, `rm`, `exit`/`quit`, `export`,
`test`/`[`, `[[`, `jobs`, `fg`, `bg`, `kill`, `undo`, `redo`, `history`,
`begin`/`commit`/`rollback`, `graph`, `proofs`

**NOT implemented** (POSIX-required):
`echo`, `printf`, `read`, `set`, `unset`, `readonly`, `alias`/`unalias`,
`source`/`.`, `exec`, `eval`, `trap`, `true`/`false`, `type`, `command`,
`hash`, `umask`, `wait`, `getopts`, `shift`, `break`, `continue`, `return`,
`local`

### Milestone 12: Functions — NOT STARTED

No function definition or calling syntax exists in the parser.

### Milestone 13: Shell Scripts — NOT STARTED

No `.sh` file execution, no shebang handling.

### Milestone 14: Advanced Features — PARTIAL

| Feature | Status | Notes |
|---------|--------|-------|
| Here documents | Done | `<<DELIM`, `<<-DELIM` |
| Here strings | Done | `<<<word` |
| Process substitution | Done | `<(cmd)`, `>(cmd)` via FIFOs |
| Brace expansion | Done | Nested support |
| Extended test `[[ ]]` | Done | Pattern matching |
| Array variables | Done | Sparse indexed arrays |
| Tilde expansion | **Partial** | Only `~/` in `cd` command |
| Coprocesses | Not implemented | |
| Associative arrays | Not implemented | |

---

## Critical Missing Features (by impact)

1. **Control structures** — Blocks ALL script execution
2. **Functions** — No `func() { ... }`
3. **`echo` builtin** — Delegates to external `/usr/bin/echo`
4. ~~**`2>&1` fd duplication**~~ — **Done** (tracks stdout file handle for `try_clone()`)
5. **Word splitting (`$IFS`)** — Unquoted expansions not split
6. ~~**Semicolons**~~ — **Done** (`cmd1; cmd2` splits and executes sequentially)
7. **Tilde expansion** — Only works for `~/` in `cd`
8. **`read` builtin** — Cannot read user input into variables
9. **`set`/`unset`/`readonly`** — Cannot manage shell options
10. **`source`/`.` and `eval`** — Cannot include scripts

---

## What IS Verified

- **200+ theorems** across 6 proof systems (Lean 4, Coq, Agda, Isabelle/HOL, Mizar, Z3)
- **31 proof holes** remain (26 gaps, 3 axioms, 2 structural) — see `docs/PROOF_HOLES_AUDIT.md`
- **Proven properties**: Reversibility, composition, independence, type preservation
- **Correspondence**: 28 tests validate Rust matches Lean 4 theorems (~85% confidence)
- **No mechanized extraction** — Lean 4 → Rust is via testing, not proven

---

## Test Coverage

**541 tests passing, 0 failures, 14 ignored** (as of 2026-02-12)

| Suite | Count |
|-------|-------|
| Unit tests (lib) | 220 |
| Correspondence | 28 |
| Extended | 55 |
| Integration | 35 + 10 |
| Lean4 proptest | 16 |
| Parameter expansion | 67 |
| Property correspondence | 15 |
| Property | 28 |
| Security | 15 |
| Doctests | 52 |

---

## Honest Assessment

**Milestones 1-8** are substantially complete with the caveats noted above.
The shell can execute external commands, pipe them together, redirect I/O,
expand variables/globs/arithmetic/commands, and process quotes correctly.

**Milestones 9-14** are the gap between "working REPL" and "usable shell."
Control structures and functions are the critical path. Without them, vsh
cannot run any real shell scripts.

**Estimated effort to full POSIX compliance**: 12-18 months from current state
(significantly less than the original 3-5 year estimate, since M1-M8 are done).

---

**Author**: Jonathan D.A. Jewell <jonathan.jewell@open.ac.uk>
