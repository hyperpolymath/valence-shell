# SPDX-License-Identifier: PMPL-1.0-or-later
# POSIX Compliance Status - Valence Shell (v0.9.0)

**Goal**: Full POSIX shell compliance with formal verification at each increment

**Current Status**: Milestones 1-8 complete; M9 complete; M10-11 partial; M12-14 not started

**Last Updated**: 2026-03-08 (P7 documentation rewrite)

---

## Milestone Status Overview

| # | Milestone | Status | Notes |
|---|-----------|--------|-------|
| 1 | Simple Command Execution | **Complete** | PATH lookup, args, exit status |
| 2 | Redirections | **Complete** | All 8 types including `2>&1` |
| 3 | Pipelines | **Complete** | Multi-stage, exit code from last |
| 4 | Variables | **Complete** | Scalars, arrays, parameter expansion |
| 5 | Glob Expansion | **Complete** | POSIX-compliant + brace expansion |
| 6 | Quote Processing | **Complete** | Single, double, backslash |
| 7 | Command Substitution | **Complete** | `$(cmd)` and backticks |
| 8 | Arithmetic | **Complete** | Full operator set including `**` |
| 9 | Control Structures | **Complete** | if/elif/else, while, for, case/esac |
| 10 | Job Control | **Partial** | No SIGCHLD, no Ctrl+Z |
| 11 | Shell Builtins | **Partial** | ~30 implemented, ~15 missing |
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

### Milestone 2: Redirections — COMPLETE

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
| Reversible assignment (undo/redo) | Done | `OperationType::SetVariable`/`UnsetVariable` |

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

### Milestone 9: Control Structures — COMPLETE (added 2026-03-08)

| Feature | Status | Implementation |
|---------|--------|---------------|
| `if`/`then`/`else`/`elif`/`fi` | Done | `Command::If` with condition chains |
| `while`/`do`/`done` | Done | `Command::While` with break/continue |
| `for`/`in`/`do`/`done` | Done | `Command::For` with glob expansion in wordlist |
| `case`/`esac` | Done | `Command::Case` with glob pattern matching |
| `until`/`do`/`done` | Not implemented | Rarely used, low priority |
| `select` (bashism) | Not implemented | Non-POSIX |
| `test`/`[` builtin | Done | `test_builtin.rs` — file tests, string ops, numeric comparison |
| `[[ ]]` extended test | Done | Pattern matching, regex support |
| Logical operators `&&` `\|\|` | Done | Short-circuit, left-to-right (fixed 2026-02-12) |
| Multi-line input | Done | REPL detects open blocks and prompts `>` |

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

**Implemented** (30):
`cd`, `pwd`, `ls`, `mkdir`, `rmdir`, `touch`, `rm`, `cp`, `mv`, `ln`,
`chmod`, `chown`, `exit`/`quit`, `export`, `test`/`[`, `[[`,
`echo`, `read`, `source`/`.`, `eval`, `set`, `unset`, `true`, `false`,
`jobs`, `fg`, `bg`, `kill`,
`undo`, `redo`, `history`, `begin`/`commit`/`rollback`, `graph`, `proofs`,
`explain`, `checkpoint`, `restore`, `checkpoints`, `diff`, `replay`

**NOT implemented** (POSIX-required):
`printf`, `readonly`, `alias`/`unalias`, `exec`, `trap`,
`type`, `command`, `hash`, `umask`, `wait`, `getopts`, `shift`,
`break`, `continue`, `return`, `local`

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

## Formally Verified Operations

All filesystem-mutating builtins are backed by formal proofs:

| Operation | Proof Systems | Theorems | Gaps |
|-----------|---------------|----------|------|
| mkdir/rmdir | Lean, Coq, Agda, Isabelle, Mizar, Z3 | Reversibility, composition | 0 |
| touch/rm | Lean, Coq, Agda, Isabelle, Mizar, Z3 | Reversibility | 0 |
| write_file | Lean, Coq, Agda, Isabelle, Mizar, Z3 | Content reversibility | 0 |
| cp | Lean, Coq, Agda, Isabelle, Mizar, Z3 | Copy reversibility | 0 |
| mv | Lean, Coq, Agda, Isabelle, Mizar, Z3 | Move reversibility | 0 |
| ln -s | Lean, Coq, Agda, Isabelle, Mizar, Z3 | Symlink reversibility | 0 |
| chmod | Lean, Coq, Agda, Isabelle, Mizar, Z3 | Permission reversibility | 0 |
| chown | Lean, Coq, Agda, Isabelle, Mizar, Z3 | Ownership reversibility | 0 |
| Variable assignment | Pending | State-machine property | Pending |

**Total**: ~250+ theorems, 4 remaining gaps, 4 axioms (see `docs/PROOF_HOLES_AUDIT.md`)

---

## Critical Missing Features (by impact)

1. **Functions** — No `func() { ... }` — blocks modular scripts
2. **Shell script execution** — No `.sh` file running
3. **Word splitting (`$IFS`)** — Unquoted expansions not split
4. **Tilde expansion** — Only works for `~/` in `cd`
5. **`trap`** — Cannot handle signals in scripts
6. **`alias`** — No command aliases
7. **SIGCHLD/Ctrl+Z** — Job control incomplete

---

## Test Coverage

**602 tests passing, 0 failures, 14 ignored** (as of 2026-03-08)

| Suite | Count |
|-------|-------|
| Unit tests (lib) | 277 |
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

**Milestones 1-9** are complete with the caveats noted above.
The shell can execute external commands, pipe them together, redirect I/O,
expand variables/globs/arithmetic/commands, process quotes, and run
control structures (if/while/for/case). Reversible builtins include
mkdir, rmdir, touch, rm, cp, mv, ln, chmod, chown — all with formal proofs.

**Milestones 10-14** are the gap between "functional shell" and "full POSIX shell."
Functions and shell script execution are the critical path. Without them, vsh
cannot run complex shell scripts.

**Estimated effort to full POSIX compliance**: 6-12 months from current state
(M1-M9 done, M10-11 partial, M12-14 remaining).

---

**Author**: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
