# Valence Shell (vsh)

## Project Overview

**Formally verified shell with proven reversibility guarantees and MAA framework.**

**Current Version**: 0.9.0 (advanced research prototype, ~72% complete)
**Primary Implementation**: `impl/rust-cli/` (Rust)
**License**: PMPL-1.0-or-later

## HONEST STATUS (2026-02-12)

**This project is NOT production-ready.** It is an advanced research prototype.

Previous documentation (from a Sonnet mega-commit) falsely claimed v1.0.0,
100% complete, production-ready. That was corrected on 2026-02-12 by an
Opus audit session that fixed all broken tests, real bugs, and documentation.

### What Actually Works (v0.9.0)

The Rust CLI is a functional interactive shell with these features:

- Built-in filesystem operations (mkdir, rmdir, touch, rm) with undo/redo
- External command execution via PATH lookup
- Reversible file operations (`cp`, `mv`, `ln -s`) with formal proofs
- Unix pipelines (`cmd1 | cmd2 | cmd3`)
- I/O redirections (`>`, `>>`, `<`, `2>`, `2>>`, `&>`, `2>&1`)
- Process substitution (`<(cmd)` and `>(cmd)`)
- Arithmetic expansion (`$((expr))`)
- Here documents (`<<DELIM`) and here strings (`<<<word`)
- Glob expansion (`*.txt`, `file?.rs`, `[a-z]*`, `{1,2,3}`)
- Quote processing (single, double, backslash)
- Control structures (`if/then/elif/else/fi`, `while/do/done`, `for/in/do/done`, `case/esac`)
- `test`/`[` and `[[ ]]` conditionals
- Logical operators (`&&` `||`) with short-circuit evaluation
- Shell builtins (`echo`, `read`, `source`, `eval`, `set`, `unset`, `true`, `false`)
- Shell variables (`$VAR`, `${VAR}`, `export`) with reversible assignment (undo/redo)
- Job control (`bg`, `fg`, `jobs`, `kill`, `&` operator)
- Transaction grouping (`begin`/`commit`/`rollback`)
- Interactive REPL with history and multi-line input for control structures
- Command correction (zsh-style "Did you mean?")
- `explain` command (proof-annotated dry runs)
- `checkpoint`/`restore` (named snapshots with proof certificates)
- `diff` (state comparison between checkpoints or current state)
- `replay` (animated history with proof narration)

### What Does NOT Work

- NOT a full POSIX shell (word splitting in external command args, $IFS in all contexts, full function nesting still incomplete)
- NOT formally verified end-to-end (Lean -> Rust is ~95% confidence via property testing, not proven)
- NOT a replacement for bash/zsh in current state
- No GDPR compliance (RMO/secure deletion are stubs)
- No mechanized correspondence proof (property testing only)
- Elixir NIF build broken (low priority)
- BEAM daemon not implemented (planned, not built)

### Test Results (2026-04-20, ALL PASSING)

| Suite | Count | Notes |
|-------|-------|-------|
| Unit tests (lib) | 310 | Core logic + control structures + tracked variables |
| Correspondence | 28 | Lean 4 theorem validation |
| Extended | 55 | Advanced features |
| Integration | 35 | End-to-end |
| Integration (extra) | 10 | Edge cases |
| Lean4 proptest correspondence | 16 | Property-based Lean validation |
| Parameter expansion | 67 | Variable/parameter tests |
| Property correspondence | 15 | Property-based Lean validation |
| Property | 28 | General property tests |
| Security | 15 | Injection, traversal, validation (skips on root) |
| Function/script | 24 | Function defs, scripts, trap/alias |
| Function control flow | 8 | Control structures in function bodies |
| IFS splitting | 8 | Word splitting in for-loops |
| Multi-line scripts | 9 | Sourced scripts with multi-line control structures |
| Tilde expansion | 9 | ~, ~/path, ~+, ~- |
| Trap firing | 7 | Signal handler execution |
| Doctests | 56 | Inline examples |
| **Total passing** | **736** | **0 failures** |
| Ignored (stress+1) | 14 | Run manually with `--ignored` |

### Codebase Metrics

- ~21,000 lines of Rust across 33 source files
- ~200+ formal theorems across 6 proof systems
- 10 proof holes across 8 proof files (4 gaps, 4 axioms, 2 structural) — see `docs/PROOF_HOLES_AUDIT.md`

## Critical Issues

### Critical Priority

1. **No mechanized Lean -> Rust correspondence** — testing only, ~85% confidence
2. **4 real proof gaps** across 4 files (plus 4 axioms, 2 structural — see `docs/PROOF_HOLES_AUDIT.md`)
3. **NOT production-ready** — research prototype only

### High Priority

1. **47/58 commits authored as `Test <test@example.com>`** (Sonnet damage)
2. **No Echidna integration** for automated verification

_Note: the prior "Dead code" bullet (`lean_ffi.rs`, `daemon_client.rs`)
is closed — both files were removed in commit `5802dc9` (2026-02-12
deep-audit session). The corresponding Phase 4C design docs under
`impl/rust-cli/docs/` carry archival banners pointing here._

### Medium Priority

1. Full POSIX compliance incomplete (see `docs/POSIX_COMPLIANCE.md`)
2. No GDPR compliance (RMO/secure deletion are stubs)
3. Elixir NIF build broken (low priority)

### Low Priority

1. Performance not benchmarked in CI
2. Security audit script not automated

## What Was Fixed (2026-02-12 Opus Audit)

**Session**: Deep audit, test fixes, bug fixes, documentation rewrite

### Test Fixes (API signature mismatches from Sonnet)
- `correspondence_tests.rs`: `state.undo()/redo()` -> `vsh::commands::undo()/redo()`
- `correspondence_tests.rs`: `crate::` -> `vsh::` for integration test context
- `correspondence_tests.rs`: `state.operation_history()` -> `state.history`
- `property_tests.rs`: `proptest!(|()| ...)` -> plain test, `expand_glob` arity fixed
- `security_tests.rs`: `ShellState::new(temp.path())` -> `.to_str().unwrap()`
- `security_tests.rs`: `expand_glob` arity, recursive glob test scale reduced
- `stress_tests.rs`: `ShellState::new` signature, `pop_undo` -> `commands::undo`
- `integration_test.rs`: 6 glob tests rewritten from `Command::new("ls")` to `vsh::glob::expand_glob()`

### Real Bug Fixes
- **Redo bug**: `record_operation()` cleared redo stack, breaking multi-step redo. Added `record_redo_operation()` in `state.rs`
- **Glob POSIX compliance**: `expand_glob` now uses `require_literal_leading_dot: true` (hidden files not matched by `*`)
- **4 doctest fixes**: Missing imports, PATH-dependent assertions
- **Append redirection truncation**: `>>` used `File::create()` (truncates!) instead of `OpenOptions::append()` in `external.rs`
- **`2>` tokenization**: `file2>out` incorrectly split as `file [2>] out` instead of `file2 [>] out` — now only treats `2>` as error redirect when `2` starts a new token
- **Logical operator precedence**: `a && b || c` parsed as `a && (b || c)` — fixed to left-to-right `(a && b) || c` via `rposition`
- **Shift overflow panic**: `$((1 << 64))` panicked — now returns error for shift counts >= 64
- **Path traversal**: `resolve_path("../../etc/passwd")` could escape sandbox — now normalizes `..` components and clamps to root
- **Version mismatch**: `main.rs` reported version 1.0.0 and "256 proofs" — fixed to 0.9.0 and "200+ theorems"

### Dead Code Removed
- `QuotedWord::with_quote_type()` — never called (parser.rs)
- `RedirectSetup::get_file()` — never called (redirection.rs)
- `JobTable::get_job_mut()` — never called (job.rs)
- `JobTable::cleanup_done_jobs()` — never called (job.rs)

### Documentation Fixes
- Downgraded version from 1.0.0 to 0.9.0 (honest)
- Rewrote STATE.scm from inflated 1114-line mess to honest ~130-line assessment
- Rewrote ECOSYSTEM.scm with accurate status
- Rewrote this CLAUDE.md (was stale at v0.7.0)
- Fixed Cargo.toml license typo: PLMP -> PMPL

## Architecture

### Technology Stack

**Formal Verification (6 systems)**:
- Lean 4 — primary source of truth
- Coq — CIC foundation, extraction to OCaml
- Isabelle/HOL — cross-validation
- Agda — intensional type theory
- Mizar — set theory foundation
- Z3 SMT — automated verification

**Runtime**:
- Rust — primary shell implementation (`impl/rust-cli/`)
- Elixir — reference implementation (stale, NIF issues)
- OCaml — extraction target from Coq (design only)
- Zig — FFI layer (builds, not integrated)

### Directory Structure

```
valence-shell/
  impl/
    rust-cli/           # PRIMARY - Rust CLI (v0.9.0)
      src/              # 30 source files, 15,720 lines
      tests/            # 602 tests passing
      Cargo.toml
    elixir/             # Reference impl (stale)
    ocaml/              # Extraction target (design only)
  proofs/
    lean4/              # Primary proof source
    coq/                # CIC proofs + extraction
    agda/               # Type theory proofs
    isabelle/           # HOL proofs
    mizar/              # Set theory proofs
    z3/                 # SMT proofs
  ffi/zig/              # Zig FFI (builds, not integrated)
  docs/                 # Design docs, roadmaps
  .machine_readable/    # STATE.scm, ECOSYSTEM.scm, META.scm
```

### Key Rust Source Files

| File | Purpose |
|------|---------|
| `src/main.rs` | Entry point, REPL loop |
| `src/lib.rs` | Library root, module declarations |
| `src/state.rs` | ShellState, operation history, undo/redo state |
| `src/commands.rs` | Built-in commands (mkdir, rm, undo, redo, etc.) |
| `src/parser.rs` | Command parsing, variable expansion |
| `src/external.rs` | External command execution, PATH lookup |
| `src/pipeline.rs` | Unix pipeline implementation |
| `src/redirection.rs` | I/O redirection |
| `src/glob.rs` | Glob expansion (POSIX compliant) |
| `src/job_control.rs` | Job control (bg, fg, jobs) |
| `src/process_substitution.rs` | Process substitution |
| `src/arithmetic.rs` | Arithmetic expansion |
| `src/here_doc.rs` | Here documents and here strings |
| `src/test_builtin.rs` | test/[ and [[ ]] builtins |
| `src/correction.rs` | Command correction (Levenshtein) |
| `src/repl.rs` | Interactive REPL with reedline |

### API Notes for Test Writers

```rust
// ShellState takes &str, not &Path
let state = ShellState::new(temp.path().to_str().unwrap());

// undo/redo are free functions in vsh::commands, not methods
vsh::commands::undo(&mut state, count, verbose)?;
vsh::commands::redo(&mut state, count, verbose)?;

// History is a public field, not a method
let history: &Vec<Operation> = &state.history;

// Glob takes pattern + base_dir
vsh::glob::expand_glob(pattern, base_dir)?;

// In integration tests, use vsh:: not crate::
vsh::parser::expand_variables(&input, &state);
```

## For the Next Claude Session

### Immediate Priorities

1. **Word splitting in external command arguments** (requires quote-context threading)
2. **Alias expansion in pipe segments** (currently only first command in a pipeline)
3. **Echidna integration** for automated property-based verification
4. **`~user` tilde expansion** (requires getpwnam/NSS lookup)

### This Week

1. Implement shell functions (`func() { ... }`)
2. Shell script execution (`.sh` files)
3. Set up Echidna property-based validation pipeline

### This Month

1. Implement shell functions (`func() { ... }`)
2. Shell script execution (`.sh` files)
3. Begin Idris2 extraction path for v2.0

### What NOT to Do

- Do NOT claim this is production-ready
- Do NOT inflate version numbers
- Do NOT add features before closing proof holes
- Do NOT trust Sonnet's commit messages or claims without verification

## Building and Testing

```bash
cd impl/rust-cli

# Build
cargo build

# Run all tests
cargo test

# Run specific test suite
cargo test --test correspondence_tests
cargo test --test integration_test
cargo test --test security_tests

# Run stress tests (slow, ignored by default)
cargo test --test stress_tests -- --ignored

# Run the shell
cargo run
```

## MAA Framework

### RMR (Remove-Match-Reverse)
- Reversible transactions with undo/redo proof
- Proven for filesystem operations (mkdir/rmdir, create/delete)
- Working in Rust CLI

### RMO (Remove-Match-Obliterate)
- Irreversible deletion with proof of complete removal
- Stubs only — NOT implemented
- Needed for GDPR compliance

## License

PMPL-1.0-or-later (Palimpsest License)

---

## POSIX Compliance Notes (2026-03-08)

`docs/POSIX_COMPLIANCE.md` is now up-to-date. Milestones 1-9 complete, M10-11 partial.

**Most critical missing POSIX features** (ranked by impact):
1. Word splitting in external command args — `cmd $var` doesn't split (requires quote-context)
2. `~user` — only `~`, `~/`, `~+`, `~-` work (no getpwnam)
3. SIGCHLD/Ctrl+Z — job control incomplete
4. Here-string quoting edge cases
5. Subshell `(...)` syntax — not implemented

---

**Last Updated**: 2026-04-20 (function control-flow, multi-line scripts, tilde, IFS, trap, alias)
**Version**: 0.9.0
**Status**: Advanced research prototype — NOT production-ready
**Tests**: 736 passing, 0 failures, 14 ignored
**Completion**: ~78% (up from 72% at 2026-03-08)
