# Valence Shell (vsh)

## Project Overview

**Formally verified shell with proven reversibility guarantees and MAA framework.**

**Current Version**: 0.9.0 (advanced research prototype, ~65% complete)
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
- Unix pipelines (`cmd1 | cmd2 | cmd3`)
- I/O redirections (`>`, `>>`, `<`, `2>`, `2>>`, `&>`, `2>&1`)
- Process substitution (`<(cmd)` and `>(cmd)`)
- Arithmetic expansion (`$((expr))`)
- Here documents (`<<DELIM`) and here strings (`<<<word`)
- Glob expansion (`*.txt`, `file?.rs`, `[a-z]*`, `{1,2,3}`)
- Quote processing (single, double, backslash)
- `test`/`[` and `[[ ]]` conditionals
- Logical operators (`&&` `||`) with short-circuit evaluation
- Shell variables (`$VAR`, `${VAR}`, `export`)
- Job control (`bg`, `fg`, `jobs`, `kill`, `&` operator)
- Transaction grouping (`begin`/`commit`/`rollback`)
- Interactive REPL with history
- Command correction (zsh-style "Did you mean?")

### What Does NOT Work

- NOT a full POSIX shell (many features missing per `docs/POSIX_COMPLIANCE.md`)
- NOT formally verified end-to-end (Lean -> Rust is ~85% confidence via testing, not proven)
- NOT a replacement for bash/zsh in current state
- No GDPR compliance (RMO/secure deletion are stubs)
- No mechanized correspondence proof (manual testing only)
- Elixir NIF build broken (low priority)
- BEAM daemon not implemented (planned, not built)

### Test Results (2026-02-12, ALL PASSING)

| Suite | Count | Notes |
|-------|-------|-------|
| Unit tests (lib) | 220 | Core logic |
| Correspondence | 28 | Lean 4 theorem validation |
| Extended | 55 | Advanced features |
| Integration | 35 | End-to-end |
| Integration (extra) | 10 | Edge cases |
| Parameter expansion | 67 | Variable/parameter tests |
| Property correspondence | 15 | Property-based Lean validation |
| Property | 28 | General property tests |
| Security | 15 | Injection, traversal, validation |
| Doctests | 52 | Inline examples |
| **Total passing** | **525** | **0 failures** |
| Ignored (stress) | 15 | Run manually with `--ignored` |

### Codebase Metrics

- 15,720 lines of Rust across 30 source files
- ~200+ formal theorems across 6 proof systems
- 41 proof holes across 17 proof files (28 gaps, 3 axioms, 10 structural)

## Critical Issues

### Critical Priority

1. **No mechanized Lean -> Rust correspondence** — testing only, ~85% confidence
2. **28 real proof gaps** across 17 files (plus 3 axioms, 10 structural — see `docs/PROOF_HOLES_AUDIT.md`)
3. **NOT production-ready** — research prototype only

### High Priority

1. **47/58 commits authored as `Test <test@example.com>`** (Sonnet damage)
2. **Dead code**: `lean_ffi.rs` (library doesn't exist), `daemon_client.rs` (no daemon)
3. **No Echidna integration** for automated verification

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
      tests/            # 525 tests passing
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

1. **Close 28 proof gaps** (prioritized in `docs/PROOF_HOLES_AUDIT.md`)
2. **Remove dead code**: `lean_ffi.rs`, `daemon_client.rs`
3. **Fix git author** on future commits (currently `Test <test@example.com>`)

### This Week

1. Set up Echidna property-based validation pipeline
2. Begin mechanized Lean -> Rust correspondence (even partial)
3. Audit Sonnet's mega-commit for correctness beyond test files

### This Month

1. Achieve 95%+ correspondence confidence via property testing
2. Complete POSIX compliance for implemented features
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

**Last Updated**: 2026-02-12 (Opus honest audit and fixes)
**Version**: 0.9.0
**Status**: Advanced research prototype — NOT production-ready
**Tests**: 525 passing, 0 failures, 15 ignored
**Completion**: ~65%
