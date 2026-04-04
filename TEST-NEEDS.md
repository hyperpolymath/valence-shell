# TEST-NEEDS: valence-shell

## CRG Grade: C — ACHIEVED 2026-04-04

## Current State (Post-CRG-C Blitz 2026-04-04)

| Category | Count | Details |
|----------|-------|---------|
| **Source modules** | 77 | Rust CLI (~32: parser, commands, arith, glob, job, pager, etc.), Zig impl (~12: root, audit, daemon, demo, path, preconditions, prover, etc.), Elixir (2: application, NIF), 3 Idris2 ABI |
| **Unit tests (Rust inline)** | ~310+ | parser=112, commands=27, state=34, posix_builtins=18, quotes=17, arith=13, external=13, functions=13, glob=8, job=8, highlighter=6, etc. |
| **Integration tests (Rust)** | 12 files | parameter_expansion=67, extended_test=55, integration=35, correspondence=35, function_and_script=24, property_correspondence=19, property=28, lean4_proptest=16, security=15, stress=11, integration_tests=10, **e2e_script_execution=25** |
| **Elixir tests** | 1 file | vsh_test.exs (**19 test cases**, expanded with 6 NIF-specific tests) |
| **Zig tests** | ~28 | audit.zig **+5 tests**, other modules inline tests |
| **Shell integration test** | 1 | integration_test.sh (70 assertions) |
| **Benchmarks** | 3 files | **Fixed & operational**: operation_benchmarks.rs, performance_benchmarks.rs (8 benches), shell_benchmarks.rs (7 benches) |
| **E2E tests** | 1 file | **e2e_script_execution.rs (25 tests)** — script parsing, shebang, error handling, variable scope |

## What's Missing (Remaining Gaps)

### P2P Tests
- [ ] No tests for Rust CLI <-> Zig backend <-> Elixir NIF pipeline
- [ ] No tests for Lean4 prover integration in practice (only proptest correspondence)

### Interactive E2E Tests
- [x] ✅ **Script execution end-to-end** — 25 E2E tests added (script parsing, shebang, error handling)
- [ ] No test running valence-shell as an actual shell REPL (interactive session)
- [ ] No POSIX compliance test suite (compliance docs exist, test harness does not)

### Aspect Tests
- [ ] **Security**: security_tests.rs exists (15 tests) -- good start but insufficient for a shell (needs injection, escape, privilege escalation tests)
- [x] ✅ **Performance**: Benchmarks added (3 files, 23+ benchmarks for startup, parsing, pipelines, undo/redo, checkpoint)
- [ ] **Concurrency**: No tests for job control with concurrent processes
- [ ] **Error handling**: stress_tests.rs exists (11 tests) -- needs expansion

### Benchmarks Completed
- [x] ✅ Shell startup time (cold + with state)
- [x] ✅ Command parsing throughput (simple commands, batch, 10-command sequences)
- [x] ✅ Pipeline parsing (2, 3, 5, 10 stage pipelines)
- [x] ✅ Glob expansion performance (10, 50, 100 files)
- [x] ✅ Undo/redo efficiency (single, scaling 10/50/100, cycle efficiency)
- [x] ✅ History lookup performance
- [x] ✅ Checkpoint creation & restore cycles
- [x] ✅ Deep directory nesting (5, 10, 20 levels)

### Self-Tests
- [ ] No `valence-shell --self-test` mode
- [ ] No POSIX conformance self-check

## FLAGGED ISSUES (CRG-C Status)

### Completed (2026-04-04)
- ✅ **Benchmarks**: 3 files, 23+ benchmarks now operational (was "None")
- ✅ **E2E script execution**: 25 tests added covering parsing, shebang, error handling
- ✅ **Zig layer expansion**: +5 tests added to audit.zig (was "~21 tests")
- ✅ **Elixir NIF expansion**: +6 NIF-specific tests added (was "13 assertions")

### Remaining Gaps
- **Best tested repo in the estate** -- 310+ inline + 335+ integration + 25 E2E tests
- **Property-based testing exists** (proptest, lean4 correspondence) -- rare and excellent
- **Zig layer still lean** -- 28 tests for 12 modules (needs continued expansion)
- **Elixir layer moderate** -- 19 test cases, NIF behavior now tested
- **No interactive REPL testing** -- E2E tests are script-focused, not interactive

## Priority: P2 → **CRG C (COMPLETE for blitz goals)**

**Metrics (Post-Blitz):**
- Benchmarks: ✅ **23+** (shell startup, command parsing, pipelines, undo/redo, checkpoint, history, glob, nesting)
- E2E tests: ✅ **25** (script execution coverage)
- Zig tests: ✅ **+5** (audit logging)
- Elixir tests: ✅ **+6** (NIF-specific behavior)
- **Total test coverage increase: ~60 new tests/benchmarks**

## FAKE-FUZZ ALERT

- `tests/fuzz/placeholder.txt` is a scorecard placeholder inherited from rsr-template-repo — it does NOT provide real fuzz testing
- Replace with an actual fuzz harness (see rsr-template-repo/tests/fuzz/README.adoc) or remove the file
- Priority: P2 — creates false impression of fuzz coverage
