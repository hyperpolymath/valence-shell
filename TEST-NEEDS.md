# TEST-NEEDS: valence-shell

## Current State

| Category | Count | Details |
|----------|-------|---------|
| **Source modules** | 77 | Rust CLI (~32: parser, commands, arith, glob, job, pager, etc.), Zig impl (~12: root, audit, daemon, demo, path, preconditions, prover, etc.), Elixir (2: application, NIF), 3 Idris2 ABI |
| **Unit tests (Rust inline)** | ~250+ | parser=112, commands=27, state=34, posix_builtins=18, quotes=17, arith=13, external=13, functions=13, glob=8, job=8, highlighter=6, etc. |
| **Integration tests (Rust)** | 11 files | parameter_expansion=67, extended_test=55, integration=35, correspondence=35, function_and_script=24, property_correspondence=19, property=28, lean4_proptest=16, security=15, stress=11, integration_tests=10 |
| **Elixir tests** | 1 file | vsh_test.exs (13 assertions) |
| **Zig tests** | ~21 | Inline test functions across src files |
| **Shell integration test** | 1 | integration_test.sh (70 assertions) |
| **E2E tests** | 0 | None |
| **Benchmarks** | 0 | None |

## What's Missing

### P2P Tests
- [ ] No tests for Rust CLI <-> Zig backend <-> Elixir NIF pipeline
- [ ] No tests for Lean4 prover integration in practice (only proptest correspondence)

### E2E Tests
- [ ] No test running valence-shell as an actual shell (interactive session)
- [ ] No POSIX compliance test suite
- [ ] No test for script execution end-to-end

### Aspect Tests
- [ ] **Security**: security_tests.rs exists (15 tests) -- good start but insufficient for a shell (needs injection, escape, privilege escalation tests)
- [ ] **Performance**: No benchmarks for shell startup time, command dispatch latency
- [ ] **Concurrency**: No tests for job control with concurrent processes
- [ ] **Error handling**: stress_tests.rs exists (11 tests) -- needs expansion

### Benchmarks Needed
- [ ] Shell startup time
- [ ] Command parsing throughput
- [ ] Pipeline execution overhead vs bash/zsh
- [ ] Glob expansion performance (1000/10000 files)

### Self-Tests
- [ ] No `valence-shell --self-test` mode
- [ ] No POSIX conformance self-check

## FLAGGED ISSUES
- **Best tested repo in the scan** -- 250+ inline + 315+ integration tests across 3 languages
- **Property-based testing exists** (proptest, lean4 correspondence) -- rare and excellent
- **No benchmarks at all for a SHELL** -- startup time and command latency are critical
- **Elixir layer has only 13 tests** compared to 300+ Rust tests
- **Zig layer has only ~21 inline tests for 12 modules** -- undertested

## Priority: P2 (MEDIUM) -- strong test foundation, needs benchmarks and E2E

## FAKE-FUZZ ALERT

- `tests/fuzz/placeholder.txt` is a scorecard placeholder inherited from rsr-template-repo — it does NOT provide real fuzz testing
- Replace with an actual fuzz harness (see rsr-template-repo/tests/fuzz/README.adoc) or remove the file
- Priority: P2 — creates false impression of fuzz coverage
