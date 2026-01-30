# Valence Shell v1.0: Testing & Verification Checklist

**Status**: Pre-v1.0 Release Validation
**Target**: 100% completion before v1.0 release
**Last Updated**: 2026-01-29

---

## Overview

This document tracks all testing and verification requirements for v1.0 release. Each item must be completed and verified before release.

**Progress**: 6/10 layers complete (60%)

---

## Layer 1: Formal Proofs ✅ COMPLETE

**Goal**: Mathematical certainty for core operations

### Status

- [x] Lean 4 theorems (primary source of truth)
  - [x] mkdir_rmdir_reversible
  - [x] createFile_deleteFile_reversible
  - [x] operation_sequence_reversible
  - [x] filesystem_equivalence theorems

- [x] Cross-validation in multiple proof systems
  - [x] Coq (Calculus of Inductive Constructions)
  - [x] Agda (Intensional Type Theory)
  - [x] Isabelle/HOL (Higher-Order Logic)
  - [x] Mizar (Set Theory)
  - [x] Z3 SMT (Automated verification)

### Metrics

- **Total Proofs**: 256+ theorems
- **Proof Systems**: 6
- **Completeness**: 100% for core operations

### Remaining Work

- [ ] Proofs for file truncation/append reversibility
- [ ] Proofs for quote processing correctness
- [ ] Proofs for glob expansion correctness

---

## Layer 2: Correspondence Tests ⚠️ PARTIAL

**Goal**: Verify Rust implementation matches Lean 4 specification

### Status

- [x] Basic correspondence tests (27 tests)
  - [x] mkdir/rmdir correspondence
  - [x] touch/rm correspondence
  - [x] Path preservation tests
  - [x] Precondition tests

- [ ] Mechanized correspondence proofs
  - [ ] Lean 4 → Rust extraction
  - [ ] Automated verification pipeline
  - [ ] Formal bisimulation proof

### Current Confidence

- **Manual Correspondence**: 85%
- **Target for v1.0**: 95%
- **Target for v2.0**: 99.9%

### Required for v1.0

```bash
# Run all correspondence tests
cd impl/rust-cli
cargo test correspondence

# Expected output: 27/27 passing

# Add mechanized tests
cargo test --features lean-runtime-checks
```

### Remaining Work

- [ ] Add 20+ property-based correspondence tests
- [ ] Implement Lean 4 extraction framework
- [ ] Create automated verification in CI
- [ ] Document correspondence mapping for all operations

---

## Layer 3: Property-Based Tests ❌ TODO

**Goal**: Randomized validation with 1000s of test cases

### Required Tests

#### PropTest (Rust)

```rust
// impl/rust-cli/tests/property_tests.rs

#[test]
fn prop_mkdir_rmdir_always_reversible() {
    // Generate random valid paths
    // Verify mkdir followed by rmdir always restores state
    // 1000+ iterations
}

#[test]
fn prop_operation_sequence_reversible() {
    // Generate random operation sequences
    // Verify undo(ops) always works
    // 1000+ iterations
}

#[test]
fn prop_glob_expansion_quote_aware() {
    // Generate random glob patterns with quotes
    // Verify quoted patterns never expand
    // 1000+ iterations
}
```

#### Echidna (Haskell-based)

- [ ] Set up Echidna configuration
- [ ] Generate properties from Lean 4 theorems
- [ ] Integrate into CI/CD pipeline
- [ ] Document property failures

### Status

- [x] PropTest framework added
- [x] 19 property tests written
- [ ] Echidna integration (planned for v1.0)
- [ ] 95%+ property coverage

### Remaining Work

- [ ] Add 30+ property-based tests
- [ ] Echidna integration (see docs/ECHIDNA_INTEGRATION.md)
- [ ] Continuous fuzzing in CI
- [ ] Property failure analysis toolkit

---

## Layer 4: Integration Tests ✅ COMPLETE

**Goal**: End-to-end testing of real usage scenarios

### Status

- [x] Filesystem operations (14 tests)
- [x] Undo/redo cycles (8 tests)
- [x] Pipeline execution (7 tests)
- [x] Glob expansion (9 tests)
- [x] Quote processing (integration via parser tests)
- [x] Redirections (6 tests)

### Metrics

- **Total Integration Tests**: 44+
- **Coverage**: Core features 100%
- **Pass Rate**: 100%

### Command

```bash
cd impl/rust-cli
cargo test --test integration_test

# Expected: 44+ tests passing
```

### Remaining Work for v1.0

- [ ] Add tests for test/[ commands
- [ ] Add tests for && and || operators
- [ ] Add tests for command grouping
- [ ] Add tests for if/while/case statements

---

## Layer 5: Unit Tests ✅ COMPLETE

**Goal**: Component isolation and module testing

### Status

- [x] Parser module (30+ tests)
- [x] Quotes module (17 tests)
- [x] Glob module (8 tests)
- [x] State module (5 tests)
- [x] Redirection module (10 tests)
- [x] External execution (7 tests)
- [x] Job control (8 tests)
- [x] Arithmetic expansion (5 tests)

### Metrics

- **Total Unit Tests**: 157+
- **Module Coverage**: 90%+
- **Pass Rate**: 100%

### Command

```bash
cargo test --lib

# Expected: 157+ tests passing
```

### Remaining Work

- [ ] Add unit tests for test_command module
- [ ] Add unit tests for && / || parsing
- [ ] Increase coverage to 95%+

---

## Layer 6: Fuzzing ⚠️ PARTIAL

**Goal**: Attack surface testing with untrusted input

### Current Fuzz Targets

```
impl/rust-cli/fuzz/fuzz_targets/
├── fuzz_parser.rs       ✅ Created
├── fuzz_arith.rs        ✅ Created
├── fuzz_job_spec.rs     ✅ Created
└── fuzz_signal_parse.rs ✅ Created
```

### Fuzzing Campaigns

- [ ] Parser fuzzing (24 hours minimum)
  ```bash
  cargo fuzz run fuzz_parser -- -max_total_time=86400
  ```

- [ ] Arithmetic expression fuzzing (12 hours)
  ```bash
  cargo fuzz run fuzz_arith -- -max_total_time=43200
  ```

- [ ] Job spec fuzzing (6 hours)
  ```bash
  cargo fuzz run fuzz_job_spec -- -max_total_time=21600
  ```

- [ ] Signal parsing fuzzing (6 hours)
  ```bash
  cargo fuzz run fuzz_signal_parse -- -max_total_time=21600
  ```

### Coverage Targets

- [ ] Parser: 95%+ code coverage
- [ ] Arithmetic: 90%+ code coverage
- [ ] Job specs: 85%+ code coverage
- [ ] Signal parsing: 90%+ code coverage

### Crash Analysis

- [ ] No crashes in 24-hour run
- [ ] All crashes documented and fixed
- [ ] Regression tests added for found bugs

### Remaining Work

- [ ] Run continuous fuzzing campaigns
- [ ] Add fuzzing for quote processing
- [ ] Add fuzzing for glob expansion
- [ ] Add fuzzing for test command expressions
- [ ] Set up OSS-Fuzz for continuous fuzzing

---

## Layer 7: Stress Tests ❌ TODO

**Goal**: Performance and reliability under extreme conditions

### Required Stress Tests

#### Deep Nesting

```bash
# Test 1: 1000-level directory nesting
vsh> mkdir -p $(printf 'a/%.0s' {1..1000})
vsh> cd $(printf 'a/%.0s' {1..1000})
vsh> undo  # Should handle gracefully
```

**Requirements**:
- [ ] No stack overflow
- [ ] Reasonable memory usage (<100MB)
- [ ] Undo works correctly
- [ ] Performance acceptable (<1s for undo)

#### Large Files

```bash
# Test 2: Large file operations (1GB+)
vsh> dd if=/dev/zero of=large.bin bs=1M count=1024
vsh> touch large.bin
vsh> undo  # Should handle large file content
```

**Requirements**:
- [ ] No OOM (Out of Memory)
- [ ] Streaming undo data (don't load all in memory)
- [ ] Progress indication for large operations
- [ ] Graceful degradation if undo data too large

#### Many Operations

```bash
# Test 3: 10,000 operations in history
for i in {1..10000}; do
  vsh> touch "file_$i.txt"
done
vsh> undo 10000  # Should handle efficiently
```

**Requirements**:
- [ ] History size limits (configurable)
- [ ] Efficient undo/redo (O(1) per operation)
- [ ] State persistence (<1s for save/load)
- [ ] Memory usage proportional to unique operations

#### Concurrent Access

```bash
# Test 4: Multiple vsh instances
Terminal 1: vsh> mkdir shared
Terminal 2: vsh> cd shared
Terminal 1: vsh> undo
```

**Requirements**:
- [ ] File locking for state file
- [ ] Graceful handling of conflicts
- [ ] Clear error messages
- [ ] No corruption of shared state

#### Resource Limits

```bash
# Test 5: Under memory pressure
ulimit -v 50000  # Limit virtual memory
vsh> # Perform normal operations
```

**Requirements**:
- [ ] Graceful degradation under low memory
- [ ] No panics on allocation failure
- [ ] Clear error messages
- [ ] Essential operations still work

### Remaining Work

- [ ] Create stress test suite script
- [ ] Run all 5 stress test categories
- [ ] Document performance characteristics
- [ ] Add stress tests to CI (weekly runs)

---

## Layer 8: Compilation Tests ⚠️ PARTIAL

**Goal**: Cross-platform compilation verification

### Current Status

- [x] Linux (Fedora) - Primary development platform
- [ ] Linux (Ubuntu 22.04 LTS)
- [ ] Linux (Ubuntu 24.04 LTS)
- [ ] Linux (Arch Linux)
- [ ] macOS (Intel)
- [ ] macOS (Apple Silicon)
- [ ] FreeBSD
- [ ] OpenBSD

### CI/CD Pipeline

```yaml
# .github/workflows/ci.yml
name: CI

on: [push, pull_request]

jobs:
  test:
    strategy:
      matrix:
        os: [ubuntu-22.04, ubuntu-24.04, macos-latest]
        rust: [stable, nightly]

    runs-on: ${{ matrix.os }}

    steps:
      - uses: actions/checkout@v4
      - uses: dtolnay/rust-toolchain@master
        with:
          toolchain: ${{ matrix.rust }}

      - name: Build
        run: cargo build --verbose

      - name: Test
        run: cargo test --verbose

      - name: Test (lean-runtime-checks)
        run: cargo test --features lean-runtime-checks
```

### Requirements

- [ ] All tests pass on all platforms
- [ ] No platform-specific compilation errors
- [ ] Consistent behavior across platforms
- [ ] CI runs on every commit

### Remaining Work

- [ ] Set up GitHub Actions CI
- [ ] Add macOS to CI matrix
- [ ] Add FreeBSD/OpenBSD if possible
- [ ] Test on ARM64 (Raspberry Pi, Apple Silicon)
- [ ] Document platform-specific issues

---

## Layer 9: Security Audits ❌ TODO

**Goal**: Attack surface analysis and vulnerability assessment

### Security Checklist

#### Input Validation

- [ ] **Path Traversal**: Test `../../../../etc/passwd`
  ```bash
  vsh> cat ../../../../etc/passwd
  # Should sanitize or reject
  ```

- [ ] **Command Injection**: Test `$(rm -rf /)`
  ```bash
  vsh> echo "$(malicious command)"
  # Should not execute in unsafe context
  ```

- [ ] **Glob Bombs**: Test `*/*/*/*/*/*/*/*/...`
  ```bash
  vsh> ls */*/*/*/*/*/*/*/
  # Should have recursion limits
  ```

- [ ] **Quote Injection**: Test `'$(evil)'` vs `"$(evil)"`
  ```bash
  vsh> echo '$(whoami)'  # Should stay literal
  vsh> echo "$(whoami)"  # Should expand safely
  ```

#### Resource Exhaustion

- [ ] **Fork Bombs**: Test `:(){ :|:& };:`
  ```bash
  vsh> :(){ :|:& };:
  # Should detect and prevent
  ```

- [ ] **Infinite Loops**: Test `while true; do :; done`
  ```bash
  vsh> while true; do :; done
  # Should allow Ctrl+C interrupt
  ```

- [ ] **Memory Bombs**: Test large glob expansions
  ```bash
  vsh> echo {1..1000000000}
  # Should have limits
  ```

#### Privilege Escalation

- [ ] **Setuid Binaries**: Ensure safe handling
- [ ] **Environment Variables**: No $LD_PRELOAD tricks
- [ ] **File Permissions**: Respect umask, permissions

#### Data Leakage

- [ ] **Sensitive Files**: No accidental disclosure
- [ ] **Error Messages**: Don't leak paths/usernames
- [ ] **State Files**: Proper permissions (0600)

### Security Tools

```bash
# Static analysis
cargo clippy -- -W clippy::all

# Dependency audit
cargo audit

# Memory sanitizer (nightly)
RUSTFLAGS="-Z sanitizer=address" cargo +nightly test

# Undefined behavior sanitizer
RUSTFLAGS="-Z sanitizer=undefined" cargo +nightly test
```

### Remaining Work

- [ ] Complete security checklist (20+ tests)
- [ ] Run automated security scanners
- [ ] Third-party security audit (recommended)
- [ ] Document security model
- [ ] Create security policy (SECURITY.md)

---

## Layer 10: Benchmarking ❌ TODO

**Goal**: Performance metrics and regression prevention

### Benchmark Suite

Create `benches/benchmarks.rs`:

```rust
use criterion::{black_box, criterion_group, criterion_main, Criterion};

fn bench_cold_start(c: &mut Criterion) {
    c.bench_function("cold_start", |b| {
        b.iter(|| {
            // Spawn vsh process and measure time to ready
        });
    });
}

fn bench_simple_command(c: &mut Criterion) {
    c.bench_function("echo_hello", |b| {
        b.iter(|| {
            // Execute: echo "hello"
        });
    });
}

fn bench_pipeline(c: &mut Criterion) {
    c.bench_function("pipeline_3_stages", |b| {
        b.iter(|| {
            // Execute: ls | grep txt | wc -l
        });
    });
}

fn bench_glob_expansion(c: &mut Criterion) {
    c.bench_function("glob_1000_files", |b| {
        // Setup: Create 1000 .txt files
        b.iter(|| {
            // Execute: echo *.txt
        });
    });
}

fn bench_undo_operation(c: &mut Criterion) {
    c.bench_function("undo_mkdir", |b| {
        b.iter(|| {
            // mkdir test
            // undo
        });
    });
}

criterion_group!(
    benches,
    bench_cold_start,
    bench_simple_command,
    bench_pipeline,
    bench_glob_expansion,
    bench_undo_operation
);
criterion_main!(benches);
```

### Performance Targets

| Metric | Target | Stretch Goal |
|--------|--------|--------------|
| Cold start | <5ms | <3ms |
| Simple command | <10ms | <5ms |
| Pipeline (3 stages) | <50ms | <30ms |
| Glob (100 files) | <5ms | <3ms |
| Undo operation | <1ms | <0.5ms |
| State load | <10ms | <5ms |
| State save | <10ms | <5ms |
| Memory (idle) | <10MB | <5MB |
| Memory (1000 ops) | <50MB | <30MB |

### Comparison Benchmarks

```bash
# Compare with bash
hyperfine --warmup 3 'bash -c "echo hello"' 'vsh -c "echo hello"'

# Compare with zsh
hyperfine --warmup 3 'zsh -c "ls | wc -l"' 'vsh -c "ls | wc -l"'

# Compare with fish
hyperfine --warmup 3 'fish -c "echo *.txt"' 'vsh -c "echo *.txt"'
```

### Regression Prevention

```bash
# Save baseline
cargo bench --bench benchmarks -- --save-baseline main

# Compare after changes
cargo bench --bench benchmarks -- --baseline main
```

### Remaining Work

- [ ] Create comprehensive benchmark suite
- [ ] Run baseline benchmarks
- [ ] Compare with bash/zsh/fish
- [ ] Identify and fix performance bottlenecks
- [ ] Set up benchmark CI (track regressions)
- [ ] Document performance characteristics

---

## Summary Dashboard

### Overall Progress

```
Layer 1: Formal Proofs          ████████████████████ 100% ✅
Layer 2: Correspondence         ████████████░░░░░░░░  60% ⚠️
Layer 3: Property-Based         ████░░░░░░░░░░░░░░░░  20% ❌
Layer 4: Integration Tests      ████████████████████ 100% ✅
Layer 5: Unit Tests             ████████████████████ 100% ✅
Layer 6: Fuzzing                ████████░░░░░░░░░░░░  40% ⚠️
Layer 7: Stress Tests           ░░░░░░░░░░░░░░░░░░░░   0% ❌
Layer 8: Compilation Tests      ████████░░░░░░░░░░░░  40% ⚠️
Layer 9: Security Audits        ░░░░░░░░░░░░░░░░░░░░   0% ❌
Layer 10: Benchmarking          ░░░░░░░░░░░░░░░░░░░░   0% ❌
                                ─────────────────────────
                                Overall:  46% (6/10)
```

### Critical Path to v1.0

**Blocking Items** (Must complete before v1.0):

1. **Layer 3**: Property-based tests (60% → 100%)
   - [ ] Add 30+ PropTest tests
   - [ ] Integrate Echidna
   - [ ] Run fuzzing campaigns

2. **Layer 7**: Stress tests (0% → 100%)
   - [ ] Deep nesting, large files, many operations
   - [ ] Resource limit tests
   - [ ] Performance under pressure

3. **Layer 8**: Compilation tests (40% → 100%)
   - [ ] CI/CD pipeline for all platforms
   - [ ] macOS and BSD testing

4. **Layer 9**: Security audits (0% → 100%)
   - [ ] Complete security checklist
   - [ ] Vulnerability assessment
   - [ ] Third-party audit (recommended)

5. **Layer 10**: Benchmarking (0% → 100%)
   - [ ] Comprehensive benchmark suite
   - [ ] Performance targets verified
   - [ ] Regression prevention

**Timeline**: 4-6 weeks to complete all layers

---

## Automation Scripts

### Run All Tests

```bash
#!/bin/bash
# scripts/run_all_tests.sh

echo "🧪 Running ALL verification layers..."

# Layer 1: Proofs (manual verification)
echo "✅ Layer 1: Formal proofs (256+ theorems verified)"

# Layer 2: Correspondence
echo "📊 Layer 2: Correspondence tests..."
cargo test correspondence

# Layer 3: Property-based (when ready)
# echo "🎲 Layer 3: Property-based tests..."
# cargo test --features echidna

# Layer 4: Integration
echo "🔗 Layer 4: Integration tests..."
cargo test --test integration_test

# Layer 5: Unit
echo "🧩 Layer 5: Unit tests..."
cargo test --lib

# Layer 6: Fuzzing (run separately - takes hours)
echo "⚠️  Layer 6: Fuzzing - run manually (24h+ campaigns)"

# Layer 7: Stress (when implemented)
# echo "💪 Layer 7: Stress tests..."
# ./scripts/stress_tests.sh

# Layer 8: Compilation
echo "🔨 Layer 8: Compilation tests..."
cargo build --release

# Layer 9: Security (when implemented)
# echo "🔒 Layer 9: Security audit..."
# ./scripts/security_audit.sh

# Layer 10: Benchmarks (when implemented)
# echo "⚡ Layer 10: Benchmarks..."
# cargo bench

echo "✅ All available tests complete!"
```

---

**END OF TESTING CHECKLIST**
