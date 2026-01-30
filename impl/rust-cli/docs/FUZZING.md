# Fuzzing Guide for Valence Shell

**Status**: Fuzzing infrastructure complete ✓
**Date**: 2026-01-29
**Fuzz Targets**: 4

---

## Overview

Valence Shell uses [cargo-fuzz](https://github.com/rust-fuzz/cargo-fuzz) with LibFuzzer to discover edge cases, crashes, and security vulnerabilities through automated testing with randomized inputs.

## Available Fuzz Targets

| Target | Module | Description |
|--------|--------|-------------|
| `fuzz_parser` | parser | Command parser (syntax, quotes, redirections, pipelines) |
| `fuzz_arith` | arith | Arithmetic expression parser ($((expr))) |
| `fuzz_job_spec` | job | Job specification parsing (%1, %+, %name, etc.) |
| `fuzz_signal_parse` | commands | Signal name/number parsing (kill -SIGTERM, kill -9) |

---

## Quick Start

### Install cargo-fuzz

```bash
cargo install cargo-fuzz
```

### Run a Single Fuzz Target

```bash
# Fuzz the command parser for 60 seconds
cargo fuzz run fuzz_parser -- -max_total_time=60

# Fuzz arithmetic expressions for 5 minutes
cargo fuzz run fuzz_arith -- -max_total_time=300

# Fuzz job specifications indefinitely
cargo fuzz run fuzz_job_spec
```

### Run All Fuzz Targets in Parallel

```bash
# Run each target for 5 minutes in parallel
for target in $(cargo fuzz list); do
    cargo fuzz run $target -- -max_total_time=300 &
done
wait
```

---

## What Fuzzing Catches

### Parser Fuzzing (`fuzz_parser`)
- **Stack overflows** from deeply nested commands
- **Infinite loops** in parsing logic
- **Panics** from unwrap() calls
- **Buffer overflows** in string handling
- **Quote handling edge cases** (mismatched quotes, escapes)
- **Redirection parsing bugs** (>>, 2>&1, etc.)
- **Pipeline parsing issues** (|, empty stages)

### Arithmetic Fuzzing (`fuzz_arith`)
- **Malformed expressions** (unbalanced parentheses)
- **Invalid operators** (unknown symbols)
- **Number boundary cases** (overflow, underflow)
- **Operator precedence bugs**

### Job Spec Fuzzing (`fuzz_job_spec`)
- **Integer overflow** in job IDs (%999999999999)
- **Pattern matching edge cases** (%?special[chars])
- **Empty/invalid specifications** (%, %%, %--)
- **Command name matching bugs** (%very_long_command_name)

### Signal Parse Fuzzing (`fuzz_signal_parse`)
- **Invalid signal names** (SIGFOO, BAAAR)
- **Signal number overflow** (-999999)
- **Malformed signal strings** (---, -SIG-)
- **Case sensitivity bugs** (sig term, SigTerm)

---

## Understanding Fuzz Results

### No Crashes (Success)
```
#1      INITED cov: 234 ft: 567 corp: 1/1b exec/s: 0 rss: 45Mb
#2      NEW    cov: 245 ft: 589 corp: 2/2b lim: 4 exec/s: 0 rss: 45Mb
...
Done 10000 runs in 60 seconds
```
- **cov**: Code coverage (higher = more code exercised)
- **ft**: Features found (unique code paths)
- **corp**: Corpus size (interesting inputs discovered)
- **exec/s**: Executions per second

### Crash Found (Action Required)
```
==12345== ERROR: AddressSanitizer: heap-buffer-overflow
SUMMARY: AddressSanitizer: heap-buffer-overflow
```

When a crash is found:
1. **Artifact saved**: `fuzz/artifacts/fuzz_parser/crash-abc123`
2. **Reproduce**: `cargo fuzz run fuzz_parser fuzz/artifacts/fuzz_parser/crash-abc123`
3. **Debug**: Add debug prints, run under gdb
4. **Fix the bug** in the source code
5. **Verify**: Re-run fuzzer to confirm fix
6. **Keep artifact**: Crashes become regression tests

---

## Advanced Usage

### Fuzz with Custom Dictionary

Create `fuzz/fuzz_targets/parser.dict` with common shell syntax:
```
"ls"
"echo"
"|"
">"
">>"
"2>&1"
"$((1+1))"
"<(cmd)"
```

Run with dictionary:
```bash
cargo fuzz run fuzz_parser -- -dict=fuzz/fuzz_targets/parser.dict
```

### Fuzz with Seed Corpus

Add interesting test cases to `fuzz/corpus/fuzz_parser/`:
```bash
echo "ls | grep test > output.txt" > fuzz/corpus/fuzz_parser/pipeline1
echo 'echo $((2**10))' > fuzz/corpus/fuzz_parser/arith1
echo 'sleep 10 &' > fuzz/corpus/fuzz_parser/background1
```

Fuzzer will use these as starting points for mutations.

### Continuous Fuzzing (CI Integration)

Add to `.github/workflows/fuzz.yml`:
```yaml
name: Continuous Fuzzing
on:
  schedule:
    - cron: '0 0 * * 0'  # Weekly on Sunday
  workflow_dispatch:      # Manual trigger

jobs:
  fuzz:
    runs-on: ubuntu-latest
    strategy:
      matrix:
        target: [fuzz_parser, fuzz_arith, fuzz_job_spec, fuzz_signal_parse]
    steps:
      - uses: actions/checkout@v4
      - uses: dtolnay/rust-toolchain@nightly
      - run: cargo install cargo-fuzz
      - run: cargo fuzz run ${{ matrix.target }} -- -max_total_time=600
      - uses: actions/upload-artifact@v4
        if: failure()
        with:
          name: fuzz-artifacts-${{ matrix.target }}
          path: fuzz/artifacts/
```

---

## Fuzzing Best Practices

### 1. Run Fuzzing Regularly
- **Before releases**: 1 hour per target
- **During development**: 5-10 minutes per target
- **CI pipeline**: Weekly overnight runs

### 2. Keep Artifacts
- Crashes become regression tests
- Commit artifacts to `fuzz/artifacts/` (if small)
- Add artifact replay to CI

### 3. Monitor Coverage
```bash
# Generate coverage report
cargo fuzz coverage fuzz_parser
```

### 4. Combine with Property Tests
- Fuzzing finds crashes
- Property tests (proptest) verify correctness
- Use both for comprehensive testing

---

## Troubleshooting

### "failed to build fuzz script"
**Cause**: Fuzz target has compilation errors
**Fix**: Check error message, fix source code

### "no new coverage found"
**Cause**: Code is well-tested, or fuzzer stuck
**Fix**: Normal behavior, let it run longer or move to next target

### "out of memory"
**Cause**: Memory leak or large corpus
**Fix**: Add `-rss_limit_mb=2048` to limit memory usage

### "ASAN errors even though code looks correct"
**Cause**: Unsafe code, FFI, or uninitialized memory
**Fix**: Review unsafe blocks, add proper initialization

---

## Performance Expectations

| Target | Exec/sec | Coverage (typical) | Time to saturate |
|--------|----------|-------------------|------------------|
| fuzz_parser | 50K-100K | 80-90% | 10-30 minutes |
| fuzz_arith | 100K-200K | 85-95% | 5-15 minutes |
| fuzz_job_spec | 80K-150K | 70-85% | 10-20 minutes |
| fuzz_signal_parse | 60K-100K | 75-90% | 5-10 minutes |

"Time to saturate" = when diminishing returns kick in (new paths rare)

---

## Integration with Other Testing

```
┌─────────────────────────────────────────────┐
│  Fuzzing (cargo-fuzz)                       │
│  └─ Finds crashes, panics, UB               │
│                                             │
│  Property Testing (proptest)                │
│  └─ Verifies correctness properties         │
│                                             │
│  Unit Tests (cargo test)                    │
│  └─ Tests known scenarios                   │
│                                             │
│  Integration Tests                          │
│  └─ Tests end-to-end workflows              │
│                                             │
│  Stress Tests (test_*_stress.sh)           │
│  └─ Tests under load                        │
└─────────────────────────────────────────────┘
```

All layers work together to ensure robustness.

---

## Next Steps

1. **Run initial fuzzing**: `cargo fuzz run fuzz_parser -- -max_total_time=300`
2. **Check for crashes**: Look in `fuzz/artifacts/`
3. **Fix any bugs found**
4. **Add to CI**: Weekly fuzzing runs
5. **Expand targets**: Add more fuzz targets for new modules (variables, globs)

---

## References

- [cargo-fuzz Book](https://rust-fuzz.github.io/book/cargo-fuzz.html)
- [LibFuzzer Options](https://llvm.org/docs/LibFuzzer.html#options)
- [Fuzzing Rust Code (Rust RFC)](https://github.com/rust-lang/rfcs/blob/master/text/3164-fuzz-testing.md)
- [LLVM sanitizers](https://github.com/google/sanitizers)
