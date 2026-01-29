# Valence Shell: Roadmap to v1.0.0

**Current Version**: 0.10.0 (Command Substitution)
**Target**: v1.0.0 (Production-Ready Shell)
**Date**: 2026-01-29

---

## Current Status

### ✅ Implemented (v0.1.0 - v0.10.0)

| Feature | Version | Status |
|---------|---------|--------|
| Filesystem Operations | v0.1.0 | ✅ `mkdir`, `rmdir`, `touch`, `rm` |
| Undo/Redo | v0.2.0 | ✅ Reversible operations |
| History | v0.3.0 | ✅ Command history tracking |
| Transactions | v0.4.0 | ✅ `begin`, `commit`, `rollback` |
| Proof References | v0.5.0 | ✅ 256 theorems linked |
| External Commands | v0.7.0 | ✅ Fork/exec with PATH |
| I/O Redirections | v0.8.0 | ✅ `>`, `>>`, `<`, `2>`, `2>&1` |
| Pipelines | v0.8.0 | ✅ Multi-stage `cmd1 | cmd2 | cmd3` |
| Variables | v0.9.0 | ✅ `VAR=value`, `$VAR`, `${VAR}`, special vars |
| Quote Parsing | v0.9.0 | ✅ Single/double quotes, escaping |
| Command Substitution | v0.10.0 | ✅ `$(cmd)`, `` `cmd` `` |
| Process Sub Parsing | v0.10.0 | ✅ `<(cmd)`, `>(cmd)` (execution deferred) |

### 🚧 In Progress

| Feature | Version | Status |
|---------|---------|--------|
| Process Substitution Execution | v0.11.0 | 🚧 Parsing done, FIFO execution pending |

---

## Roadmap to v1.0.0

### Phase 6 Completion: Shell Features

#### M7: Process Substitution Execution (v0.11.0)
**Timeline**: 3-4 days
**Complexity**: High (FIFO management, background processes)

**Requirements**:
- [ ] FIFO (named pipe) creation using `mkfifo()` syscall
- [ ] Background process spawning with redirected file descriptors
- [ ] Process management (track PIDs, wait for completion)
- [ ] FIFO cleanup (remove after main command completes)
- [ ] Error handling (deadlocks, broken pipes, process failures)
- [ ] Platform support: Linux/macOS only (Windows has no FIFOs)

**Success Criteria**:
- `diff <(ls dir1) <(ls dir2)` executes correctly
- `tee >(wc -l) >(grep pattern)` works
- FIFOs cleaned up even on errors
- No zombie processes or resource leaks

---

#### M8: Arithmetic Expansion (v0.12.0)
**Timeline**: 2-3 days
**Complexity**: Medium (expression parsing, overflow handling)

**Requirements**:
- [ ] Parse `$((expr))` syntax
- [ ] Evaluate arithmetic expressions: `+`, `-`, `*`, `/`, `%`, `**`
- [ ] Handle precedence and parentheses
- [ ] Bitwise operators: `&`, `|`, `^`, `~`, `<<`, `>>`
- [ ] Comparison operators: `<`, `>`, `<=`, `>=`, `==`, `!=`
- [ ] Variable expansion in expressions: `$((x + y))`
- [ ] Overflow detection and safe math
- [ ] Integer-only (POSIX behavior)

**Examples**:
```bash
echo $((2 + 3))        # 5
echo $((10 / 3))       # 3 (integer division)
VAR=5; echo $((VAR * 2))  # 10
```

---

#### M9: Here Documents (v0.13.0)
**Timeline**: 2 days
**Complexity**: Low (input buffering)

**Requirements**:
- [ ] Parse `<<EOF` syntax
- [ ] Collect lines until delimiter
- [ ] Feed to command stdin
- [ ] Variable expansion in here-docs (unless `<<'EOF'`)
- [ ] No expansion with quoted delimiter: `<<'EOF'`

**Examples**:
```bash
cat <<EOF
Hello $USER
Current directory: $(pwd)
EOF

cat <<'EOF'
Literal: $USER and $(pwd)
EOF
```

---

#### M10: Job Control (v0.14.0)
**Timeline**: 4-5 days
**Complexity**: High (process groups, signals)

**Requirements**:
- [ ] Background jobs: `cmd &`
- [ ] Job list: `jobs`
- [ ] Foreground: `fg %1`
- [ ] Background: `bg %1`
- [ ] Process group management
- [ ] Signal handling (SIGTSTP, SIGCONT, SIGCHLD)
- [ ] Terminal control (tcsetpgrp)

**Deferred** (not required for v1.0):
- Job control on Windows (no POSIX signals)
- Advanced job features (disown, wait)

---

### Phase 7: Scripting Support

#### M11: Conditionals (v0.15.0)
**Timeline**: 3-4 days
**Complexity**: Medium (AST for conditionals)

**Requirements**:
- [ ] `if` / `then` / `elif` / `else` / `fi`
- [ ] Exit code checking: `if cmd; then ...`
- [ ] Test command: `if [ -f file ]; then ...`
- [ ] Built-in `test` / `[` command
- [ ] String comparisons: `=`, `!=`
- [ ] Integer comparisons: `-eq`, `-ne`, `-lt`, `-le`, `-gt`, `-ge`
- [ ] File tests: `-f`, `-d`, `-e`, `-r`, `-w`, `-x`
- [ ] Boolean operators: `-a` (and), `-o` (or), `!` (not)

**Examples**:
```bash
if [ -f config.txt ]; then
    echo "Config exists"
else
    echo "No config"
fi
```

---

#### M12: Loops (v0.16.0)
**Timeline**: 3 days
**Complexity**: Medium (control flow)

**Requirements**:
- [ ] `for` loops: `for var in list; do ...; done`
- [ ] `while` loops: `while condition; do ...; done`
- [ ] `until` loops: `until condition; do ...; done`
- [ ] `break` and `continue`
- [ ] C-style for: `for ((i=0; i<10; i++)); do ...; done`

**Examples**:
```bash
for file in *.txt; do
    echo "Processing $file"
done

i=0
while [ $i -lt 5 ]; do
    echo $i
    i=$((i + 1))
done
```

---

#### M13: Functions (v0.17.0)
**Timeline**: 3-4 days
**Complexity**: Medium (scope, local variables)

**Requirements**:
- [ ] Function definition: `func() { ...; }`
- [ ] Function calls
- [ ] Positional parameters: `$1`, `$2`, etc.
- [ ] `local` keyword for function-scoped variables
- [ ] `return` statement with exit code
- [ ] `$@` and `$*` for all arguments

**Examples**:
```bash
greet() {
    local name=$1
    echo "Hello, $name!"
}

greet "World"
```

---

### Phase 8: MAA Framework Integration

#### M14: Provenance Tracking (v0.18.0)
**Timeline**: 5-6 days
**Complexity**: High (cryptographic hashing, audit trails)

**Requirements**:
- [ ] Hash-chained audit log for all operations
- [ ] Operation metadata: user, timestamp, command, exit code
- [ ] Before/after filesystem state hashing
- [ ] Tamper-evident log storage
- [ ] Log verification command
- [ ] Integration with proven's `SafeProvenance` (Idris2)

**MAA Guarantees**:
- Every operation creates an audit entry
- Entries are cryptographically chained (hash of previous)
- Tampering with any entry breaks the chain
- GDPR compliance: immutable proof of data operations

---

#### M15: Capability-Based Security (v0.19.0)
**Timeline**: 4-5 days
**Complexity**: High (permission modeling)

**Requirements**:
- [ ] Capability tokens for file access
- [ ] Least-privilege enforcement
- [ ] Delegation and revocation
- [ ] Integration with proven's `SafeCapability` (Idris2)

**Deferred** (post-v1.0):
- Network capabilities
- Time-limited capabilities

---

### Phase 9: Production Readiness

#### M16: Error Handling & Robustness (v0.20.0)
**Timeline**: 3-4 days

**Requirements**:
- [ ] Comprehensive error messages
- [ ] Graceful degradation (missing commands)
- [ ] Resource limit handling (max file descriptors, memory)
- [ ] SIGINT handling (Ctrl+C in external commands)
- [ ] SIGTERM handling (graceful shutdown)
- [ ] Cleanup on abnormal exit
- [ ] Fuzzing integration (OSS-Fuzz or ClusterFuzzLite)

---

#### M17: Configuration & Customization (v0.21.0)
**Timeline**: 2-3 days

**Requirements**:
- [ ] Config file: `~/.vshrc`
- [ ] Prompt customization
- [ ] Aliases
- [ ] Environment variable persistence
- [ ] History file: `~/.vsh_history`
- [ ] History size limits

---

#### M18: Documentation & Examples (v0.22.0)
**Timeline**: 3-4 days

**Requirements**:
- [ ] User manual (AsciiDoc)
- [ ] Tutorial: Getting Started
- [ ] Example scripts
- [ ] Proof reference guide
- [ ] MAA framework guide
- [ ] API documentation (rustdoc)
- [ ] Man page: `man vsh`

---

#### M19: Performance Optimization (v0.23.0)
**Timeline**: 2-3 days

**Requirements**:
- [ ] Benchmarking suite
- [ ] Command lookup caching
- [ ] Fork overhead reduction
- [ ] Memory usage optimization
- [ ] Startup time optimization (< 50ms)

---

#### M20: v1.0.0 Release Candidate (v0.24.0)
**Timeline**: 1 week

**Requirements**:
- [ ] All critical features complete
- [ ] All tests passing (unit, integration, property)
- [ ] Security audit (manual + automated)
- [ ] Performance regression tests
- [ ] User acceptance testing
- [ ] Release notes
- [ ] Migration guide (from bash/zsh)

---

## v1.0.0 Release Criteria

### Must-Have Features
- ✅ All Phase 6 milestones (shell features)
- ✅ All Phase 7 milestones (scripting)
- ✅ MAA Framework (provenance tracking)
- ✅ Error handling and robustness
- ✅ Documentation complete

### Quality Gates
- [ ] 100% of critical tests passing
- [ ] No known critical bugs
- [ ] No resource leaks (valgrind clean)
- [ ] Fuzzing: 24+ hours without crashes
- [ ] Startup time < 50ms (cold start)
- [ ] Memory usage < 10MB (idle)

### Platform Support
- ✅ Linux (x86_64, aarch64)
- ✅ macOS (Intel, Apple Silicon)
- ⚠️ Windows: Limited (no FIFOs, no job control)

### Proof Coverage
- [ ] All reversible operations proven in 6 systems
- [ ] Extraction verified (Coq → OCaml, Lean → Rust correspondence)
- [ ] MAA framework mathematically verified

---

## Timeline Estimate

| Phase | Milestones | Estimated Time |
|-------|-----------|----------------|
| Phase 6 (Shell Features) | M7-M10 | 11-14 days |
| Phase 7 (Scripting) | M11-M13 | 9-11 days |
| Phase 8 (MAA Framework) | M14-M15 | 9-11 days |
| Phase 9 (Production) | M16-M20 | 11-14 days |
| **Total** | **M7-M20** | **40-50 days** |

**Target v1.0.0 Release**: ~6-8 weeks from now

---

## Proven Library Integration

### Applicable Modules (Idris2 only)

| Proven Module | Use Case | Integration Point |
|---------------|----------|-------------------|
| `SafeFile.idr` | File operations | Replace Rust file I/O with proven calls |
| `SafePath.idr` | Path manipulation | Validate paths before operations |
| `SafeStateMachine.idr` | Shell state transitions | Model REPL state machine |
| `SafeProvenance.idr` | MAA audit trails | Hash-chained operation log |
| `SafeCapability.idr` | Permission modeling | Capability-based security |

### Integration Strategy

1. **Compile Idris2 modules** to shared library
2. **Create minimal FFI wrapper** in valence-shell Rust code
3. **Ignore all bindings directories** in proven repo (contaminated)
4. **Direct Zig FFI if needed**, or use Idris2's native FFI

---

## Post-v1.0 Features (v1.1+)

- Command-line editing (readline-like)
- Tab completion
- Syntax highlighting (via rustyline)
- vi/emacs keybindings
- Advanced job control (disown, wait)
- Shell scripts with shebang: `#!/usr/bin/vsh`
- Plugin system
- Remote shell execution (SSH integration)

---

## Success Metrics for v1.0.0

- [ ] Can run basic shell scripts (bash compatibility: 80%+)
- [ ] Undo works for all reversible operations
- [ ] MAA audit log verifiable
- [ ] Zero known security vulnerabilities
- [ ] Production deployment by 1+ user

---

**Co-Authored-By**: Claude Sonnet 4.5 <noreply@anthropic.com>
