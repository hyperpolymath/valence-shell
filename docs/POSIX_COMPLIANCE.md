# POSIX Compliance Roadmap - Valence Shell

**Goal**: Full POSIX shell compliance with formal verification at each increment

**Strategy**: Incremental milestones with useful functionality at each stage

**Current Status**: Phase 3 Complete (verified filesystem operations only)

---

## What is POSIX Shell Compliance?

**POSIX.1-2017 (IEEE Std 1003.1-2017)** defines two aspects:

1. **POSIX Shell Command Language** - Syntax, semantics, builtins
2. **POSIX System Interface** - Syscalls and C API

Valence Shell targets **both**, incrementally.

---

## Current State (v0.6.0)

### ✅ What IS POSIX-Compliant Now

**POSIX Syscall Interface** (proven in Coq, implemented in Rust/Elixir/Zig):
- `mkdir(path, mode)` - with EEXIST, ENOENT error handling
- `rmdir(path)` - with ENOTDIR, ENOTEMPTY handling
- `open(path, O_CREAT)` - file creation
- `unlink(path)` - file deletion
- Error codes: EEXIST, ENOENT, EACCES, ENOTDIR, ENOTEMPTY

**Verified Properties**:
- Reversibility: `rmdir(mkdir(p)) = identity`
- Composition: Sequences of operations reverse correctly
- Independence: Operations on different paths don't interfere
- **256+ theorems** across 6 proof systems

### ❌ What is NOT Compliant Yet

**POSIX Shell Features**:
- ✗ Command parser (no syntax tree)
- ✗ Pipelines (`cmd1 | cmd2`)
- ✗ Redirections (`>`, `<`, `>>`, `2>&1`)
- ✗ Variables (`$VAR`, `${VAR}`)
- ✗ Glob expansion (`*.txt`, `[a-z]`)
- ✗ Command substitution (`` `cmd` ``, `$(cmd)`)
- ✗ Arithmetic expansion (`$((1 + 2))`)
- ✗ Tilde expansion (`~/file`)
- ✗ Quote processing (`"..."`, `'...'`, `\`)
- ✗ Job control (`&`, `fg`, `bg`, `jobs`)
- ✗ Shell builtins (cd, export, alias, etc.)
- ✗ Control structures (if, while, for, case)
- ✗ Functions
- ✗ Shell scripts (.sh files)

---

## Incremental Roadmap (Option A)

### **Milestone 1: Simple Command Execution** (3-4 months)
**Goal**: Execute external commands with arguments

**Features**:
- Basic command parser (no special syntax)
- Execute external programs via `execve()`
- Argument passing (no expansion yet)
- Exit status handling
- PATH lookup

**Example**:
```bash
vsh> ls -la /tmp
vsh> mkdir foo
vsh> touch foo/bar.txt
```

**Verification**:
- Prove: Command parsing correctness
- Prove: execve() preserves invariants
- Test: Existing operations still work

**Deliverable**: Can run external commands with literals only

---

### **Milestone 2: Redirections** (2-3 months)
**Goal**: File descriptor manipulation

**Features**:
- Output redirection (`>`, `>>`)
- Input redirection (`<`)
- Error redirection (`2>`, `2>&1`)
- File descriptor duplication
- Prove: fd operations are reversible (undo restores original fds)

**Example**:
```bash
vsh> ls > files.txt
vsh> cat < files.txt
vsh> command 2> errors.log
```

**Verification**:
- Model: File descriptor table in Coq
- Prove: Redirection reversibility
- Prove: fd leak prevention

---

### **Milestone 3: Pipelines** (2-3 months)
**Goal**: Inter-process communication

**Features**:
- Pipe creation (`|`)
- Process spawning
- Wait for completion
- Exit status composition

**Example**:
```bash
vsh> ls -la | grep ".txt"
vsh> cat file.txt | wc -l
```

**Verification**:
- Prove: Pipe composition correctness
- Prove: Resource cleanup guarantees
- Prove: No data loss in pipes

---

### **Milestone 4: Variables** (3-4 months)
**Goal**: Environment and shell variables

**Features**:
- Variable assignment (`VAR=value`)
- Variable expansion (`$VAR`, `${VAR}`)
- Environment variables (`export`, `env`)
- Special variables (`$?`, `$#`, `$@`, `$$`)

**Example**:
```bash
vsh> NAME="world"
vsh> echo "Hello $NAME"
vsh> export PATH="/usr/bin:$PATH"
```

**Verification**:
- Model: Environment as map in Coq
- Prove: Variable substitution correctness
- Prove: export visibility semantics

---

### **Milestone 5: Glob Expansion** (2 months)
**Goal**: Filename pattern matching

**Features**:
- `*` (match any string)
- `?` (match single char)
- `[...]` (character class)
- `[!...]` (negated class)

**Example**:
```bash
vsh> ls *.txt
vsh> rm test-?.log
vsh> cat [A-Z]*.md
```

**Verification**:
- Prove: Glob expansion matches POSIX spec
- Prove: No unintended file matches
- Prove: Handles special chars correctly

---

### **Milestone 6: Quote Processing** (2 months)
**Goal**: String parsing with escapes

**Features**:
- Double quotes (`"..."` - expansion allowed)
- Single quotes (`'...'` - literal)
- Backslash escapes (`\n`, `\t`, `\\`)
- Quote nesting rules

**Example**:
```bash
vsh> echo "Hello $NAME"
vsh> echo 'Literal $NAME'
vsh> echo "Quote: \"nested\""
```

**Verification**:
- Prove: Parser handles all quote combinations
- Prove: No injection vulnerabilities
- Prove: Escape sequences correct

---

### **Milestone 7: Command Substitution** (2-3 months)
**Goal**: Nested command execution

**Features**:
- Backticks (`` `cmd` ``)
- Modern syntax (`$(cmd)`)
- Nested substitution
- Exit status propagation

**Example**:
```bash
vsh> echo "Files: $(ls)"
vsh> date=$(date +%Y-%m-%d)
```

**Verification**:
- Prove: Substitution precedence rules
- Prove: No code injection
- Prove: Resource limits enforced

---

### **Milestone 8: Arithmetic** (1-2 months)
**Goal**: Integer math in shell

**Features**:
- Arithmetic expansion (`$((expr))`)
- Operators: `+`, `-`, `*`, `/`, `%`
- Comparisons: `<`, `>`, `<=`, `>=`, `==`, `!=`
- Variables in expressions

**Example**:
```bash
vsh> echo $((2 + 3))
vsh> i=$((i + 1))
```

**Verification**:
- Prove: Arithmetic evaluation correctness
- Prove: Overflow handling
- Prove: Division by zero safety

---

### **Milestone 9: Control Structures** (4-6 months)
**Goal**: Conditional execution and loops

**Features**:
- `if/then/else/fi`
- `while/do/done`
- `for/in/do/done`
- `case/esac`
- Test conditions (`[`, `[[`, `test`)

**Example**:
```bash
vsh> if [ -f file.txt ]; then
       cat file.txt
     fi

vsh> for f in *.txt; do
       echo "Processing $f"
     done
```

**Verification**:
- Prove: Control flow correctness
- Prove: Loop termination guarantees
- Prove: Condition evaluation matches POSIX

---

### **Milestone 10: Job Control** (3-4 months)
**Goal**: Background processes and signals

**Features**:
- Background execution (`&`)
- Job list (`jobs`)
- Foreground (`fg`)
- Background (`bg`)
- Signal handling (Ctrl+C, Ctrl+Z)

**Example**:
```bash
vsh> long-running-cmd &
[1] 12345
vsh> jobs
[1]+  Running    long-running-cmd &
vsh> fg %1
```

**Verification**:
- Prove: Process group semantics
- Prove: Signal delivery correctness
- Prove: No zombie processes

---

### **Milestone 11: Shell Builtins** (4-6 months)
**Goal**: Internal commands

**Features**:
- Directory: `cd`, `pwd`, `pushd`, `popd`
- Variables: `export`, `unset`, `set`, `readonly`
- Control: `exit`, `return`, `break`, `continue`
- I/O: `echo`, `printf`, `read`
- Utilities: `test`, `[`, `[[`, `true`, `false`
- Jobs: `fg`, `bg`, `jobs`, `kill`, `wait`
- Aliases: `alias`, `unalias`
- Shell: `exec`, `eval`, `source`, `.`

**Verification per builtin**:
- Prove: Matches POSIX specification
- Prove: Side effects are reversible (where applicable)

---

### **Milestone 12: Functions** (2-3 months)
**Goal**: User-defined commands

**Features**:
- Function definition
- Parameter passing (`$1`, `$2`, ...)
- Local variables
- Return values
- Recursion limits

**Example**:
```bash
vsh> greet() {
       echo "Hello $1"
     }
vsh> greet World
```

**Verification**:
- Prove: Function call/return correctness
- Prove: Variable scope rules
- Prove: Stack overflow prevention

---

### **Milestone 13: Shell Scripts** (3-4 months)
**Goal**: Execute .sh files

**Features**:
- Shebang handling (`#!/usr/bin/env vsh`)
- Script parsing
- Source command (`.`, `source`)
- Command-line arguments to scripts

**Example**:
```bash
#!/usr/bin/env vsh
# script.sh
for arg in "$@"; do
  echo "Arg: $arg"
done
```

**Verification**:
- Prove: Script execution matches interactive mode
- Prove: Argument passing correctness
- Prove: File permissions checked

---

### **Milestone 14: Advanced Features** (6-12 months)
**Goal**: Complete POSIX compliance

**Features**:
- Tilde expansion (`~`, `~user`)
- Brace expansion (`{a,b,c}`)
- Process substitution (`<(cmd)`, `>(cmd)`)
- Coprocesses
- Arrays (if beyond POSIX)
- Associative arrays
- Extended test (`[[ ]]`)
- Here documents (`<<EOF`)
- Here strings (`<<<`)

---

## Verification Strategy Per Milestone

Each milestone follows this pattern:

### 1. **Specification Phase**
- Write formal semantics in Coq
- Define abstract syntax tree (AST)
- Model runtime state changes

### 2. **Proof Phase**
- Prove correctness theorems
- Cross-validate in 2+ proof systems
- Ensure composition with existing theorems

### 3. **Extraction Phase**
- Extract verified code to OCaml
- Prove correspondence to Coq model
- Integrate with FFI layer

### 4. **Testing Phase**
- POSIX conformance tests
- Comparison with bash behavior
- Fuzzing for edge cases

### 5. **Integration Phase**
- Merge with main codebase
- Update all proof systems
- Document verification boundaries

---

## Timeline Summary

| Milestone | Duration | Cumulative | Functionality |
|-----------|----------|-----------|---------------|
| 1. Simple Commands | 3-4 mo | 3-4 mo | Run external programs |
| 2. Redirections | 2-3 mo | 5-7 mo | File I/O control |
| 3. Pipelines | 2-3 mo | 7-10 mo | IPC between commands |
| 4. Variables | 3-4 mo | 10-14 mo | State management |
| 5. Glob Expansion | 2 mo | 12-16 mo | Pattern matching |
| 6. Quote Processing | 2 mo | 14-18 mo | String handling |
| 7. Command Subst | 2-3 mo | 16-21 mo | Nested execution |
| 8. Arithmetic | 1-2 mo | 17-23 mo | Math in shell |
| 9. Control Structures | 4-6 mo | 21-29 mo | if/while/for |
| 10. Job Control | 3-4 mo | 24-33 mo | Background jobs |
| 11. Shell Builtins | 4-6 mo | 28-39 mo | Internal commands |
| 12. Functions | 2-3 mo | 30-42 mo | User-defined cmds |
| 13. Shell Scripts | 3-4 mo | 33-46 mo | .sh file execution |
| 14. Advanced | 6-12 mo | 39-58 mo | Full POSIX |

**Total**: ~3-5 years for full POSIX compliance with verification

---

## Interim Deliverables

Each milestone produces a **usable shell** with incrementally more features:

- **After M1**: Basic shell (better than `sh` from 1970s)
- **After M3**: Useful for simple scripts
- **After M6**: Most common shell patterns work
- **After M9**: Feature-complete for most users
- **After M14**: Full POSIX compatibility

---

## Dependencies

### Prerequisites for Each Milestone
- Coq 8.18+ (proof development)
- OCaml 5.0+ (extraction target)
- Rust 1.75+ (CLI/FFI implementation)
- 6 proof assistants (cross-validation)

### Parallel Work Streams
While working on shell features (Milestones 1-14), these run in parallel:

1. **Extraction Gap Closure** (ongoing)
   - Verify Coq → OCaml correspondence
   - FFI layer verification

2. **Performance Optimization** (after M6)
   - Once syntax is stable
   - Target: 5ms cold start

3. **Security Audit** (after M11)
   - External review
   - Fuzzing campaigns

4. **RMO/GDPR** (parallel to M7-10)
   - Secure deletion proofs
   - MAA framework extensions

---

## Verification Boundaries

### What WILL Be Proven
- Command syntax parsing correctness
- Execution semantics match POSIX spec
- Filesystem operations preserve invariants
- No resource leaks (fds, processes, memory)
- Security properties (no injection, no privilege escalation)

### What Will NOT Be Proven
- External program behavior (unverified binaries)
- Operating system kernel correctness
- Hardware correctness
- Timing/performance characteristics
- Cryptographic primitives (use verified libraries)

---

## Success Criteria

### Per Milestone
- ✅ All proofs compile in 6 systems
- ✅ Extraction produces working code
- ✅ POSIX conformance tests pass
- ✅ No regression in previous milestones
- ✅ Documentation complete

### Final (M14)
- ✅ Passes POSIX shell test suite
- ✅ Runs real-world shell scripts
- ✅ Performance competitive with bash
- ✅ External security audit passed
- ✅ Production deployment ready

---

## Related Documents

- `README.adoc` - Project overview
- `STATE.scm` - Current project state
- `ECOSYSTEM.scm` - Ecosystem relationships
- `proofs/README.md` - Proof documentation
- `docs/EXTRACTION_STRATEGY.md` - Extraction gap closure plan
- `.claude/plans/magical-yawning-canyon.md` - Implementation plan

---

**Status**: Roadmap approved, starting with immediate fixes and M1 planning

**Last Updated**: 2026-01-28

**Author**: Jonathan D.A. Jewell <jonathan.jewell@open.ac.uk>
