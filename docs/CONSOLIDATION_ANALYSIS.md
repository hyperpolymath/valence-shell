# Consolidation Analysis: MUST/SHOULD/COULD + Seam Sealing

**Version**: 0.7.0
**Date**: 2026-01-28
**Purpose**: Assess current state, identify polish opportunities, plan Phase 6

---

## Part 1: MUST/SHOULD/COULD Analysis

### What We Have Built (v0.7.0)

#### Layer 0: Formal Proofs (256+ theorems)
- ✅ Lean 4, Coq, Agda, Isabelle/HOL, Mizar, Z3
- ✅ Reversibility theorems (mkdir/rmdir, create/delete)
- ✅ Composition and equivalence theory
- ✅ Real filesystem model (not abstract lists)

#### Layer 1: Rust CLI Implementation
- ✅ Built-in operations (mkdir, rmdir, touch, rm)
- ✅ Undo/redo with operation history
- ✅ Transaction grouping
- ✅ External command execution
- ✅ PATH lookup and executable discovery
- ✅ Exit code tracking

#### Layer 2: Parser Infrastructure
- ✅ Command parsing (built-ins vs external)
- ✅ Argument validation
- ✅ Error handling

#### Layer 3: Documentation
- ✅ Architecture design (ARCHITECTURE.md)
- ✅ Lean 4 → Rust correspondence map (LEAN4_RUST_CORRESPONDENCE.md)
- ✅ Echidna integration plan (ECHIDNA_INTEGRATION.md)
- ✅ POSIX compliance roadmap (POSIX_COMPLIANCE.md)
- ✅ Implementation specs (PHASE6_M1_DESIGN.md)

#### Layer 4: Testing
- ✅ 13 unit tests (parser, external, state)
- ✅ 14 integration tests (filesystem operations)
- ✅ All tests passing (27/27)

#### Layer 5: Project Infrastructure
- ✅ STATE.scm tracking
- ✅ Git workflow
- ✅ Documentation structure

---

## MUST (Critical - Cannot Ship Without)

### Verification Gap Closure
- **MUST** prove Rust implementation matches Lean 4 specs
  - Currently: Documentation only, no formal correspondence
  - Risk: Implementation drift from specification
  - Timeline: 4-6 weeks

- **MUST** implement Echidna validation in CI/CD
  - Currently: Plan exists, not implemented
  - Risk: Manual verification doesn't scale
  - Timeline: 2-4 weeks

### Safety & Correctness
- **MUST** handle Ctrl+C (SIGINT) for external commands
  - Currently: Not implemented
  - Risk: Zombie processes, poor UX
  - Timeline: 1-2 days

- **MUST** implement proper error recovery
  - Currently: Basic error handling only
  - Risk: Crashes or inconsistent state
  - Timeline: 3-5 days

- **MUST** add `cd` as built-in
  - Currently: Not implemented (external cd doesn't work)
  - Risk: Shell is unusable for navigation
  - Timeline: 1 day

### Documentation Completeness
- **MUST** update CLAUDE.md with v0.7.0 state
  - Currently: Still shows v0.6.0
  - Risk: AI assistant confusion
  - Timeline: 30 minutes

- **MUST** add comprehensive examples
  - Currently: Basic demo only
  - Risk: Users don't know what's possible
  - Timeline: 2-3 days

---

## SHOULD (Important - Significantly Improves Quality)

### User Experience
- **SHOULD** improve error messages with suggestions
  - Currently: Basic "command not found"
  - Better: "command not found. Did you mean 'mkdir'?"
  - Timeline: 1 week

- **SHOULD** add command history with arrow keys
  - Currently: No readline integration
  - Better: Up/down arrow for history
  - Timeline: 2-3 days (use rustyline properly)

- **SHOULD** add tab completion
  - Currently: No completion
  - Better: Tab completes commands, paths
  - Timeline: 1 week

### Testing & Validation
- **SHOULD** add property-based tests with proptest
  - Currently: Only example tests
  - Better: Fuzz testing with random inputs
  - Timeline: 1 week

- **SHOULD** add benchmarks for performance tracking
  - Currently: Manual timing only
  - Better: criterion.rs benchmarks
  - Timeline: 2-3 days

- **SHOULD** test on multiple platforms (macOS, BSD)
  - Currently: Linux only
  - Better: Cross-platform verification
  - Timeline: 1 week

### Code Quality
- **SHOULD** refactor REPL complexity
  - Currently: execute_line() is getting large
  - Better: Modular command execution
  - Timeline: 2 days

- **SHOULD** add logging infrastructure
  - Currently: println!/eprintln! only
  - Better: tracing or log crate
  - Timeline: 1-2 days

- **SHOULD** document public APIs
  - Currently: Module-level docs only
  - Better: /// docs on all pub items
  - Timeline: 2-3 days

---

## COULD (Nice to Have - Polish)

### User Experience Enhancements
- **COULD** add colored output for errors/warnings
  - Currently: Basic colored crate usage
  - Better: Consistent color scheme
  - Timeline: 1 day

- **COULD** add shell prompt customization
  - Currently: Fixed "vsh>" prompt
  - Better: Configurable PS1-like prompt
  - Timeline: 2-3 days

- **COULD** add configuration file support
  - Currently: No config
  - Better: ~/.vshrc for settings
  - Timeline: 3-5 days

### Developer Experience
- **COULD** add cargo-deny for dependency auditing
  - Timeline: 1 day

- **COULD** add cargo-udeps for unused deps
  - Timeline: 1 day

- **COULD** set up GitHub Actions for CI
  - Currently: No CI for Rust tests
  - Timeline: 1 day

### Performance
- **COULD** optimize PATH lookup caching
  - Currently: Searches PATH every time
  - Better: Cache executable locations
  - Timeline: 2-3 days

- **COULD** parallelize integration tests
  - Currently: Sequential execution
  - Timeline: 1 day

---

## Part 2: Seam Sealing Analysis

### Layer 0 ↔ Layer 1: Proofs ↔ Implementation

**Current Seam**: Documentation only (LEAN4_RUST_CORRESPONDENCE.md)

**Gaps**:
1. No automated correspondence checking
2. Manual proofs not mechanized
3. Rust code can drift from spec

**Sealing Strategies**:

#### MUST: Echidna Property Tests
```rust
// Generated from Lean 4 theorems
#[test]
fn prop_mkdir_rmdir_reversible() {
    proptest!(|(path: ValidPath)| {
        let temp = tempdir()?;
        let state = ShellState::new(temp.path())?;

        // Assume preconditions
        if !mkdir_precondition(&path) {
            return Ok(());
        }

        // Snapshot
        let before = snapshot_fs(&temp);

        // mkdir then rmdir
        commands::mkdir(&mut state, &path, false)?;
        commands::rmdir(&mut state, &path, false)?;

        // Verify equivalence
        let after = snapshot_fs(&temp);
        assert_fs_equivalent!(before, after);
    });
}
```

**Timeline**: 1 week to set up infrastructure

#### SHOULD: Rust Type-Level Proofs
```rust
// Use typestate pattern to encode preconditions
struct ValidatedPath<Exists, Parent> {
    path: PathBuf,
    _marker: PhantomData<(Exists, Parent)>,
}

impl ShellState {
    fn mkdir(&mut self, path: ValidatedPath<DoesNotExist, ParentExists>) -> Result<Operation> {
        // Types guarantee preconditions!
    }
}
```

**Timeline**: 2-3 weeks (requires refactor)

#### COULD: Formal Extraction Pipeline
- Set up Coq → OCaml extraction
- Build FFI bridge to Rust
- Compare behavior against extracted code

**Timeline**: 4-6 weeks (longer-term project)

---

### Layer 1 ↔ Layer 2: Implementation ↔ Parser

**Current Seam**: Manual dispatch in execute_line()

**Gaps**:
1. Parser returns Command enum, REPL manually matches
2. No separation of parsing from execution
3. Built-ins hardcoded in match arms

**Sealing Strategies**:

#### SHOULD: Command Trait
```rust
pub trait ExecutableCommand {
    fn execute(&self, state: &mut ShellState) -> Result<()>;
    fn is_reversible(&self) -> bool;
    fn proof_reference(&self) -> Option<ProofReference>;
}

impl ExecutableCommand for Command {
    fn execute(&self, state: &mut ShellState) -> Result<()> {
        match self {
            Command::Mkdir { path } => commands::mkdir(state, path, false),
            Command::External { program, args } => external::execute_external(program, args),
            // ...
        }
    }
}

// In REPL:
let cmd = parser::parse_command(input)?;
cmd.execute(&mut state)?;
```

**Timeline**: 1-2 days

#### COULD: Plugin System
```rust
pub struct CommandRegistry {
    builtins: HashMap<String, Box<dyn ExecutableCommand>>,
    plugins: Vec<Box<dyn CommandPlugin>>,
}
```

**Timeline**: 1 week (overkill for now)

---

### Layer 1 ↔ Layer 4: Implementation ↔ Testing

**Current Seam**: Tests are separate from code

**Gaps**:
1. Integration tests duplicate setup logic
2. No test coverage tracking
3. Manual verification of Lean 4 correspondence

**Sealing Strategies**:

#### MUST: Test Fixtures
```rust
// tests/fixtures/mod.rs
pub fn test_sandbox() -> TempDir {
    let temp = tempdir().unwrap();
    // Common setup
    temp
}

pub fn test_state(root: &Path) -> ShellState {
    ShellState::new(root.to_str().unwrap()).unwrap()
}

// Reuse everywhere
#[test]
fn test_mkdir() {
    let temp = test_sandbox();
    let mut state = test_state(temp.path());
    // ...
}
```

**Timeline**: 1 day

#### SHOULD: Coverage Tracking
```bash
# Add to CI
cargo tarpaulin --out Html --output-dir coverage/
# Aim for 80%+ coverage
```

**Timeline**: 1 day

#### SHOULD: Mutation Testing
```bash
# Use cargo-mutants
cargo mutants
# Verify tests catch bugs
```

**Timeline**: 2 days

---

### Layer 3: Documentation Gaps

**Current State**: Comprehensive but scattered

**Gaps**:
1. No single "getting started" guide
2. Examples spread across multiple files
3. No troubleshooting guide
4. API docs missing

**Sealing Strategies**:

#### MUST: Getting Started Guide
```markdown
# docs/GETTING_STARTED.md
## Installation
## First Commands
## Common Patterns
## Next Steps
```

**Timeline**: 2-3 hours

#### SHOULD: Consolidate Examples
```markdown
# docs/EXAMPLES.md
All examples in one place:
- Basic operations
- Undo/redo workflows
- Transaction patterns
- External commands
- Error handling
```

**Timeline**: 1 day

#### SHOULD: API Documentation
```rust
/// Execute an external command via PATH lookup
///
/// # Arguments
/// * `program` - Command name or path
/// * `args` - Command arguments
///
/// # Returns
/// Exit code (0 for success)
///
/// # Errors
/// Returns error if command not found or execution fails
///
/// # Example
/// ```
/// let exit_code = execute_external("ls", &["-la".to_string()])?;
/// assert_eq!(exit_code, 0);
/// ```
pub fn execute_external(program: &str, args: &[String]) -> Result<i32>
```

**Timeline**: 2-3 days for all public APIs

---

### Cross-Layer: Build & Deployment

**Current Gaps**:
1. No CI/CD for Rust tests
2. No automated release process
3. No performance regression tracking
4. Echidna not integrated

**Sealing Strategies**:

#### MUST: GitHub Actions CI
```yaml
# .github/workflows/rust-ci.yml
name: Rust CI
on: [push, pull_request]
jobs:
  test:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: dtolnay/rust-toolchain@stable
      - run: cargo test --all-features
      - run: cargo clippy -- -D warnings
```

**Timeline**: 1 day

#### SHOULD: Automated Releases
```yaml
# .github/workflows/release.yml
# Trigger on version tags (v0.7.0, etc.)
# Build binaries for Linux/macOS/Windows
# Create GitHub release with artifacts
```

**Timeline**: 1-2 days

#### SHOULD: Performance Tracking
```yaml
# .github/workflows/benchmark.yml
# Run criterion benchmarks on main
# Track performance over time
# Alert on regressions
```

**Timeline**: 1 day

---

## Part 3: Prioritized Work Plan

### Phase 0: Critical Sealing (1-2 weeks)

**Week 1: Must-Fix Items**
- [ ] Day 1: Add `cd` builtin
- [ ] Day 1: Update CLAUDE.md to v0.7.0
- [ ] Day 2: SIGINT handling for external commands
- [ ] Day 2-3: Error recovery improvements
- [ ] Day 4: Test fixtures refactor
- [ ] Day 4: Getting Started guide
- [ ] Day 5: GitHub Actions CI setup

**Week 2: Quality Improvements**
- [ ] Day 1-2: Command trait pattern
- [ ] Day 3: Property-based tests setup
- [ ] Day 4: Benchmarking infrastructure
- [ ] Day 5: API documentation pass

**Deliverable**: v0.7.1 - Polished and sealed

---

### Phase 1: Echidna Integration (2-3 weeks)

Following ECHIDNA_INTEGRATION.md timeline:

**Week 1-2: Basic Integration**
- [ ] Install Echidna tooling
- [ ] Set up proof compilation checks
- [ ] Cross-validation across 6 systems
- [ ] CI/CD integration

**Week 3: Property Generation**
- [ ] Generate Rust property tests from Lean 4
- [ ] Integrate with cargo test
- [ ] Document correspondence

**Deliverable**: Automated verification in CI

---

### Phase 2: Phase 6 M2 - Redirections (2-3 weeks)

**Week 1: Design & Parser**
- [ ] Design redirection syntax
- [ ] Extend parser for `>`, `<`, `>>`, `2>`
- [ ] File descriptor management

**Week 2: Implementation**
- [ ] Output redirection implementation
- [ ] Input redirection implementation
- [ ] Error redirection implementation
- [ ] Tests

**Week 3: Polish**
- [ ] Documentation
- [ ] Examples
- [ ] Integration tests
- [ ] Performance tuning

**Deliverable**: v0.8.0 - Redirections working

---

### Phase 3: Phase 6 M3 - Pipelines (3-4 weeks)

**Week 1: Design**
- [ ] Pipeline semantics
- [ ] Process management
- [ ] stdio plumbing

**Week 2-3: Implementation**
- [ ] Pipeline parser
- [ ] Multi-process execution
- [ ] Buffer management
- [ ] Error handling

**Week 4: Polish**
- [ ] Tests
- [ ] Documentation
- [ ] Examples

**Deliverable**: v0.9.0 - Pipelines working

---

### Phase 4: Phase 6 M4 - Variables (2-3 weeks)

**Week 1: Design**
- [ ] Variable storage
- [ ] Expansion rules
- [ ] Special variables ($?, $@, etc.)

**Week 2: Implementation**
- [ ] Variable assignment
- [ ] Variable expansion in commands
- [ ] Tests

**Week 3: Polish**
- [ ] Documentation
- [ ] Examples

**Deliverable**: v0.10.0 - Variables working

---

## Timeline Summary

| Phase | Duration | Version | Key Deliverable |
|-------|----------|---------|-----------------|
| Phase 0: Sealing | 2 weeks | v0.7.1 | Polished foundation |
| Phase 1: Echidna | 3 weeks | v0.7.2 | Automated verification |
| Phase 2: M2 Redirections | 3 weeks | v0.8.0 | File I/O |
| Phase 3: M3 Pipelines | 4 weeks | v0.9.0 | Process composition |
| Phase 4: M4 Variables | 3 weeks | v0.10.0 | State management |

**Total**: ~15 weeks (3.5 months) to v0.10.0

---

## Success Criteria

### Phase 0 (Sealing)
- ✅ All critical MUSTs complete
- ✅ CI/CD running
- ✅ 80%+ test coverage
- ✅ Zero known crashes
- ✅ Documentation complete

### Phase 1 (Echidna)
- ✅ Proofs compile in CI
- ✅ Property tests generated
- ✅ Correspondence validated
- ✅ Build hash validated

### Phase 2-4 (M2-M4)
- ✅ Feature complete per milestone
- ✅ Tests passing
- ✅ Documentation updated
- ✅ Performance within targets
- ✅ No regressions

---

## Risk Mitigation

### Technical Risks
1. **Echidna integration complexity**
   - Mitigation: Start with basic checks, expand gradually
   - Fallback: Manual validation process

2. **Pipeline implementation complexity**
   - Mitigation: Study existing implementations (dash, toybox)
   - Fallback: Simplified pipeline (no background jobs)

3. **Performance regressions**
   - Mitigation: Benchmark before/after each change
   - Fallback: Revert and optimize

### Process Risks
1. **Scope creep**
   - Mitigation: Strict adherence to MUST/SHOULD/COULD
   - Fallback: Push features to next milestone

2. **Testing gaps**
   - Mitigation: Require tests for all new code
   - Fallback: Extended testing phase

---

**Author**: Jonathan D.A. Jewell <jonathan.jewell@open.ac.uk>
**License**: PMPL-1.0-or-later
**Date**: 2026-01-28
