<!--
SPDX-License-Identifier: MPL-2.0
Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
-->
# Valence Shell: Architecture & Process Diagrams

**Version**: 0.15.0 (pre-v1.0)
**Date**: 2026-01-29
**Status**: Comprehensive System Documentation

---

## Part 1: System Architecture (Anatomy)

### High-Level Architecture

```
┌─────────────────────────────────────────────────────────────────────┐
│                      VALENCE SHELL v1.0                             │
│                  Formally Verified Shell System                      │
└─────────────────────────────────────────────────────────────────────┘
                                │
                ┌───────────────┴───────────────┐
                │                               │
        ┌───────▼────────┐            ┌────────▼────────┐
        │  USER LAYER    │            │  PROOF LAYER    │
        │  (CLI/REPL)    │            │  (Verification) │
        └───────┬────────┘            └────────┬────────┘
                │                               │
        ┌───────▼─────────────────────────────▼────────┐
        │         CORE SHELL ENGINE                    │
        │  ┌──────────┐  ┌──────────┐  ┌──────────┐  │
        │  │  Parser  │  │ Executor │  │  State   │  │
        │  │  (Rust)  │  │  (Rust)  │  │  (Rust)  │  │
        │  └────┬─────┘  └────┬─────┘  └────┬─────┘  │
        │       │             │             │         │
        │  ┌────▼─────────────▼─────────────▼─────┐  │
        │  │      Operation History & Undo/Redo   │  │
        │  │     (Reversibility Guarantees)       │  │
        │  └──────────────────┬───────────────────┘  │
        └─────────────────────┼───────────────────────┘
                              │
        ┌─────────────────────▼────────────────────────┐
        │         SYSTEM INTERFACE LAYER               │
        │  ┌──────────┐  ┌──────────┐  ┌──────────┐  │
        │  │   POSIX  │  │   IPC    │  │  Audit   │  │
        │  │  Syscalls│  │(Optional)│  │   Log    │  │
        │  └────┬─────┘  └────┬─────┘  └────┬─────┘  │
        └───────┼─────────────┼─────────────┼─────────┘
                │             │             │
        ┌───────▼─────────────▼─────────────▼─────────┐
        │        OPERATING SYSTEM (Linux/Unix)        │
        └─────────────────────────────────────────────┘
```

### Component Architecture (Detailed)

```
┌─────────────────────────────────────────────────────────────────────┐
│                     VALENCE SHELL COMPONENTS                         │
├─────────────────────────────────────────────────────────────────────┤
│                                                                      │
│  ┌────────────────────────────────────────────────────────────┐    │
│  │  1. REPL (Read-Eval-Print Loop)                            │    │
│  │     ┌──────────────────────────────────────┐               │    │
│  │     │  Reedline (Input/History/Completion) │               │    │
│  │     │  - Tab completion                    │               │    │
│  │     │  - Command history                   │               │    │
│  │     │  - Syntax highlighting               │               │    │
│  │     └──────────────┬───────────────────────┘               │    │
│  └────────────────────┼────────────────────────────────────────┘    │
│                       │                                              │
│  ┌────────────────────▼────────────────────────────────────────┐    │
│  │  2. PARSER (Tokenizer + AST Builder)                        │    │
│  │     ┌────────────┐  ┌────────────┐  ┌────────────┐         │    │
│  │     │ Tokenizer  │→ │   Quote    │→ │    AST     │         │    │
│  │     │   (lexer)  │  │  Processor │  │  Builder   │         │    │
│  │     └────────────┘  └────────────┘  └──────┬─────┘         │    │
│  │                                             │               │    │
│  │     Handles: quotes, globs, redirects, pipes, vars         │    │
│  └─────────────────────────────────────────────┼───────────────┘    │
│                                                 │                    │
│  ┌─────────────────────────────────────────────▼───────────────┐    │
│  │  3. EXPANDER (Variable/Command/Glob Expansion)              │    │
│  │     ┌──────────┐  ┌───────────┐  ┌──────────┐              │    │
│  │     │ Variable │  │  Command  │  │   Glob   │              │    │
│  │     │Expansion │  │Substituti │  │ Expansion│              │    │
│  │     │ ($VAR)   │  │on $(cmd)  │  │  (*.txt) │              │    │
│  │     └────┬─────┘  └─────┬─────┘  └────┬─────┘              │    │
│  └──────────┼───────────────┼─────────────┼────────────────────┘    │
│             └───────────────┴─────────────┘                         │
│                             │                                        │
│  ┌──────────────────────────▼──────────────────────────────────┐    │
│  │  4. EXECUTOR (Command Execution Engine)                     │    │
│  │     ┌───────────┐  ┌────────────┐  ┌────────────┐          │    │
│  │     │  Built-in │  │  External  │  │  Pipeline  │          │    │
│  │     │ Commands  │  │  Commands  │  │  Executor  │          │    │
│  │     │(mkdir/cd) │  │(PATH lookup│  │  (|pipes)  │          │    │
│  │     └─────┬─────┘  └──────┬─────┘  └──────┬─────┘          │    │
│  └───────────┼────────────────┼───────────────┼────────────────┘    │
│              │                │               │                     │
│  ┌───────────▼────────────────▼───────────────▼────────────────┐    │
│  │  5. STATE MANAGER (Undo/Redo/History)                       │    │
│  │     ┌──────────────┐  ┌──────────────┐  ┌──────────────┐   │    │
│  │     │  Operation   │  │  Undo Stack  │  │  Redo Stack  │   │    │
│  │     │   History    │  │   (LIFO)     │  │   (LIFO)     │   │    │
│  │     └──────┬───────┘  └──────┬───────┘  └──────┬───────┘   │    │
│  │            │                  │                  │           │    │
│  │     ┌──────▼──────────────────▼──────────────────▼───────┐  │    │
│  │     │  State Persistence (JSON)                          │  │    │
│  │     │  ~/.vsh_state.json                                 │  │    │
│  │     └────────────────────────────────────────────────────┘  │    │
│  └─────────────────────────────────────────────────────────────┘    │
│                                                                      │
│  ┌──────────────────────────────────────────────────────────────┐   │
│  │  6. VERIFICATION LAYER (Formal Proofs)                       │   │
│  │     ┌──────────┐  ┌────────┐  ┌────────┐  ┌──────────┐     │   │
│  │     │  Lean 4  │  │  Coq   │  │  Agda  │  │ Isabelle │     │   │
│  │     │ Theorems │  │Theorems│  │Theorems│  │ Theorems │     │   │
│  │     └────┬─────┘  └────┬───┘  └────┬───┘  └────┬─────┘     │   │
│  │          │             │           │           │            │   │
│  │     ┌────▼─────────────▼───────────▼───────────▼────────┐   │   │
│  │     │  Correspondence Proofs (Rust ↔ Lean 4)           │   │   │
│  │     │  Property-Based Tests (Echidna/PropTest)          │   │   │
│  │     └───────────────────────────────────────────────────┘   │   │
│  └──────────────────────────────────────────────────────────────┘   │
│                                                                      │
└──────────────────────────────────────────────────────────────────────┘
```

### Module Dependency Graph

```
                    ┌──────────┐
                    │   main   │
                    │ (binary) │
                    └────┬─────┘
                         │
              ┌──────────▼──────────┐
              │        repl         │
              │ (interactive loop)  │
              └──────────┬──────────┘
                         │
         ┌───────────────┼───────────────┐
         │               │               │
    ┌────▼────┐    ┌────▼────┐    ┌────▼────┐
    │ parser  │    │executor │    │  state  │
    │         │◄───┤         │◄───┤         │
    └────┬────┘    └────┬────┘    └────┬────┘
         │              │              │
    ┌────▼────┐    ┌────▼────┐    ┌────▼────┐
    │ quotes  │    │external │    │history  │
    └─────────┘    └────┬────┘    └─────────┘
                        │
                   ┌────▼────┐
                   │  glob   │
                   └─────────┘

Legend:
  ─► : depends on
  ◄─ : used by
```

---

## Part 2: Process Flow (Physiology)

### Command Execution Flow

```
┌─────────────────────────────────────────────────────────────────┐
│                  COMMAND EXECUTION PIPELINE                     │
└─────────────────────────────────────────────────────────────────┘

USER INPUT: echo "Hello $USER" > output.txt
    │
    ▼
┌─────────────────┐
│  1. TOKENIZE    │  Split into tokens, handle quotes
│     (parser.rs) │  Output: [echo, "Hello $USER", >, output.txt]
└────────┬────────┘
         │
         ▼
┌─────────────────┐
│  2. PARSE       │  Build AST, identify command type
│     (parser.rs) │  Output: External { program: echo, args: [...],
└────────┬────────┘         redirects: [Output{file: output.txt}] }
         │
         ▼
┌─────────────────┐
│  3. EXPAND      │  Process $VAR, $(cmd), *.txt, quotes
│ (parser.rs +    │  Variables: $USER → "hyper"
│  glob.rs +      │  Globs: (none in quotes)
│  quotes.rs)     │  Quotes: Remove quotes, preserve literal
└────────┬────────┘  Output: [echo, Hello hyper]
         │
         ▼
┌─────────────────┐
│  4. SETUP       │  Open files for redirections
│ REDIRECTIONS    │  Create: output.txt (truncate mode)
│(redirection.rs) │  Track: Original state for undo
└────────┬────────┘
         │
         ▼
┌─────────────────┐
│  5. EXECUTE     │  PATH lookup: /usr/bin/echo
│  (external.rs   │  Fork/exec with redirected stdout
│   or            │  Wait for completion
│   commands.rs)  │  Capture exit code: 0
└────────┬────────┘
         │
         ▼
┌─────────────────┐
│  6. RECORD      │  Save operation to history
│  (state.rs)     │  Operation: FileTruncated
└────────┬────────┘  Path: output.txt
         │           Undo data: (original content)
         ▼           Proof ref: write_file_reversible
┌─────────────────┐
│  7. UPDATE      │  Update shell state
│    STATE        │  last_exit_code = 0
│  (state.rs)     │  Persist to ~/.vsh_state.json
└────────┬────────┘
         │
         ▼
    RESULT: Success (exit code 0)
            output.txt contains "Hello hyper\n"
```

### Undo/Redo Flow

```
┌─────────────────────────────────────────────────────────────────┐
│                     UNDO/REDO MECHANISM                         │
└─────────────────────────────────────────────────────────────────┘

STATE AFTER OPERATIONS:
  History: [mkdir(foo), touch(foo/bar.txt), rm(foo/bar.txt)]
  Redo Stack: []

USER: undo
    │
    ▼
┌─────────────────┐
│  1. POP FROM    │  Last operation: rm(foo/bar.txt)
│     HISTORY     │  Inverse: CreateFile
└────────┬────────┘
         │
         ▼
┌─────────────────┐
│  2. COMPUTE     │  Operation: DeleteFile
│    INVERSE      │  Inverse: CreateFile
│  (state.rs)     │  Undo data: (original content: "...")
└────────┬────────┘
         │
         ▼
┌─────────────────┐
│  3. EXECUTE     │  Recreate: foo/bar.txt
│    INVERSE      │  Restore content from undo_data
│ (commands.rs)   │  Set permissions, metadata
└────────┬────────┘
         │
         ▼
┌─────────────────┐
│  4. PUSH TO     │  Store for redo: rm(foo/bar.txt)
│   REDO STACK    │
└────────┬────────┘
         │
         ▼
┌─────────────────┐
│  5. MARK AS     │  Set undone flag on operation
│     UNDONE      │  Update history: operation.undone = true
│  (state.rs)     │
└────────┬────────┘
         │
         ▼
    RESULT: File restored
            History: [mkdir(foo), touch(foo/bar.txt), rm(foo/bar.txt)✗]
            Redo Stack: [rm(foo/bar.txt)]
```

### Pipeline Execution Flow

```
┌─────────────────────────────────────────────────────────────────┐
│              PIPELINE: ls | grep txt | wc -l                    │
└─────────────────────────────────────────────────────────────────┘

┌─────────────────┐
│  1. PARSE       │  Identify 3 stages
│    PIPELINE     │  Stages: [ls], [grep, txt], [wc, -l]
└────────┬────────┘
         │
         ▼
┌─────────────────┐
│  2. CREATE      │  Create pipes: pipe1, pipe2
│     PIPES       │  pipe1: ls → grep
└────────┬────────┘  pipe2: grep → wc
         │
         ▼
┌─────────────────┐     ┌─────────────────┐     ┌─────────────────┐
│  3. SPAWN       │     │  4. SPAWN       │     │  5. SPAWN       │
│     STAGE 1     │────▶│     STAGE 2     │────▶│     STAGE 3     │
│     (ls)        │     │  (grep txt)     │     │    (wc -l)      │
│                 │     │                 │     │                 │
│ stdout → pipe1  │     │ stdin ← pipe1   │     │ stdin ← pipe2   │
│                 │     │ stdout → pipe2  │     │ stdout → term   │
└────────┬────────┘     └────────┬────────┘     └────────┬────────┘
         │                       │                       │
         └───────────────────────┴───────────────────────┘
                                 │
                                 ▼
                        ┌─────────────────┐
                        │  6. WAIT FOR    │
                        │  ALL STAGES     │
                        │  (external.rs)  │
                        └────────┬────────┘
                                 │
                                 ▼
                        ┌─────────────────┐
                        │  7. RETURN      │
                        │  LAST EXIT CODE │
                        │  (POSIX: wc's)  │
                        └─────────────────┘
```

### Verification Flow

```
┌─────────────────────────────────────────────────────────────────┐
│              FORMAL VERIFICATION PIPELINE                       │
└─────────────────────────────────────────────────────────────────┘

┌─────────────────┐
│  LEAN 4 PROOFS  │
│  (source of     │  Theorems:
│   truth)        │  - mkdir_rmdir_reversible
└────────┬────────┘  - createFile_deleteFile_reversible
         │           - operation_sequence_reversible
         │
         ▼
┌─────────────────┐
│  COERCIONS TO   │  Same theorems proven in:
│  OTHER SYSTEMS  │  - Coq (CIC)
│  (cross-        │  - Agda (ITT)
│   validation)   │  - Isabelle/HOL
└────────┬────────┘  - Mizar (Set Theory)
         │           - Z3 SMT (Automated)
         │
         ▼
┌─────────────────┐
│  RUST           │  Manual correspondence:
│ IMPLEMENTATION  │  - Rust mkdir ↔ Lean mkdir
│  (vsh crate)    │  - State mapping documented
└────────┬────────┘  - Preconditions match
         │
         ▼
┌─────────────────┐
│ CORRESPONDENCE  │  Tests verify:
│     TESTS       │  - Rust behavior matches Lean spec
│(correspondence_ │  - All theorems hold in practice
│  tests.rs)      │  - 27 tests (15 unit + 12 property)
└────────┬────────┘
         │
         ▼
┌─────────────────┐
│  PROPERTY-BASED │  PropTest/Echidna:
│    TESTING      │  - Randomized inputs
│ (proptest +     │  - Verify theorems hold for all inputs
│  echidna)       │  - Find edge cases
└────────┬────────┘
         │
         ▼
┌─────────────────┐
│  FUZZING        │  Cargo-fuzz:
│ (fuzz targets)  │  - Parser fuzzing
└────────┬────────┘  - Arithmetic expression fuzzing
         │           - Job spec fuzzing
         │
         ▼
    VERIFICATION COMPLETE
    Confidence: 85% (manual correspondence)
    Goal: 99%+ (mechanized proofs)
```

---

## Part 3: Data Flow

### State Transition Diagram

```
┌─────────────────────────────────────────────────────────────────┐
│                    SHELL STATE MACHINE                          │
└─────────────────────────────────────────────────────────────────┘

    ┌────────────┐
    │   START    │  Initialize shell
    │  (clean)   │  Load ~/.vsh_state.json (if exists)
    └──────┬─────┘
           │
           ▼
    ┌────────────┐
    │   READY    │◄──────────────────────┐
    │ (awaiting  │                       │
    │   input)   │                       │
    └──────┬─────┘                       │
           │                             │
           │ User enters command         │
           ▼                             │
    ┌────────────┐                       │
    │  PARSING   │  Tokenize → AST       │
    └──────┬─────┘                       │
           │                             │
           ▼                             │
    ┌────────────┐                       │
    │ EXPANDING  │  $VAR, *.txt, quotes  │
    └──────┬─────┘                       │
           │                             │
           ▼                             │
    ┌────────────┐                       │
    │ EXECUTING  │  Run command          │
    └──────┬─────┘                       │
           │                             │
           ├──── Success ────────────────┤
           │                             │
           └──── Error ──┐               │
                         ▼               │
                  ┌────────────┐         │
                  │   ERROR    │         │
                  │ (display)  │─────────┘
                  └────────────┘

Special States:

    ┌────────────┐
    │TRANSACTION │  begin → commands → commit/rollback
    │  ACTIVE    │  Groups operations
    └────────────┘

    ┌────────────┐
    │  UNDOING   │  Reverse last operation
    │            │  Restore previous state
    └────────────┘

    ┌────────────┐
    │  REDOING   │  Replay undone operation
    │            │  Restore newer state
    └────────────┘
```

---

## Part 4: File System Layout

```
valence-shell/
├── proofs/                          # Formal Verification (256+ theorems)
│   ├── lean4/                       # Primary source of truth
│   │   ├── FilesystemModel.lean     # mkdir/rmdir reversibility
│   │   ├── FileOperations.lean      # touch/rm reversibility
│   │   ├── FilesystemComposition.lean  # Operation sequences
│   │   └── FilesystemEquivalence.lean  # Equivalence relations
│   ├── coq/                         # Cross-validation (CIC)
│   ├── agda/                        # Cross-validation (ITT)
│   ├── isabelle/                    # Cross-validation (HOL)
│   └── mizar/                       # Cross-validation (Set Theory)
│
├── impl/                            # Implementation
│   └── rust-cli/                    # Primary implementation (Rust)
│       ├── src/
│       │   ├── main.rs              # CLI entry point
│       │   ├── lib.rs               # Library interface
│       │   ├── repl.rs              # Interactive REPL
│       │   ├── parser.rs            # Tokenizer + Parser
│       │   ├── quotes.rs            # Quote processing (M13)
│       │   ├── glob.rs              # Glob expansion (M12)
│       │   ├── executor.rs          # Built-in commands
│       │   ├── external.rs          # External command execution
│       │   ├── state.rs             # State management (undo/redo)
│       │   ├── history.rs           # Command history
│       │   ├── redirection.rs       # I/O redirections
│       │   ├── job.rs               # Job control
│       │   ├── verification.rs      # Runtime verification
│       │   └── proof_refs.rs        # Proof references
│       ├── tests/
│       │   ├── correspondence_tests.rs  # Lean ↔ Rust tests
│       │   ├── integration_test.rs      # Integration tests
│       │   └── property_tests.rs        # Property-based tests
│       ├── fuzz/                    # Fuzzing targets
│       │   └── fuzz_targets/
│       │       ├── fuzz_parser.rs
│       │       ├── fuzz_arith.rs
│       │       └── fuzz_job_spec.rs
│       └── Cargo.toml
│
├── docs/                            # Documentation
│   ├── ARCHITECTURE.md              # System design
│   ├── LEAN4_RUST_CORRESPONDENCE.md # Proof mapping
│   ├── ECHIDNA_INTEGRATION.md       # Verification pipeline
│   ├── POSIX_COMPLIANCE.md          # POSIX roadmap
│   └── PHASE6_M*.md                 # Milestone designs
│
└── STATE.scm                        # Project state tracking
```

---

## Part 5: Testing & Verification Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│                  TESTING & VERIFICATION LAYERS                  │
└─────────────────────────────────────────────────────────────────┘

Layer 1: FORMAL PROOFS (Mathematical Certainty)
┌───────────────────────────────────────────────────────────────┐
│ Lean 4 Theorems → Coq → Agda → Isabelle → Mizar → Z3        │
│ 256+ theorems across 6 proof systems                         │
│ Reversibility, composition, equivalence, independence        │
└───────────────────────────────────────────────────────────────┘
                            ↓
Layer 2: CORRESPONDENCE TESTS (Spec ↔ Impl)
┌───────────────────────────────────────────────────────────────┐
│ tests/correspondence_tests.rs (27 tests)                     │
│ - Verify Rust implementation matches Lean 4 specification   │
│ - Test preconditions, effects, reversibility                │
│ - 85% confidence (manual) → 99%+ (goal: mechanized)          │
└───────────────────────────────────────────────────────────────┘
                            ↓
Layer 3: PROPERTY-BASED TESTS (Randomized Validation)
┌───────────────────────────────────────────────────────────────┐
│ PropTest + Echidna                                           │
│ - Randomized inputs (1000s of test cases)                   │
│ - Verify theorems hold for all inputs                       │
│ - Find edge cases automatically                             │
└───────────────────────────────────────────────────────────────┘
                            ↓
Layer 4: INTEGRATION TESTS (End-to-End)
┌───────────────────────────────────────────────────────────────┐
│ tests/integration_test.rs (40+ tests)                       │
│ - Real filesystem operations                                │
│ - Undo/redo cycles                                          │
│ - Pipeline execution                                        │
│ - Glob expansion, quote processing                          │
└───────────────────────────────────────────────────────────────┘
                            ↓
Layer 5: UNIT TESTS (Component Isolation)
┌───────────────────────────────────────────────────────────────┐
│ Individual module tests (130+ tests)                        │
│ - Parser, quotes, glob, state, redirections                │
│ - Each module tested in isolation                           │
└───────────────────────────────────────────────────────────────┘
                            ↓
Layer 6: FUZZING (Attack Surface)
┌───────────────────────────────────────────────────────────────┐
│ Cargo-fuzz targets (4 targets)                              │
│ - Parser fuzzing (untrusted input)                          │
│ - Arithmetic expression fuzzing                             │
│ - Job spec fuzzing                                          │
│ - Signal parsing fuzzing                                    │
└───────────────────────────────────────────────────────────────┘
                            ↓
Layer 7: STRESS TESTS (Performance & Reliability)
┌───────────────────────────────────────────────────────────────┐
│ - Deep nesting (1000+ levels)                               │
│ - Large files (GB+)                                         │
│ - Many operations (10k+ history)                            │
│ - Concurrent access                                         │
│ - Memory limits                                             │
└───────────────────────────────────────────────────────────────┘
                            ↓
Layer 8: COMPILATION TESTS (Cross-Platform)
┌───────────────────────────────────────────────────────────────┐
│ CI/CD on GitHub Actions                                     │
│ - Linux (Ubuntu, Fedora, Arch)                             │
│ - macOS                                                     │
│ - BSD (if portable)                                        │
│ - Different Rust versions (stable, nightly)                │
└───────────────────────────────────────────────────────────────┘
                            ↓
Layer 9: SECURITY AUDITS (Attack Surface Analysis)
┌───────────────────────────────────────────────────────────────┐
│ - Input validation (untrusted user input)                  │
│ - Path traversal attacks (../../../../etc/passwd)          │
│ - Command injection ($(malicious))                         │
│ - Resource exhaustion (fork bombs, infinite loops)         │
│ - Privilege escalation                                     │
│ - Memory safety (Rust guarantees)                          │
└───────────────────────────────────────────────────────────────┘
                            ↓
Layer 10: BENCHMARKING (Performance Metrics)
┌───────────────────────────────────────────────────────────────┐
│ Criterion benchmarks                                        │
│ - Cold start time (target: <5ms)                           │
│ - Command execution overhead                                │
│ - Parser performance                                        │
│ - State persistence I/O                                     │
│ - Memory usage                                              │
└───────────────────────────────────────────────────────────────┘

VERIFICATION STATUS:
✅ Layers 1-5: Complete (256+ proofs, 157+ tests)
🔄 Layer 6: Partial (fuzzing infrastructure ready)
❌ Layers 7-10: pending v1.0 (tracked under #43 — test+bench expansion)
```

---

## Part 6: Route to v2 and v3

### Version Roadmap

```
┌─────────────────────────────────────────────────────────────────┐
│                    VALENCE SHELL ROADMAP                        │
└─────────────────────────────────────────────────────────────────┘

v0.14.0 (CURRENT)
├─ Phase 6: M1-M11 complete (pipelines, redirections, variables, job control)
├─ 256+ formal proofs across 6 systems
├─ Working interactive shell
└─ 85% correspondence confidence

         │ 6 weeks
         ▼

v1.0.0 (STABLE RELEASE) - Target: Q1 2026
├─ Phase 6: M14 complete (Full POSIX shell)
│  ├─ test/[ commands
│  ├─ && and || operators
│  ├─ Command grouping { }
│  └─ if/while/case statements
├─ Verification complete:
│  ├─ Echidna pipeline integrated
│  ├─ 99%+ correspondence confidence
│  ├─ All 10 testing layers complete
│  └─ Security audit passed
├─ Documentation complete:
│  ├─ Man pages
│  ├─ User guide
│  ├─ Migration guide from bash
│  └─ Example scripts
├─ Performance optimized:
│  ├─ <5ms cold start
│  ├─ Minimal memory footprint
│  └─ Comparable to bash/zsh
└─ Production ready:
   ├─ Package for major distros
   ├─ Homebrew formula
   └─ Docker images

         │ 3-6 months
         ▼

v2.0.0 (ENHANCED VERIFICATION) - Target: Q3 2026
├─ Mechanized correspondence proofs:
│  ├─ Lean 4 extraction to Rust
│  ├─ Automated theorem checking
│  └─ 99.9%+ verification confidence
├─ Extended MAA Framework:
│  ├─ RMO (secure deletion) fully implemented
│  ├─ GDPR compliance with proofs
│  ├─ Cryptographic guarantees
│  └─ Audit trail with tamper-evidence
├─ Advanced features:
│  ├─ Functions (fn keyword)
│  ├─ Arrays and associative arrays
│  ├─ Advanced pattern matching
│  └─ Module system
├─ BEAM integration (optional):
│  ├─ Elixir daemon for complex ops
│  ├─ Distributed shell capabilities
│  └─ Hot code reload
└─ Performance:
   ├─ <3ms cold start
   ├─ JIT compilation for loops
   └─ Aggressive optimization

         │ 6-12 months
         ▼

v3.0.0 (DISTRIBUTED & ADVANCED) - Target: Q2 2027
├─ Distributed shell:
│  ├─ Remote execution with proofs
│  ├─ Consensus protocols
│  └─ Multi-node coordination
├─ Advanced verification:
│  ├─ Full stack verification (OS→Shell)
│  ├─ Verified compiler integration
│  └─ Hardware-level guarantees
├─ AI integration:
│  ├─ Natural language commands
│  ├─ Proof synthesis
│  └─ Automated script generation
├─ Extended platform support:
│  ├─ Windows (WSL2 + native)
│  ├─ Mobile (Termux)
│  └─ Embedded systems
└─ Ecosystem:
   ├─ Plugin system (Wasm)
   ├─ Package manager integration
   └─ Cloud shell services
```

### Feature Comparison Matrix

```
┌──────────────────────────────────────────────────────────────────┐
│              FEATURE COMPARISON: v1 vs v2 vs v3                  │
├──────────────────────┬──────────┬──────────┬──────────────────────┤
│ Feature              │   v1.0   │   v2.0   │        v3.0          │
├──────────────────────┼──────────┼──────────┼──────────────────────┤
│ POSIX Shell          │    ✅    │    ✅    │         ✅           │
│ Formal Proofs        │    ✅    │    ✅    │         ✅           │
│ Undo/Redo            │    ✅    │    ✅    │         ✅           │
│ Job Control          │    ✅    │    ✅    │         ✅           │
│ Pipelines            │    ✅    │    ✅    │         ✅           │
│ Glob Expansion       │    ✅    │    ✅    │         ✅           │
│ Quote Processing     │    ✅    │    ✅    │         ✅           │
│ test/[ commands      │    ✅    │    ✅    │         ✅           │
│ && / || operators    │    ✅    │    ✅    │         ✅           │
│ if/while/case        │    ✅    │    ✅    │         ✅           │
│                      │          │          │                      │
│ Mechanized Proofs    │   85%    │   99.9%  │        99.99%        │
│ RMO/GDPR             │   Partial│    ✅    │         ✅           │
│ Functions            │    ❌    │    ✅    │         ✅           │
│ Arrays               │    ❌    │    ✅    │         ✅           │
│ BEAM Integration     │    ❌    │  Optional│         ✅           │
│                      │          │          │                      │
│ Distributed Shell    │    ❌    │    ❌    │         ✅           │
│ AI Integration       │    ❌    │    ❌    │         ✅           │
│ Plugin System        │    ❌    │    ❌    │         ✅           │
│ Mobile Support       │    ❌    │    ❌    │         ✅           │
│                      │          │          │                      │
│ Cold Start Time      │   <5ms   │   <3ms   │        <2ms          │
│ Memory Usage         │   ~10MB  │   ~8MB   │        ~6MB          │
│ Platform Support     │ Linux/BSD│ +macOS   │   +Windows/Mobile    │
└──────────────────────┴──────────┴──────────┴──────────────────────┘
```

---

## Part 7: Pre-v1.0 Checklist

### Critical Path to v1.0 (6 weeks)

```
Week 1-2: Feature Completion (M14)
  ☐ Implement test/[ commands
  ☐ Implement && and || operators
  ☐ Add command grouping { ; }
  ☐ Add if/then/fi statements
  ☐ Add while/do/done loops

Week 2-3: Verification Infrastructure
  ☐ Complete Echidna integration
  ☐ Add mechanized correspondence tests
  ☐ Increase test coverage to 95%+
  ☐ Run fuzzing campaigns (24h minimum)

Week 3-4: Stress & Security Testing
  ☐ Stress tests (deep nesting, large files, many ops)
  ☐ Security audit (path traversal, injection, etc.)
  ☐ Attack surface analysis
  ☐ Resource exhaustion tests
  ☐ Compilation tests (Linux, macOS, BSD)

Week 4-5: Performance & Benchmarking
  ☐ Benchmark suite with Criterion
  ☐ Optimize cold start (<5ms target)
  ☐ Memory profiling
  ☐ Comparison with bash/zsh/fish
  ☐ Performance regression tests

Week 5-6: Documentation & Release
  ☐ Man pages (vsh.1)
  ☐ User guide
  ☐ Migration guide from bash
  ☐ Example scripts repository
  ☐ API documentation (rustdoc)
  ☐ Package for distros
  ☐ Homebrew formula
  ☐ Release announcement
```

---

**END OF ARCHITECTURE DIAGRAMS**
**Next: Implementation of remaining features**
