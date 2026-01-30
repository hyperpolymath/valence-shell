# Valence Shell: Architecture Overview

**Version**: 0.14.0
**Last Updated**: 2026-01-30

---

## High-Level Architecture

```
┌─────────────────────────────────────────────────────────┐
│                    User Interface (REPL)                 │
│                    src/repl.rs                           │
└──────────────────────┬──────────────────────────────────┘
                       │
                       ▼
┌─────────────────────────────────────────────────────────┐
│                    Parser                                │
│                    src/parser.rs                         │
│  Tokenizer → AST Builder → Command Validator            │
└──────────────────────┬──────────────────────────────────┘
                       │
                       ▼
┌─────────────────────────────────────────────────────────┐
│                    Executor                              │
│                    src/executable.rs                     │
│  Built-ins │ External Commands │ Pipelines │ Jobs       │
└──────────────────────┬──────────────────────────────────┘
                       │
              ┌────────┴────────┐
              ▼                 ▼
┌──────────────────────┐  ┌─────────────────────────────┐
│  Filesystem Ops      │  │   State Management          │
│  src/commands/*.rs   │  │   src/state.rs              │
│  - mkdir/rmdir       │  │   - History tracking        │
│  - touch/rm          │  │   - Undo/redo stacks        │
│  - File I/O          │  │   - Operation log           │
└──────────────────────┘  └─────────────────────────────┘
         │                           │
         └───────────┬───────────────┘
                     ▼
         ┌────────────────────────────┐
         │   POSIX Filesystem         │
         │   (syscalls via libc)      │
         └────────────────────────────┘
```

---

## Layer Breakdown

### Layer 1: REPL (User Interface)

**Files**: `src/repl.rs`, `src/prompt.rs`, `src/completion.rs`

**Responsibilities**:
- Read user input
- Tab completion
- History (command history, not operation history)
- Syntax highlighting (TODO)
- Prompt rendering

**Key Components**:
```rust
pub struct Repl {
    line_editor: Reedline,      // Line editor with history
    state: ShellState,          // Shell state
    completer: Completer,       // Tab completion
}
```

---

### Layer 2: Parser

**Files**: `src/parser.rs`, `src/tokenizer.rs`, `src/quotes.rs`

**Responsibilities**:
- Tokenize input string
- Parse tokens into AST (Abstract Syntax Tree)
- Handle quotes, glob patterns, redirections
- Validate syntax

**Grammar** (simplified):
```
command      ::= pipeline (';' pipeline)* ('&')?
pipeline     ::= simple_cmd ('|' simple_cmd)*
simple_cmd   ::= builtin | external | test
builtin      ::= 'cd' | 'exit' | 'undo' | 'redo' | ...
external     ::= WORD [args] [redirections]
test         ::= 'test' test_expr | '[' test_expr ']'
```

**Key Components**:
```rust
pub enum Command {
    Mkdir { path: String },
    Rmdir { path: String },
    Touch { path: String },
    Rm { path: String },
    Pipeline {
        commands: Vec<Command>,
        redirections: Vec<Redirection>,
        background: bool,
    },
    LogicalOp {
        op: LogicalOperator,  // && or ||
        left: Box<Command>,
        right: Box<Command>,
    },
    Test { expr: TestExpr },
    // ...
}
```

---

### Layer 3: Executor

**Files**: `src/executable.rs`, `src/external.rs`, `src/builtins.rs`

**Responsibilities**:
- Execute parsed commands
- Handle built-ins vs external commands
- Manage redirections
- Job control
- Pipeline execution

**Execution Flow**:
```
Command
  ↓
Is Built-in?
  ├─ Yes → Execute built-in (mkdir, cd, undo, etc.)
  └─ No → Execute external (fork/exec)
    ↓
Apply Redirections (>, <, 2>, etc.)
    ↓
Execute in Subprocess
    ↓
Wait for Completion (or background if &)
    ↓
Return Exit Code
```

**Pipeline Execution**:
```
cmd1 | cmd2 | cmd3
  ↓
1. Create pipes: pipe1 (cmd1→cmd2), pipe2 (cmd2→cmd3)
2. Fork child processes
3. Set up stdio:
   - cmd1: stdout → pipe1.write
   - cmd2: stdin ← pipe1.read, stdout → pipe2.write
   - cmd3: stdin ← pipe2.read
4. Exec commands
5. Wait for all to finish
6. Return exit code of last command (POSIX behavior)
```

---

### Layer 4: Filesystem Operations

**Files**: `src/commands/mkdir.rs`, `src/commands/rmdir.rs`, `src/commands/touch.rs`, `src/commands/rm.rs`

**Responsibilities**:
- Execute filesystem operations
- Record undo information
- Validate preconditions
- Apply changes atomically

**Operation Pattern**:
```rust
pub fn mkdir(
    state: &mut ShellState,
    path: &str,
    create_parents: bool,
) -> Result<(), VshError> {
    // 1. Validate preconditions
    let full_path = state.root.join(path);
    if full_path.exists() {
        return Err(VshError::PathAlreadyExists(path.into()));
    }

    // 2. Perform operation
    if create_parents {
        fs::create_dir_all(&full_path)?;
    } else {
        fs::create_dir(&full_path)?;
    }

    // 3. Record for undo
    state.push_history(Operation::Mkdir {
        path: path.to_string(),
        created_parents: get_created_parents(&full_path),
    });

    Ok(())
}
```

---

### Layer 5: State Management

**Files**: `src/state.rs`, `src/history.rs`

**Responsibilities**:
- Track operation history
- Manage undo/redo stacks
- Maintain shell state (current dir, variables, jobs)
- Provide undo/redo functionality

**State Machine**:
```
┌─────────────────────┐
│   Initial State     │
│   history: []       │
│   redo: []          │
└──────────┬──────────┘
           │ operation
           ▼
┌─────────────────────┐
│   After Operation   │
│   history: [op1]    │
│   redo: []          │
└──────────┬──────────┘
           │ undo
           ▼
┌─────────────────────┐
│   After Undo        │
│   history: []       │
│   redo: [op1]       │
└──────────┬──────────┘
           │ redo
           ▼
┌─────────────────────┐
│   After Redo        │
│   history: [op1]    │
│   redo: []          │
└─────────────────────┘
```

**Invariants** (verified by property tests):
- `history.len() + redo.len() = total_operations`
- After full undo: filesystem = initial state
- After undo→redo: filesystem = pre-undo state

---

## Data Flow Examples

### Example 1: Simple Command

```
User types: mkdir test_dir

1. REPL reads input
2. Parser tokenizes: [Mkdir, "test_dir"]
3. Parser creates: Command::Mkdir { path: "test_dir" }
4. Executor calls: mkdir(&mut state, "test_dir", false)
5. mkdir function:
   - Creates directory
   - Records in history
6. Returns to REPL
7. REPL shows: ✓ Created directory: test_dir
```

### Example 2: Pipeline

```
User types: ls | grep .txt | wc -l

1. REPL reads input
2. Parser tokenizes and creates:
   Command::Pipeline {
       commands: [
           External("ls", []),
           External("grep", [".txt"]),
           External("wc", ["-l"]),
       ],
       redirections: [],
       background: false,
   }
3. Executor:
   - Creates 2 pipes
   - Forks 3 processes
   - Sets up stdio chaining
   - Waits for all
4. Returns exit code of wc -l
```

### Example 3: Undo

```
User types: undo

1. REPL reads input
2. Parser creates: Command::Undo
3. Executor calls: state.pop_undo()
4. state.pop_undo():
   - Pops last operation from history
   - Determines inverse operation
   - Executes inverse (e.g., rmdir for mkdir)
   - Pushes to redo stack
5. Returns to REPL
6. REPL shows: ⟲ Undoing: mkdir test_dir
                ✓ Removed directory: test_dir
```

---

## Formal Verification Integration

### Correspondence Map

| Rust Implementation | Formal Proof (Lean 4) | Confidence |
|---------------------|------------------------|------------|
| `src/commands/mkdir.rs` | `proofs/lean4/Operations/Mkdir.lean` | 95% |
| `src/commands/rmdir.rs` | `proofs/lean4/Operations/Rmdir.lean` | 95% |
| `src/state.rs` (undo) | `proofs/lean4/Composition/Undo.lean` | 90% |
| `src/parser.rs` | N/A (tested) | 85% |

### Verification Layers

```
Layer 0: Formal Proofs (Lean 4, Coq, etc.)
  ↓ (correspondence)
Layer 1: Extracted Code (Idris2, v2.0+)
  ↓ (FFI)
Layer 2: Rust Implementation (current)
  ↓ (property tests)
Layer 3: Unit/Integration Tests
  ↓ (runtime)
Layer 4: POSIX Syscalls
```

---

## Performance Characteristics

| Operation | Time Complexity | Space Complexity | Notes |
|-----------|-----------------|------------------|-------|
| mkdir | O(1) | O(1) | Single syscall |
| undo (single) | O(1) | O(1) | Pop from stack |
| undo (all N) | O(N) | O(1) | N pops |
| history lookup | O(1) | O(N) | Vec access |
| pipeline (K stages) | O(K) | O(K) | K processes |
| glob expansion | O(N * M) | O(N) | N files, M pattern chars |

**Memory Usage**:
- Per operation: ~200 bytes (operation metadata)
- History limit: Configurable (default: 10,000 ops = ~2MB)
- Undo stack: Same as history

---

## Thread Safety

**Current**: Single-threaded (shell process)
**Future**: Multi-threaded job control

**Concurrent Access** (multiple shell instances):
- Each shell has independent `ShellState`
- Filesystem operations use POSIX locking
- No shared state between shells

---

## Error Handling Strategy

### Error Types

```rust
pub enum VshError {
    PathNotFound(PathBuf),
    PathAlreadyExists(PathBuf),
    PermissionDenied(PathBuf),
    InvalidPath(String),
    UndoStackEmpty,
    RedoStackEmpty,
    ExternalCommandFailed { cmd: String, exit_code: i32 },
    IoError(std::io::Error),
}
```

### Error Propagation

```
Operation fails
  ↓
Return VshError
  ↓
Executor catches
  ↓
Display user-friendly error
  ↓
Continue REPL (don't crash)
```

**No Silent Failures**: Every error is either:
1. Returned to user (displayed in REPL)
2. Logged (if background job)
3. Panics (only for impossible states, in debug mode)

---

## Security Model

### Sandbox Mode (Default)

```
Shell starts with root = /some/directory
  ↓
All paths relative to root
  ↓
Attempts to escape (../, absolute paths) are:
  - Detected via canonicalize()
  - Rejected with error
```

**Enabled by default** for safety.

**Disable with**: `vsh --no-sandbox` (not recommended)

### Input Validation

- **Path traversal**: Prevented via canonicalization
- **Command injection**: Parser doesn't eval shell metacharacters as commands
- **Null bytes**: Rejected (Rust strings are UTF-8)
- **Buffer overflows**: Impossible (Rust memory safety)

---

## Extension Points

### Adding New Operations

1. Create `src/commands/new_op.rs`
2. Implement operation function
3. Add to `Command` enum
4. Wire up parser and executor
5. Add property tests
6. (Maintainers update proofs)

### Adding New Built-ins

1. Add to `src/builtins.rs`
2. Wire up parser
3. Add tests

### Adding New Features

- **Pipelines**: Modify `src/external.rs`
- **Redirections**: Modify `src/executable.rs`
- **Glob patterns**: Modify `src/glob.rs`
- **Job control**: Modify `src/jobs.rs`

---

## Future Architecture (v2.0)

```
┌─────────────────────────────────────────────────────────┐
│            REPL (Rust)                                   │
└──────────────────────┬──────────────────────────────────┘
                       │
                       ▼
┌─────────────────────────────────────────────────────────┐
│            Parser (Rust)                                 │
└──────────────────────┬──────────────────────────────────┘
                       │ FFI
                       ▼
┌─────────────────────────────────────────────────────────┐
│       Core (Idris2-extracted C code)                     │
│       - State machine                                    │
│       - Undo/redo                                        │
│       - Operation verification                           │
│       99%+ confidence                                    │
└──────────────────────┬──────────────────────────────────┘
                       │
                       ▼
┌─────────────────────────────────────────────────────────┐
│            POSIX Syscalls                                │
└─────────────────────────────────────────────────────────┘
```

**Benefits**:
- Core extracted from proofs (closes correspondence gap)
- Rust UI/parser (fast, ergonomic)
- Best of both worlds

---

## Further Reading

- **User Guide**: `docs/USER_GUIDE.md`
- **Contributing**: `docs/CONTRIBUTOR_GUIDE_TIER1.md`
- **Proofs**: `docs/PROOF_OVERVIEW.md`
- **Verification Strategy**: `docs/VERIFICATION_STRATEGY_ANALYSIS.md`
