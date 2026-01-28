# Phase 6 Milestone 2: Input/Output Redirections

**Version**: 0.8.0 (Target)
**Date**: 2026-01-28
**Author**: Jonathan D.A. Jewell <jonathan.jewell@open.ac.uk>
**License**: PMPL-1.0-or-later
**Prerequisites**: Phase 6 M1 (External Commands) ✅ Complete

---

## Overview

Implement POSIX-compliant I/O redirections for both built-in and external commands.

**Goals**:
- Output redirection (`>`, `>>`)
- Input redirection (`<`)
- Error redirection (`2>`, `2>>`, `2>&1`)
- File descriptor management
- Atomic file operations (no partial writes on error)
- Proof references for file modifications

**Timeline**: 2-3 weeks
**Complexity**: Medium (file descriptor management, error handling)

---

## POSIX Redirection Semantics

### Output Redirection

| Syntax | Meaning | Behavior |
|--------|---------|----------|
| `cmd > file` | Redirect stdout to file | Truncate file, write stdout |
| `cmd >> file` | Append stdout to file | Create/append, write stdout |
| `cmd 2> file` | Redirect stderr to file | Truncate file, write stderr |
| `cmd 2>> file` | Append stderr to file | Create/append, write stderr |
| `cmd &> file` | Redirect both to file | Truncate file, write both (bash) |
| `cmd > file 2>&1` | Both to same file | Redirect stderr to stdout's target |

### Input Redirection

| Syntax | Meaning | Behavior |
|--------|---------|----------|
| `cmd < file` | Read stdin from file | Open file, connect to stdin |
| `cmd 0< file` | Explicit stdin redirect | Same as `<` |

### File Descriptor Duplication

| Syntax | Meaning | Example |
|--------|---------|---------|
| `M>&N` | Redirect M to N's target | `2>&1` (stderr → stdout's file) |
| `M<&N` | Read M from N's source | `3<&0` (fd3 from stdin's file) |

---

## Architecture

### Current State (Phase 6 M1)

```
User Input → Parser → ExecutableCommand
                         ↓
                      execute()
                         ↓
                  ┌──────┴──────┐
                  ↓             ↓
            Built-in      External (via fork+exec)
            (direct)      (stdio inherited)
```

### With Redirections (Phase 6 M2)

```
User Input → Parser → ExecutableCommand
                         ↓
                  RedirectionSetup
                         ↓
                    File I/O Layer
                         ↓
                      execute()
                         ↓
                  ┌──────┴──────┐
                  ↓             ↓
            Built-in      External
         (stdio capture)  (stdio redirected)
                         ↓
                  RedirectionCleanup
```

---

## Design Decisions

### Decision 1: When to Parse Redirections

**Option A**: Lexer-level (tokenize `>`, `>>` separately)
- Pro: Clean separation
- Con: More complex lexer

**Option B**: Parser-level (parse as part of command)
- Pro: Simpler implementation
- Con: Redirect syntax in parser

**Decision**: **Option B** - Parse redirections as part of command syntax
- Rationale: Redirections are syntactic, not semantic
- Example: `mkdir foo > log.txt` is one command with redirection, not two tokens

### Decision 2: Redirection Representation

```rust
/// Redirection for a command
#[derive(Debug, Clone, PartialEq)]
pub enum Redirection {
    /// Redirect stdout to file (truncate)
    Output { file: String },

    /// Append stdout to file
    Append { file: String },

    /// Redirect stdin from file
    Input { file: String },

    /// Redirect stderr to file (truncate)
    ErrorOutput { file: String },

    /// Append stderr to file
    ErrorAppend { file: String },

    /// Redirect stderr to stdout's target
    ErrorToOutput,

    /// Redirect both stdout and stderr to file (bash &>)
    BothOutput { file: String },
}

/// Updated Command enum
pub enum Command {
    Mkdir {
        path: String,
        redirects: Vec<Redirection>, // NEW
    },
    External {
        program: String,
        args: Vec<String>,
        redirects: Vec<Redirection>, // NEW
    },
    // ... other commands with redirects field
}
```

### Decision 3: File Descriptor Management

**Approach**: Use Rust's `std::process::Stdio` for external commands, custom capture for built-ins.

**For External Commands**:
```rust
use std::process::{Command, Stdio};
use std::fs::OpenOptions;

// Setup redirections
let stdout_config = match &output_redirect {
    Some(Redirection::Output { file }) => {
        let f = File::create(file)?;
        Stdio::from(f)
    }
    Some(Redirection::Append { file }) => {
        let f = OpenOptions::new().create(true).append(true).open(file)?;
        Stdio::from(f)
    }
    None => Stdio::inherit(),
};

Command::new(program)
    .stdout(stdout_config)
    .spawn()?;
```

**For Built-in Commands**:
```rust
// Capture stdout
let stdout_redirect = setup_stdout_redirect(&redirects)?;

// Execute command
match stdout_redirect {
    Some(RedirectTarget::File(mut file)) => {
        // Capture output and write to file
        let output = capture_builtin_output(|| {
            commands::mkdir(state, path, false)
        })?;
        file.write_all(output.as_bytes())?;
    }
    None => {
        // Normal execution
        commands::mkdir(state, path, false)?;
    }
}
```

### Decision 4: Reversibility of Redirections

**Question**: Are file writes from redirections reversible?

**Answer**: **Partially**

1. **File creation** (if file didn't exist):
   - Reversible: Delete file on undo
   - Proof: `createFile_deleteFile_reversible` (already proven)

2. **File truncation** (if file existed):
   - Needs: Save original content before truncate
   - Undo: Restore original content
   - **NEW PROOF NEEDED**: `truncate_restore_reversible`

3. **File append** (>>):
   - Needs: Record byte offset before append
   - Undo: Truncate to original size
   - **NEW PROOF NEEDED**: `append_truncate_reversible`

**Implementation Strategy**:
```rust
pub enum FileModification {
    Created { path: PathBuf },
    Truncated { path: PathBuf, original_content: Vec<u8> },
    Appended { path: PathBuf, original_size: u64 },
}

impl FileModification {
    fn reverse(&self) -> Result<()> {
        match self {
            FileModification::Created { path } => {
                fs::remove_file(path)?;
            }
            FileModification::Truncated { path, original_content } => {
                fs::write(path, original_content)?;
            }
            FileModification::Appended { path, original_size } => {
                let file = fs::OpenOptions::new().write(true).open(path)?;
                file.set_len(*original_size)?;
            }
        }
        Ok(())
    }
}
```

### Decision 5: Error Handling

**Philosophy**: Fail fast, atomic operations

**Rules**:
1. **Validate ALL redirections before executing command**
   - Check file permissions
   - Check parent directory exists
   - Fail if any redirection invalid

2. **Atomic file operations**
   - Write to temporary file first
   - Rename on success (atomic)
   - No partial writes visible to user

3. **Cleanup on error**
   - Remove created files
   - Restore truncated files
   - Leave filesystem unchanged

**Example**:
```rust
fn execute_with_redirections(
    cmd: &Command,
    redirects: &[Redirection],
    state: &mut ShellState,
) -> Result<()> {
    // Phase 1: Validate all redirections
    let redirect_targets = validate_redirections(redirects)?;

    // Phase 2: Save original state (for undo)
    let saved_state = capture_file_state(&redirect_targets)?;

    // Phase 3: Setup redirections
    let _redirect_guard = setup_redirections(redirects)?;

    // Phase 4: Execute command
    match cmd.execute(state) {
        Ok(result) => {
            // Success: Record operation for undo
            record_file_modifications(saved_state, &redirect_targets)?;
            Ok(result)
        }
        Err(e) => {
            // Failure: Restore original state
            restore_file_state(saved_state)?;
            Err(e)
        }
    }
}
```

---

## Parser Extensions

### Current Parser (Phase 6 M1)

```rust
pub enum Command {
    Mkdir { path: String },
    External { program: String, args: Vec<String> },
    // ...
}

pub fn parse_command(input: &str) -> Result<Command> {
    let parts: Vec<&str> = input.split_whitespace().collect();
    match parts[0] {
        "mkdir" => Ok(Command::Mkdir { path: parts[1].to_string() }),
        cmd => Ok(Command::External {
            program: cmd.to_string(),
            args: parts[1..].iter().map(|s| s.to_string()).collect(),
        }),
    }
}
```

### Extended Parser (Phase 6 M2)

**Step 1**: Tokenize with redirection operators

```rust
#[derive(Debug, PartialEq)]
enum Token {
    Word(String),
    OutputRedirect,      // >
    AppendRedirect,      // >>
    InputRedirect,       // <
    ErrorRedirect,       // 2>
    ErrorAppendRedirect, // 2>>
    ErrorToOutput,       // 2>&1
    BothRedirect,        // &> (bash extension)
}

fn tokenize(input: &str) -> Vec<Token> {
    // Handle >> before > (longest match first)
    // Handle 2>> before 2>
    // Handle 2>&1 specially
    // Split on whitespace, keeping redirects as separate tokens
}
```

**Step 2**: Parse redirections

```rust
pub fn parse_command(input: &str) -> Result<CommandWithRedirects> {
    let tokens = tokenize(input);

    // Extract redirections
    let mut redirects = Vec::new();
    let mut command_tokens = Vec::new();

    let mut i = 0;
    while i < tokens.len() {
        match &tokens[i] {
            Token::OutputRedirect => {
                let file = expect_word(&tokens[i+1])?;
                redirects.push(Redirection::Output { file });
                i += 2;
            }
            Token::InputRedirect => {
                let file = expect_word(&tokens[i+1])?;
                redirects.push(Redirection::Input { file });
                i += 2;
            }
            // ... other redirection types
            Token::Word(w) => {
                command_tokens.push(w.clone());
                i += 1;
            }
        }
    }

    // Parse command from remaining tokens
    let cmd = parse_base_command(&command_tokens)?;

    Ok(CommandWithRedirects { cmd, redirects })
}
```

**Step 3**: Validation

```rust
fn validate_redirections(redirects: &[Redirection]) -> Result<()> {
    // Check for conflicting redirections
    let has_stdout = redirects.iter().any(|r| matches!(r,
        Redirection::Output { .. } | Redirection::Append { .. }
    ));
    let has_both = redirects.iter().any(|r| matches!(r,
        Redirection::BothOutput { .. }
    ));

    if has_stdout && has_both {
        anyhow::bail!("Cannot redirect stdout twice");
    }

    // Check for duplicate stderr redirects
    // Check for 2>&1 with explicit stderr redirect
    // ... other validation rules

    Ok(())
}
```

---

## Implementation Plan

### Phase 1: Parser Extensions (Week 1)

**Files to Modify**:
- `src/parser.rs` - Add tokenization and redirection parsing
- `src/lib.rs` (NEW) - Make parser testable as library

**Tasks**:
- [ ] Create Token enum
- [ ] Implement tokenize() function
- [ ] Handle `>`, `>>`, `<`, `2>`, `2>>`, `2>&1`, `&>`
- [ ] Parse redirections into Redirection enum
- [ ] Add `redirects: Vec<Redirection>` to all Command variants
- [ ] Write 20+ parser tests for redirection edge cases

**Test Cases**:
```rust
#[test]
fn parse_output_redirect() {
    let cmd = parse_command("ls > output.txt").unwrap();
    assert_eq!(cmd.redirects, vec![Redirection::Output { file: "output.txt".into() }]);
}

#[test]
fn parse_multiple_redirects() {
    let cmd = parse_command("cat < input.txt > output.txt 2> error.log").unwrap();
    assert_eq!(cmd.redirects.len(), 3);
}

#[test]
fn parse_error_to_output() {
    let cmd = parse_command("make 2>&1").unwrap();
    assert!(matches!(cmd.redirects[0], Redirection::ErrorToOutput));
}
```

### Phase 2: File Descriptor Setup (Week 1-2)

**Files to Create**:
- `src/redirection.rs` - Redirection execution engine

**Core Types**:
```rust
/// Setup result for a redirection
pub struct RedirectSetup {
    /// Original stdin/stdout/stderr (for restoration)
    original_fds: SavedFds,

    /// Files opened for redirection (need cleanup)
    opened_files: Vec<File>,

    /// File modifications (for undo)
    modifications: Vec<FileModification>,
}

impl RedirectSetup {
    /// Apply redirections before command execution
    pub fn setup(redirects: &[Redirection], state: &ShellState) -> Result<Self>;

    /// Restore original file descriptors after execution
    pub fn restore(self) -> Result<()>;

    /// Get stdio configuration for external commands
    pub fn stdio_config(&self) -> (Stdio, Stdio, Stdio);

    /// Record modifications for undo
    pub fn record_undo(self, state: &mut ShellState) -> Result<()>;
}
```

**Implementation**:
```rust
pub fn setup(redirects: &[Redirection], state: &ShellState) -> Result<Self> {
    let mut opened_files = Vec::new();
    let mut modifications = Vec::new();

    for redirect in redirects {
        match redirect {
            Redirection::Output { file } => {
                let path = state.resolve_path(file);

                // Save original if file exists
                if path.exists() {
                    let original = fs::read(&path)?;
                    modifications.push(FileModification::Truncated {
                        path: path.clone(),
                        original_content: original,
                    });
                } else {
                    modifications.push(FileModification::Created {
                        path: path.clone(),
                    });
                }

                // Open for writing (truncate)
                let file = File::create(&path)?;
                opened_files.push(file);
            }

            Redirection::Append { file } => {
                let path = state.resolve_path(file);
                let original_size = if path.exists() {
                    fs::metadata(&path)?.len()
                } else {
                    0
                };

                modifications.push(FileModification::Appended {
                    path: path.clone(),
                    original_size,
                });

                let file = OpenOptions::new()
                    .create(true)
                    .append(true)
                    .open(&path)?;
                opened_files.push(file);
            }

            // ... other redirection types
        }
    }

    Ok(RedirectSetup {
        original_fds: save_current_fds()?,
        opened_files,
        modifications,
    })
}
```

### Phase 3: Built-in Command Integration (Week 2)

**Challenge**: Built-ins use `println!()` - need to capture stdout

**Approach 1**: Gag crate (capture stdio)
```rust
use gag::BufferRedirect;

let mut buf = Vec::new();
{
    let mut redirect = BufferRedirect::stdout(&mut buf)?;
    commands::mkdir(state, path, false)?;
    drop(redirect);
}

// buf now contains captured output
fs::write(redirect_file, &buf)?;
```

**Approach 2**: Return String from commands (invasive refactor)
```rust
// Modify all command functions
pub fn mkdir(state: &mut ShellState, path: &str, verbose: bool) -> Result<String> {
    // ...
    Ok(if verbose {
        format!("Created directory: {}", path)
    } else {
        String::new()
    })
}
```

**Decision**: **Approach 1 (gag crate)** - Less invasive
- Rationale: Don't change command signatures
- Trade-off: Adds dependency, slightly slower
- Fallback: If gag doesn't work, use Approach 2

### Phase 4: External Command Integration (Week 2)

**Using std::process::Stdio**:
```rust
use std::process::{Command, Stdio};

pub fn execute_external_with_redirects(
    program: &str,
    args: &[String],
    redirects: &[Redirection],
    state: &ShellState,
) -> Result<i32> {
    let setup = RedirectSetup::setup(redirects, state)?;
    let (stdin_cfg, stdout_cfg, stderr_cfg) = setup.stdio_config();

    let status = Command::new(program)
        .args(args)
        .stdin(stdin_cfg)
        .stdout(stdout_cfg)
        .stderr(stderr_cfg)
        .status()?;

    // Cleanup
    setup.record_undo(state)?;
    setup.restore()?;

    Ok(exit_code_from_status(status))
}
```

**SIGINT Handling**: Already works (from Phase 6 M1)
- Redirections don't affect signal handling
- Child processes still receive SIGINT
- Files are closed cleanly

### Phase 5: Undo/Redo Integration (Week 2)

**Extend Operation Type**:
```rust
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum OperationType {
    // Existing types
    MkDir,
    RmDir,
    CreateFile,
    DeleteFile,

    // NEW: File modification operations
    TruncateFile { original_content: Vec<u8> },
    AppendFile { original_size: u64 },
}

impl OperationType {
    pub fn inverse(&self) -> Option<Self> {
        match self {
            // Existing inverses
            OperationType::MkDir => Some(OperationType::RmDir),
            OperationType::RmDir => Some(OperationType::MkDir),

            // NEW: File modification inverses
            OperationType::TruncateFile { original_content } => {
                Some(OperationType::RestoreFile {
                    content: original_content.clone(),
                })
            }
            OperationType::AppendFile { original_size } => {
                Some(OperationType::TruncateToSize {
                    size: *original_size,
                })
            }
        }
    }
}
```

**Recording File Modifications**:
```rust
// After successful redirection execution
for modification in setup.modifications {
    let op = Operation {
        id: Uuid::new_v4(),
        timestamp: Utc::now(),
        op_type: match modification {
            FileModification::Created { path } => OperationType::CreateFile,
            FileModification::Truncated { path, original_content } => {
                OperationType::TruncateFile { original_content }
            }
            FileModification::Appended { path, original_size } => {
                OperationType::AppendFile { original_size }
            }
        },
        path: modification.path(),
        metadata: None,
        undone: false,
        transaction_id: state.active_transaction.as_ref().map(|t| t.id),
    };

    state.record_operation(op);
}
```

---

## Testing Strategy

### Unit Tests (20+ tests)

**Parser Tests**:
```rust
#[test] fn parse_output_redirect()
#[test] fn parse_append_redirect()
#[test] fn parse_input_redirect()
#[test] fn parse_error_redirect()
#[test] fn parse_error_to_output()
#[test] fn parse_multiple_redirects()
#[test] fn parse_redirect_with_quotes()
#[test] fn parse_redirect_order_independence()
#[test] fn reject_invalid_redirect_syntax()
#[test] fn reject_missing_redirect_target()
```

**Redirection Engine Tests**:
```rust
#[test] fn redirect_stdout_creates_file()
#[test] fn redirect_stdout_truncates_existing()
#[test] fn redirect_append_creates_file()
#[test] fn redirect_append_appends_to_existing()
#[test] fn redirect_stdin_reads_file()
#[test] fn redirect_error_to_file()
#[test] fn redirect_error_to_stdout()
#[test] fn multiple_redirects_work()
#[test] fn redirect_failure_leaves_fs_unchanged()
#[test] fn redirect_cleanup_on_error()
```

### Integration Tests (15+ tests)

**External Commands**:
```rust
#[test]
fn external_cmd_redirect_output() {
    let temp = test_sandbox("redirect_output");
    let mut state = ShellState::new(temp.path().to_str().unwrap()).unwrap();

    execute_line(&mut state, "echo hello > output.txt").unwrap();

    let content = fs::read_to_string(temp.path().join("output.txt")).unwrap();
    assert_eq!(content.trim(), "hello");
}

#[test]
fn external_cmd_redirect_append() {
    let temp = test_sandbox("redirect_append");
    let mut state = ShellState::new(temp.path().to_str().unwrap()).unwrap();

    execute_line(&mut state, "echo line1 > file.txt").unwrap();
    execute_line(&mut state, "echo line2 >> file.txt").unwrap();

    let content = fs::read_to_string(temp.path().join("file.txt")).unwrap();
    assert!(content.contains("line1"));
    assert!(content.contains("line2"));
}

#[test]
fn external_cmd_redirect_input() {
    let temp = test_sandbox("redirect_input");
    let mut state = ShellState::new(temp.path().to_str().unwrap()).unwrap();

    fs::write(temp.path().join("input.txt"), b"test input").unwrap();
    execute_line(&mut state, "cat < input.txt > output.txt").unwrap();

    let content = fs::read_to_string(temp.path().join("output.txt")).unwrap();
    assert_eq!(content, "test input");
}
```

**Built-in Commands**:
```rust
#[test]
fn builtin_mkdir_redirect() {
    let temp = test_sandbox("mkdir_redirect");
    let mut state = ShellState::new(temp.path().to_str().unwrap()).unwrap();

    execute_line(&mut state, "mkdir test_dir > log.txt").unwrap();

    assert!(temp.path().join("test_dir").exists());
    let log = fs::read_to_string(temp.path().join("log.txt")).unwrap();
    // Built-ins may not produce output, or capture verbose output
}
```

**Undo/Redo with Redirections**:
```rust
#[test]
fn undo_redirect_created_file() {
    let temp = test_sandbox("undo_redirect");
    let mut state = ShellState::new(temp.path().to_str().unwrap()).unwrap();

    execute_line(&mut state, "echo test > newfile.txt").unwrap();
    assert!(temp.path().join("newfile.txt").exists());

    execute_line(&mut state, "undo").unwrap();
    assert!(!temp.path().join("newfile.txt").exists());
}

#[test]
fn undo_redirect_truncated_file() {
    let temp = test_sandbox("undo_truncate");
    let mut state = ShellState::new(temp.path().to_str().unwrap()).unwrap();

    fs::write(temp.path().join("file.txt"), b"original content").unwrap();

    execute_line(&mut state, "echo new > file.txt").unwrap();
    let content = fs::read_to_string(temp.path().join("file.txt")).unwrap();
    assert!(content.contains("new"));

    execute_line(&mut state, "undo").unwrap();
    let restored = fs::read_to_string(temp.path().join("file.txt")).unwrap();
    assert_eq!(restored, "original content");
}
```

### Property Tests (Seam 0↔1 Extension)

**NEW Theorems Needed** (to be proven in Lean 4):

```lean
-- File modification reversibility
theorem truncate_restore_reversible (path : Path) (content : ByteSeq) :
  restoreFile path content (truncateFile path fs) = fs :=
  sorry -- TO PROVE

theorem append_truncate_reversible (path : Path) (size : Nat) (data : ByteSeq) :
  truncateToSize path size (appendFile path data fs) = fs :=
  sorry -- TO PROVE

-- Redirection doesn't affect command semantics
theorem redirect_preserves_semantics (cmd : Command) (redirect : Redirection) :
  executeWithRedirect cmd redirect fs ≡ execute cmd fs :=
  sorry -- TO PROVE (modulo file contents)
```

**Property Tests**:
```rust
#[test]
fn prop_truncate_restore_reversible() {
    proptest!(|(original in any::<Vec<u8>>(), new_content in any::<Vec<u8>>())| {
        let temp = test_sandbox("truncate");
        let file = temp.path().join("file.txt");

        // Write original
        fs::write(&file, &original)?;

        // Truncate with new content
        fs::write(&file, &new_content)?;

        // Restore original
        fs::write(&file, &original)?;

        // Verify equivalence
        let restored = fs::read(&file)?;
        prop_assert_eq!(restored, original);
    });
}
```

---

## Proof Requirements

### Lean 4 Theorems to Prove

**1. File Truncation Reversibility**
```lean
-- Proving that saving original content allows reversible truncation
theorem truncateWithSave_reversible
  (path : Path)
  (original : FileContent)
  (fs : Filesystem)
  (h_exists : fileExists path fs = true)
  (h_content : getFileContent path fs = some original) :
  writeFile path original (truncateFile path fs) = fs :=
by
  -- Save original content
  -- Truncate file
  -- Write original back
  -- Prove equivalence to original state
  sorry
```

**2. File Append Reversibility**
```lean
theorem appendWithSizeSave_reversible
  (path : Path)
  (original_size : Nat)
  (data : List Byte)
  (fs : Filesystem)
  (h_exists : fileExists path fs = true)
  (h_size : getFileSize path fs = some original_size) :
  truncateToSize path original_size (appendToFile path data fs) = fs :=
by
  -- Record original size
  -- Append data
  -- Truncate to original size
  -- Prove equivalence
  sorry
```

**3. Redirection Independence**
```lean
-- Redirections don't affect other files
theorem redirect_independence
  (cmd : Command)
  (redirect_path : Path)
  (other_path : Path)
  (h_distinct : redirect_path ≠ other_path)
  (fs : Filesystem) :
  getFileContent other_path (executeWithRedirect cmd redirect_path fs)
  = getFileContent other_path fs :=
by
  -- Execute with redirection
  -- Show other paths unchanged
  sorry
```

**Proof Complexity**: Medium
- Builds on existing file operation theorems
- No new concepts (just composition)
- Timeline: 1 week in Lean 4, then port to other 5 systems

---

## Edge Cases & Error Handling

### Edge Case 1: Redirect to Same File as Input

```bash
cat < file.txt > file.txt  # DANGEROUS - data race
```

**POSIX Behavior**: Undefined (bash truncates before reading → empty file)

**Our Behavior**: **Detect and reject**
```rust
fn validate_no_input_output_conflict(redirects: &[Redirection]) -> Result<()> {
    let input_files: HashSet<_> = redirects.iter()
        .filter_map(|r| match r {
            Redirection::Input { file } => Some(file),
            _ => None,
        })
        .collect();

    let output_files: HashSet<_> = redirects.iter()
        .filter_map(|r| match r {
            Redirection::Output { file } | Redirection::Append { file } => Some(file),
            _ => None,
        })
        .collect();

    if !input_files.is_disjoint(&output_files) {
        anyhow::bail!("Cannot redirect input and output to the same file");
    }

    Ok(())
}
```

**Rationale**: Safer than POSIX, prevents data loss

### Edge Case 2: Permission Denied

```bash
echo test > /root/file.txt  # Permission denied
```

**Behavior**: Fail before executing command
```rust
fn validate_redirect_permissions(redirect: &Redirection) -> Result<()> {
    match redirect {
        Redirection::Output { file } | Redirection::Append { file } => {
            let path = Path::new(file);

            // Check parent directory is writable
            let parent = path.parent()
                .ok_or_else(|| anyhow::anyhow!("Invalid path"))?;

            if !parent.exists() {
                anyhow::bail!("Parent directory does not exist: {}", parent.display());
            }

            // On Unix, check if we can write
            #[cfg(unix)]
            {
                use std::os::unix::fs::PermissionsExt;
                let meta = fs::metadata(parent)?;
                if meta.permissions().mode() & 0o200 == 0 {
                    anyhow::bail!("Permission denied: {}", parent.display());
                }
            }

            Ok(())
        }
        // ... other cases
    }
}
```

### Edge Case 3: Disk Full

```bash
cat large.txt >> small_partition.txt  # ENOSPC
```

**Behavior**: Atomic failure, no partial writes
```rust
fn atomic_write(path: &Path, content: &[u8]) -> Result<()> {
    let temp = path.with_extension(".tmp");

    // Write to temporary file
    fs::write(&temp, content)?;

    // Atomic rename
    fs::rename(&temp, path)?;

    Ok(())
}
```

**Undo**: Delete partial file or restore original

### Edge Case 4: Multiple Redirects to Same File

```bash
cmd > file.txt 2> file.txt  # Interleaved output
```

**POSIX Behavior**: Both write to same file (interleaved, undefined order)

**Our Behavior**: **Allow but warn**
- Detect duplicate file targets
- Warn user about potential interleaving
- Still allow (POSIX compatibility)

---

## Performance Considerations

### Overhead Analysis

**Redirection Setup Cost**:
- File open: ~100μs
- Save original content (1KB file): ~50μs
- File descriptor setup: ~10μs
- **Total**: ~160μs per redirection

**Acceptable**: << 1ms for typical cases

**Optimization Opportunities**:
1. **Lazy content save**: Only save if file exists
2. **Streaming for large files**: Don't load entire file into memory
3. **mmap for large restores**: Fast content restoration

**Target**: < 500μs overhead for typical redirections

### Memory Usage

**Worst Case**: Truncating a large file
- Need to save original content in memory
- 100MB file → 100MB RAM for undo

**Mitigation**:
1. **Compression**: Compress original content with zstd
   - 100MB file → ~10MB compressed (typical)
   - ~10x memory reduction

2. **Copy-on-write**: Use reflinks on supported filesystems
   - Zero memory overhead
   - Instant "copy" of original

3. **Size limit**: Warn if file > 10MB
   ```rust
   if original_size > 10 * 1024 * 1024 {
       eprintln!("Warning: Saving 10MB+ file for undo. This may use significant memory.");
   }
   ```

**Decision**: Start simple (full save), optimize later if needed

---

## File Modifications

### New Files

**src/redirection.rs** (~400 lines):
- Redirection enum
- RedirectSetup struct
- FileModification enum
- setup(), restore(), record_undo()
- Validation functions

**tests/redirection_tests.rs** (~300 lines):
- 20+ unit tests for parser
- 15+ integration tests for execution
- Edge case tests

### Modified Files

**src/parser.rs** (+150 lines):
- Token enum
- tokenize() function
- parse_redirections()
- Update parse_command() to extract redirects
- Update all Command variants to include `redirects` field

**src/executable.rs** (+50 lines):
- Update execute() to handle redirections
- Call RedirectSetup::setup() before execution
- Integrate with undo system

**src/state.rs** (+30 lines):
- Add FileModification to OperationType enum
- Add inverse() cases for truncate/append
- Serialize/deserialize support

**src/external.rs** (+80 lines):
- execute_external_with_redirects()
- stdio_config_from_redirects()
- Integration with RedirectSetup

**Cargo.toml**:
- Add `gag = "1.0"` for stdout capture (optional, for built-ins)

### Lines of Code Estimate

| Component | Current | After M2 | Delta |
|-----------|---------|----------|-------|
| src/ | ~1,800 | ~2,500 | +700 |
| tests/ | ~800 | ~1,200 | +400 |
| **Total** | ~2,600 | ~3,700 | **+1,100** |

**Complexity**: ~40% increase in implementation

---

## Deliverables

### Version 0.8.0 Release

**Features**:
- ✅ Output redirection (`>`, `>>`)
- ✅ Input redirection (`<`)
- ✅ Error redirection (`2>`, `2>>`, `2>&1`)
- ✅ Bash-style `&>` shorthand
- ✅ Multiple redirections per command
- ✅ Atomic file operations
- ✅ Undo/redo for file modifications
- ✅ Proper error handling and validation

**Testing**:
- 20+ parser tests
- 15+ integration tests
- 5+ property tests (new theorems)
- All existing tests still passing

**Documentation**:
- Update COMPREHENSIVE_EXAMPLES.md with redirection examples
- Create REDIRECTION_GUIDE.md
- Update POSIX_COMPLIANCE.md progress
- Update STATE.scm

**Performance**:
- Cold start: < 10ms (acceptable < 2ms increase)
- Redirection overhead: < 500μs typical case
- Memory: < 10MB for typical undo history

---

## Verification & Proof Plan

### Lean 4 Proofs (1-2 weeks)

**New File**: `proofs/lean4/FileRedirections.lean`

**Theorems to Prove**:
1. `truncateWithSave_reversible` - Save+truncate+restore = identity
2. `appendWithSizeSave_reversible` - Record+append+truncate = identity
3. `redirect_independence` - Redirections don't affect other files
4. `redirect_composition` - Multiple redirections compose correctly
5. `redirect_atomicity` - Failures leave filesystem unchanged

**Cross-System Validation**:
- Port all 5 theorems to Coq, Agda, Isabelle, Mizar
- Add Z3 SMT encoding for automated checking
- Update proof count: 256 → ~280 theorems

**Timeline**: 1 week Lean 4, 1 week porting to other systems

### Property Tests (Seam 0↔1 Extension)

**tests/property_tests.rs** - Add 5 new tests:
```rust
#[test] fn prop_truncate_restore_reversible()
#[test] fn prop_append_truncate_reversible()
#[test] fn prop_redirect_independence()
#[test] fn prop_redirect_atomicity_on_error()
#[test] fn prop_multiple_redirects_commute()
```

**Coverage**: Validate all 5 new Lean 4 theorems

---

## Risks & Mitigations

### Risk 1: Stdout Capture Complexity

**Risk**: Capturing built-in output is tricky
**Mitigation**: Use battle-tested `gag` crate
**Fallback**: Refactor commands to return String

### Risk 2: File Descriptor Leaks

**Risk**: Forgetting to close files
**Mitigation**: Use RAII guards (RedirectSetup Drop impl)
**Detection**: Add leak tests

### Risk 3: Race Conditions

**Risk**: File modified between save and execution
**Mitigation**: Check mtime before restore
**Fallback**: Warn user, don't restore

### Risk 4: Large File Memory Usage

**Risk**: 100MB file → 100MB RAM for undo
**Mitigation**: Compression or size limits
**Monitoring**: Track total undo history size

---

## Success Criteria

### Functional Requirements

- ✅ All POSIX redirection operators work
- ✅ External commands redirect correctly
- ✅ Built-in commands redirect (or reasonably handle)
- ✅ Undo reverses file modifications
- ✅ Atomic operations (no partial state on error)
- ✅ Proper error messages

### Quality Requirements

- ✅ All existing tests pass
- ✅ 35+ new tests (20 unit + 15 integration)
- ✅ Zero compiler warnings
- ✅ Zero clippy warnings
- ✅ Documentation updated

### Performance Requirements

- ✅ Cold start: < 10ms
- ✅ Redirection overhead: < 500μs
- ✅ Memory: < 10MB for typical usage

---

## Timeline & Milestones

### Week 1: Parser & Design
- **Day 1-2**: Design doc (this file) + tokenizer implementation
- **Day 3-4**: Parser extensions + tests
- **Day 5**: Review & refine

**Milestone**: Parser tests passing (20+ tests)

### Week 2: Implementation
- **Day 1-2**: RedirectSetup implementation
- **Day 3**: External command integration
- **Day 4**: Built-in command integration (if possible)
- **Day 5**: Undo/redo integration

**Milestone**: Integration tests passing (15+ tests)

### Week 3: Polish & Proofs
- **Day 1-2**: Lean 4 theorem proofs
- **Day 3**: Property tests
- **Day 4**: Documentation
- **Day 5**: Final testing & release

**Milestone**: v0.8.0 release

---

## Next Steps (Immediate)

1. **Create tokenizer** - Parse `>`, `>>`, `<`, `2>`, etc.
2. **Extend Command enum** - Add `redirects: Vec<Redirection>` field
3. **Write parser tests** - TDD approach for redirection syntax
4. **Update ExecutableCommand** - Handle redirections in execute()

**First File to Create**: `src/redirection.rs` (types and validation)

---

## References

- **POSIX Shell Spec**: IEEE Std 1003.1-2017, Section 2.7 (Redirection)
- **Bash Manual**: Chapter 3.6 (Redirections)
- **Rust std::process**: https://doc.rust-lang.org/std/process/
- **gag crate**: https://docs.rs/gag/ (stdio capture)

---

**Status**: 📋 Design Complete - Ready for Implementation
**Next**: Create src/redirection.rs and begin parser extensions
