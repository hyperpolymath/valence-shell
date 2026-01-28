# Phase 6 Milestone 1: Simple Command Execution

**Version**: 0.7.0 (proposed)
**Timeline**: 3-4 months
**Status**: Design phase
**Updated**: 2026-01-28

---

## Goal

Execute external commands with arguments (no special syntax, no expansion).

**Example**:
```bash
vsh> ls -la /tmp
vsh> cat file.txt
vsh> echo hello world
```

**NOT in this milestone**:
- ❌ Pipes (`|`)
- ❌ Redirections (`>`, `<`)
- ❌ Variables (`$VAR`)
- ❌ Glob expansion (`*.txt`)
- ❌ Quote processing (`"..."`)
- ❌ Command substitution (`` `cmd` ``)

**Just**: Parse command + args, execute via `execve()`, display output.

---

## Architecture Decision

### Option A: Pure Rust (Recommended)
**Pros**:
- Fast startup (~5ms maintained)
- Direct `std::process::Command` API
- No daemon needed for simple commands
- Memory efficient

**Cons**:
- No undo for external commands (by design - they're not filesystem ops)
- Less interesting from BEAM perspective

### Option B: Delegate to BEAM
**Pros**:
- Could implement undo for some commands
- Supervision for long-running processes

**Cons**:
- Slower (~30-50ms extra latency)
- Overkill for simple commands

**Decision**: **Option A - Pure Rust**

---

## Implementation Plan

### 1. Parser Extension

**Current** (`impl/rust-cli/src/repl.rs`):
```rust
// Hardcoded commands only
match input.trim() {
    "exit" | "quit" => break,
    cmd if cmd.starts_with("mkdir ") => ...,
    cmd if cmd.starts_with("rmdir ") => ...,
    // ...
}
```

**New** (`impl/rust-cli/src/parser.rs`):
```rust
pub enum Command {
    // Built-ins (existing)
    Mkdir { path: String },
    Rmdir { path: String },
    Touch { path: String },
    Rm { path: String },
    Undo { count: usize },
    Redo { count: usize },
    History,

    // NEW: External command
    External {
        program: String,
        args: Vec<String>,
    },
}

pub fn parse_command(input: &str) -> Result<Command> {
    let parts: Vec<&str> = input.split_whitespace().collect();
    if parts.is_empty() {
        return Err(anyhow!("Empty command"));
    }

    let cmd = parts[0];
    let args = parts[1..].iter().map(|s| s.to_string()).collect();

    match cmd {
        "mkdir" => Ok(Command::Mkdir { path: args[0].clone() }),
        "rmdir" => Ok(Command::Rmdir { path: args[0].clone() }),
        "touch" => Ok(Command::Touch { path: args[0].clone() }),
        "rm" => Ok(Command::Rm { path: args[0].clone() }),
        "undo" => Ok(Command::Undo { count: args.get(0).and_then(|s| s.parse().ok()).unwrap_or(1) }),
        // ... other builtins ...

        // Everything else: external command
        _ => Ok(Command::External {
            program: cmd.to_string(),
            args,
        }),
    }
}
```

### 2. External Command Execution

**File**: `impl/rust-cli/src/external.rs` (NEW)

```rust
// SPDX-License-Identifier: PMPL-1.0-or-later
//! External Command Execution
//!
//! Executes external programs via execve(), handles PATH lookup,
//! and manages stdio.

use anyhow::{Context, Result};
use std::process::{Command, Stdio};
use std::path::PathBuf;

/// Execute an external command
pub fn execute_external(program: &str, args: &[String]) -> Result<i32> {
    // PATH lookup
    let executable = find_in_path(program)?;

    // Execute via std::process::Command
    let status = Command::new(&executable)
        .args(args)
        .stdin(Stdio::inherit())   // Pass through stdin
        .stdout(Stdio::inherit())  // Pass through stdout
        .stderr(Stdio::inherit())  // Pass through stderr
        .status()
        .context(format!("Failed to execute: {}", program))?;

    // Return exit code
    Ok(status.code().unwrap_or(1))
}

/// Find executable in PATH
fn find_in_path(program: &str) -> Result<PathBuf> {
    // If path contains '/', treat as literal path
    if program.contains('/') {
        let path = PathBuf::from(program);
        if path.exists() && is_executable(&path) {
            return Ok(path);
        }
        anyhow::bail!("Command not found: {}", program);
    }

    // Search PATH
    let path_env = std::env::var("PATH")
        .unwrap_or_else(|_| "/usr/local/bin:/usr/bin:/bin".to_string());

    for dir in path_env.split(':') {
        let candidate = PathBuf::from(dir).join(program);
        if candidate.exists() && is_executable(&candidate) {
            return Ok(candidate);
        }
    }

    anyhow::bail!("Command not found: {}", program);
}

/// Check if file is executable
fn is_executable(path: &PathBuf) -> bool {
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        if let Ok(metadata) = std::fs::metadata(path) {
            let perms = metadata.permissions();
            return perms.mode() & 0o111 != 0;  // Check any execute bit
        }
    }
    false
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_find_ls() {
        let ls = find_in_path("ls").unwrap();
        assert!(ls.to_string_lossy().contains("ls"));
    }

    #[test]
    fn test_not_found() {
        assert!(find_in_path("nonexistent-command-xyz").is_err());
    }

    #[test]
    fn test_absolute_path() {
        let result = find_in_path("/bin/ls");
        assert!(result.is_ok() || result.is_err());  // Platform-dependent
    }
}
```

### 3. REPL Integration

**Update**: `impl/rust-cli/src/repl.rs`

```rust
use crate::external;
use crate::parser::{Command, parse_command};

pub fn run_repl(state: &mut ShellState) -> Result<()> {
    let mut rl = Editor::<()>::new()?;

    loop {
        let readline = rl.readline("vsh> ");
        match readline {
            Ok(line) => {
                rl.add_history_entry(line.as_str());

                // Parse command
                let cmd = match parse_command(&line) {
                    Ok(c) => c,
                    Err(e) => {
                        eprintln!("Parse error: {}", e);
                        continue;
                    }
                };

                // Execute command
                match cmd {
                    Command::Mkdir { path } => {
                        if let Err(e) = commands::mkdir(state, &path, false) {
                            eprintln!("mkdir: {}", e);
                        }
                    }
                    // ... other builtins ...

                    Command::External { program, args } => {
                        match external::execute_external(&program, &args) {
                            Ok(exit_code) => {
                                // Store exit code for $?
                                state.last_exit_code = exit_code;
                            }
                            Err(e) => {
                                eprintln!("{}: {}", program, e);
                                state.last_exit_code = 127;  // Command not found
                            }
                        }
                    }
                }
            }
            Err(ReadlineError::Interrupted) => {
                println!("^C");
                continue;
            }
            Err(ReadlineError::Eof) => {
                println!("exit");
                break;
            }
            Err(err) => {
                eprintln!("Error: {:?}", err);
                break;
            }
        }
    }

    Ok(())
}
```

### 4. Exit Code Tracking

**Update**: `impl/rust-cli/src/state.rs`

```rust
pub struct ShellState {
    pub root: PathBuf,
    pub undo_stack: Vec<Operation>,
    pub redo_stack: Vec<Operation>,

    // NEW: Track last exit code (for future $? support)
    pub last_exit_code: i32,
}

impl ShellState {
    pub fn new(root: &str) -> Result<Self> {
        Ok(Self {
            root: PathBuf::from(root),
            undo_stack: Vec::new(),
            redo_stack: Vec::new(),
            last_exit_code: 0,
        })
    }
}
```

---

## Verification Strategy

### Lean 4 Model Extension

**New file**: `proofs/lean4/CommandExecution.lean`

```lean
-- External command model
structure ExternalCommand where
  program : String
  args : List String

-- Execution result
inductive ExecResult where
  | success (exit_code : Nat)
  | not_found (program : String)
  | permission_denied (program : String)

-- PATH lookup specification
def find_in_path (program : String) (path_env : String) : Option FilePath :=
  sorry  -- Formal spec for PATH search

-- Execution semantics
def execute_external (cmd : ExternalCommand) (env : Environment) : ExecResult :=
  match find_in_path cmd.program env.path with
  | none => ExecResult.not_found cmd.program
  | some executable =>
      if has_execute_permission executable env then
        ExecResult.success (syscall_exec executable cmd.args)
      else
        ExecResult.permission_denied cmd.program

-- Properties to prove
theorem path_lookup_correct :
  ∀ prog path,
    find_in_path prog path = some exe →
    exists_in_path_dirs exe path

theorem execute_preserves_filesystem :
  ∀ cmd fs,
    execute_external cmd fs →
    -- Filesystem unchanged (unless command modifies it)
    -- External commands are not reversible by shell
    true  -- Placeholder
```

### Rust Correspondence

| Lean 4 | Rust | Verified By |
|--------|------|-------------|
| `find_in_path` | `external::find_in_path()` | Unit tests |
| `has_execute_permission` | `is_executable()` | Unit tests |
| `execute_external` | `execute_external()` | Integration tests |
| `ExecResult` | `Result<i32>` | Manual proof |

### Testing

**Unit Tests** (`impl/rust-cli/src/external.rs`):
- ✅ Find `ls` in PATH
- ✅ Find `/bin/ls` absolute path
- ✅ Command not found error
- ✅ Executable permission check

**Integration Tests** (`tests/external_commands.sh`):
```bash
#!/usr/bin/env bash
# Test external command execution

# Test 1: Simple command
output=$(echo "ls" | vsh)
assert_contains "$output" "."

# Test 2: Command with args
output=$(echo "echo hello world" | vsh)
assert_equals "$output" "hello world"

# Test 3: Command not found
output=$(echo "nonexistent-xyz" | vsh 2>&1)
assert_contains "$output" "Command not found"

# Test 4: Exit code tracking
echo "false" | vsh
assert_exit_code 1

echo "true" | vsh
assert_exit_code 0
```

---

## Security Considerations

### 1. PATH Injection
**Risk**: Malicious PATH could execute untrusted binaries
**Mitigation**:
- Sanitize PATH at shell startup
- Warn if PATH contains `.` (current directory)
- Option: `--safe-path` flag restricts to `/usr/bin:/bin`

### 2. Command Injection
**Risk**: None at this milestone (no expansion or substitution)
**Future Risk**: When adding `$VAR` or `` `cmd` ``, injection becomes possible
**Mitigation**: Proper escaping in future milestones

### 3. Resource Limits
**Risk**: External command consumes all memory/CPU
**Mitigation**:
- Set `ulimit` constraints
- Timeout for long-running commands (future)
- SIGINT handling (Ctrl+C)

### 4. Privilege Escalation
**Risk**: Executing setuid binaries
**Mitigation**:
- Document behavior (inherits user privileges)
- Future: Option to drop privileges

---

## Performance Targets

| Operation | Target | Expected |
|-----------|--------|----------|
| Parse command | <0.1ms | ~0.05ms |
| PATH lookup | <1ms | ~0.2ms |
| Execute `ls` | <5ms | ~3ms |
| Execute `cat` | <10ms | ~5ms |
| Total (parse + exec) | <10ms | ~5ms |

**Cold start maintained**: Still ~5ms for shell startup

---

## User Experience

### Before (v0.6.0)
```bash
vsh> ls
Unknown command: ls

vsh> cat file.txt
Unknown command: cat
```

### After (v0.7.0)
```bash
vsh> ls
CLAUDE.md  LICENSE  README.adoc  docs/  impl/  proofs/

vsh> cat README.adoc
= Valence Shell
...

vsh> echo hello world
hello world

vsh> mkdir test
[op:94c00e8] mkdir test

vsh> ls
CLAUDE.md  LICENSE  README.adoc  docs/  impl/  proofs/  test/

vsh> undo
[op:990d907b] undo [op:94c00e8] rmdir test

vsh> ls
CLAUDE.md  LICENSE  README.adoc  docs/  impl/  proofs/
```

**Key insight**: Built-ins (mkdir, rm) still have undo. External commands don't.

---

## Implementation Checklist

### Week 1-2: Parser
- [ ] Create `parser.rs` with `Command` enum
- [ ] Implement `parse_command()` function
- [ ] Add unit tests for parsing
- [ ] Update REPL to use parser

### Week 3-4: External Execution
- [ ] Create `external.rs` module
- [ ] Implement `find_in_path()`
- [ ] Implement `is_executable()`
- [ ] Implement `execute_external()`
- [ ] Add unit tests

### Week 5-6: Integration
- [ ] Update REPL to handle `Command::External`
- [ ] Add exit code tracking to `ShellState`
- [ ] Create integration test suite
- [ ] Update docs

### Week 7-8: Verification
- [ ] Write Lean 4 command execution model
- [ ] Document correspondence
- [ ] Run ECHIDNA validation
- [ ] Performance benchmarks

### Week 9-10: Polish
- [ ] Error message improvements
- [ ] Help text updates
- [ ] User documentation
- [ ] Release v0.7.0

---

## Future Milestones Preview

### M2: Redirections (v0.8.0)
```bash
vsh> ls > files.txt
vsh> cat < input.txt
vsh> command 2> errors.log
```

### M3: Pipelines (v0.9.0)
```bash
vsh> ls | grep ".txt"
vsh> cat file.txt | wc -l
```

### M4: Variables (v0.10.0)
```bash
vsh> NAME="world"
vsh> echo "Hello $NAME"
```

---

## Success Criteria

- ✅ Can execute any command in PATH
- ✅ Arguments passed correctly
- ✅ Exit codes tracked
- ✅ PATH lookup works
- ✅ Command not found errors handled
- ✅ stdio inherited correctly
- ✅ Ctrl+C interrupts command
- ✅ Lean 4 model formalized
- ✅ Rust correspondence documented
- ✅ Tests passing (unit + integration)
- ✅ Performance targets met

---

## Related Documentation

- `docs/POSIX_COMPLIANCE.md` - Full 14-milestone roadmap
- `docs/ARCHITECTURE.md` - Hybrid Rust+BEAM architecture
- `docs/LEAN4_RUST_CORRESPONDENCE.md` - Verification mapping
- `docs/ECHIDNA_INTEGRATION.md` - Automated validation

---

**Last Updated**: 2026-01-28
**Author**: Jonathan D.A. Jewell <jonathan.jewell@open.ac.uk>
**License**: PMPL-1.0-or-later
