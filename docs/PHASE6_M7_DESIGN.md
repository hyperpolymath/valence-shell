# Phase 6 Milestone 7: Process Substitution

**Status**: In Progress
**Version**: 0.11.0
**Date**: 2026-01-29
**Prerequisites**: Phase 6 M6 (Command Substitution) ✅ Complete

## Overview

Implement bash-style process substitution for treating command output as files.

**Goals**:
- Input process substitution: `<(cmd)` - Treats output as readable file
- Output process substitution: `>(cmd)` - Treats input as writable file
- FIFO (named pipe) management
- Background process handling
- Automatic cleanup

**Timeline**: 2-3 days
**Complexity**: High (FIFOs, background processes, cleanup)

## Process Substitution Semantics

### Input Process Substitution: `<(cmd)`

Creates a named pipe (FIFO) that provides command output as a readable file.

```bash
vsh> diff <(ls dir1) <(ls dir2)
# Creates: /tmp/vsh-fifo-123 and /tmp/vsh-fifo-124
# Runs: ls dir1 > /tmp/vsh-fifo-123 (background)
# Runs: ls dir2 > /tmp/vsh-fifo-124 (background)
# Executes: diff /tmp/vsh-fifo-123 /tmp/vsh-fifo-124
# Cleans up FIFOs after diff completes

vsh> cat <(echo Hello) <(echo World)
Hello
World

vsh> wc -l <(ls)
# Count lines in ls output without creating temp file
```

**Rules**:
- `<(cmd)` is replaced with path to FIFO (e.g., `/tmp/vsh-fifo-PID-N`)
- Command runs in background, writing to FIFO
- FIFO appears as readable file to main command
- FIFOs cleaned up after main command finishes

### Output Process Substitution: `>(cmd)`

Creates a named pipe (FIFO) that feeds input to a command.

```bash
vsh> tee >(wc -l) >(grep pattern) < input.txt
# Creates: /tmp/vsh-fifo-125 and /tmp/vsh-fifo-126
# Runs: wc -l < /tmp/vsh-fifo-125 (background)
# Runs: grep pattern < /tmp/vsh-fifo-126 (background)
# Executes: tee /tmp/vsh-fifo-125 /tmp/vsh-fifo-126 < input.txt

vsh> echo "test" | tee >(cat >&2)
test              # stdout
test              # stderr (from tee'd copy)
```

**Rules**:
- `>(cmd)` is replaced with path to FIFO
- Command runs in background, reading from FIFO
- FIFO appears as writable file to main command
- FIFOs cleaned up after all processes finish

### Multiple Process Substitutions

```bash
vsh> diff <(sort file1) <(sort file2)
# Two input FIFOs

vsh> paste <(cut -f1 file) <(cut -f2 file)
# Process different fields separately

vsh> comm <(sort a) <(sort b)
# Compare sorted files without temp files
```

## Architecture

### Current Flow

```
Input: diff <(ls dir1) <(ls dir2)
      ↓
Tokenizer: [Word("diff"), Word("<(ls dir1)"), Word("<(ls dir2)")]
      ↓
Expansion: [Word("diff"), Word("/tmp/vsh-fifo-1"), Word("/tmp/vsh-fifo-2")]
      ↓
Execute: diff /tmp/vsh-fifo-1 /tmp/vsh-fifo-2
```

### With Process Substitution

```
Input: diff <(ls dir1) <(ls dir2)
      ↓
Tokenizer (recognizes <(...) and >(...))
      ↓
[Word("diff"), ProcessSub(Input, "ls dir1"), ProcessSub(Input, "ls dir2")]
      ↓
Process Sub Expansion:
  1. Create /tmp/vsh-fifo-PID-1
  2. Create /tmp/vsh-fifo-PID-2
  3. Start: ls dir1 > /tmp/vsh-fifo-PID-1 (background)
  4. Start: ls dir2 > /tmp/vsh-fifo-PID-2 (background)
      ↓
[Word("diff"), Word("/tmp/vsh-fifo-PID-1"), Word("/tmp/vsh-fifo-PID-2")]
      ↓
Execute: diff /tmp/vsh-fifo-PID-1 /tmp/vsh-fifo-PID-2
      ↓
Wait for diff to complete
      ↓
Wait for background processes
      ↓
Cleanup FIFOs
```

## Implementation Plan

### Step 1: Add ProcessSub WordPart (1-2 hours)

```rust
#[derive(Debug, Clone, PartialEq)]
enum ProcessSubType {
    Input,   // <(cmd)
    Output,  // >(cmd)
}

#[derive(Debug, Clone, PartialEq)]
enum WordPart {
    Literal(String),
    Variable(String),
    BracedVariable(String),
    CommandSub(String),
    ProcessSub(ProcessSubType, String),  // NEW
}
```

### Step 2: Parse Process Substitution (2-3 hours)

```rust
fn parse_process_sub_input(chars: &mut Peekable<Chars>) -> Result<String> {
    // Parse <(cmd)
    // Similar to parse_command_sub_dollar but for <(
    chars.next(); // consume '('
    let mut cmd = String::new();
    let mut depth = 1;

    while let Some(ch) = chars.next() {
        match ch {
            '(' => {
                depth += 1;
                cmd.push(ch);
            }
            ')' => {
                depth -= 1;
                if depth == 0 {
                    return Ok(cmd);
                }
                cmd.push(ch);
            }
            _ => cmd.push(ch),
        }
    }

    Err(anyhow!("Unclosed process substitution: <("))
}

fn parse_process_sub_output(chars: &mut Peekable<Chars>) -> Result<String> {
    // Parse >(cmd)
    // Identical logic to parse_process_sub_input
    chars.next(); // consume '('
    // ... same as above
}
```

Update tokenizer:
```rust
'<' => {
    if chars.peek() == Some(&'(') {
        // Process substitution: <(cmd)
        push_literal!();
        let cmd = parse_process_sub_input(&mut chars)?;
        current_word.push_process_sub(ProcessSubType::Input, cmd);
    } else {
        // Input redirection: <
        push_word!();
        tokens.push(Token::InputRedirect);
    }
}

'>' => {
    if chars.peek() == Some(&'(') {
        // Process substitution: >(cmd)
        push_literal!();
        let cmd = parse_process_sub_output(&mut chars)?;
        current_word.push_process_sub(ProcessSubType::Output, cmd);
    } else {
        // Output redirection: >, >>, &>, etc.
        push_word!();
        // ... existing redirect logic
    }
}
```

### Step 3: FIFO Management (3-4 hours)

```rust
use std::fs;
use std::os::unix::fs::OpenOptionsExt;

struct ProcessSubstitution {
    fifo_path: PathBuf,
    command: String,
    sub_type: ProcessSubType,
    child_process: Option<std::process::Child>,
}

impl ProcessSubstitution {
    fn create(sub_type: ProcessSubType, cmd: String, state: &mut ShellState) -> Result<Self> {
        // Generate unique FIFO path
        let pid = std::process::id();
        let fifo_id = state.next_fifo_id();
        let fifo_path = PathBuf::from(format!("/tmp/vsh-fifo-{}-{}", pid, fifo_id));

        // Create FIFO
        unsafe {
            use std::ffi::CString;
            let path_cstr = CString::new(fifo_path.to_str().unwrap())?;
            let result = libc::mkfifo(path_cstr.as_ptr(), 0o600);
            if result != 0 {
                return Err(anyhow!("Failed to create FIFO: {}", fifo_path.display()));
            }
        }

        Ok(Self {
            fifo_path,
            command: cmd,
            sub_type,
            child_process: None,
        })
    }

    fn start(&mut self, state: &mut ShellState) -> Result<()> {
        // Parse command
        let parsed_cmd = parse_command(&self.command)?;

        // Start background process
        match self.sub_type {
            ProcessSubType::Input => {
                // Redirect command output to FIFO
                // exec cmd > fifo_path
                let child = start_command_with_redirect(
                    &parsed_cmd,
                    state,
                    RedirectTo::File(self.fifo_path.clone())
                )?;
                self.child_process = Some(child);
            }
            ProcessSubType::Output => {
                // Redirect FIFO to command input
                // exec cmd < fifo_path
                let child = start_command_with_redirect(
                    &parsed_cmd,
                    state,
                    RedirectFrom::File(self.fifo_path.clone())
                )?;
                self.child_process = Some(child);
            }
        }

        Ok(())
    }

    fn cleanup(&mut self) -> Result<()> {
        // Wait for background process
        if let Some(mut child) = self.child_process.take() {
            child.wait()?;
        }

        // Remove FIFO
        if self.fifo_path.exists() {
            fs::remove_file(&self.fifo_path)?;
        }

        Ok(())
    }
}
```

### Step 4: Expand Process Substitution (2-3 hours)

```rust
pub fn expand_process_substitution(
    sub_type: ProcessSubType,
    cmd: &str,
    state: &mut ShellState,
) -> Result<(String, ProcessSubstitution)> {
    // Create FIFO and start background process
    let mut proc_sub = ProcessSubstitution::create(sub_type, cmd.to_string(), state)?;
    proc_sub.start(state)?;

    // Return FIFO path (will be used as argument)
    let fifo_path = proc_sub.fifo_path.to_string_lossy().to_string();

    Ok((fifo_path, proc_sub))
}

pub fn expand_with_process_sub(
    input: &str,
    state: &mut ShellState,
) -> Result<(String, Vec<ProcessSubstitution>)> {
    // Similar to expand_with_command_sub but also handles ProcessSub
    let mut result = String::new();
    let mut proc_subs = Vec::new();
    let mut chars = input.chars().peekable();

    while let Some(ch) = chars.next() {
        if ch == '<' && chars.peek() == Some(&'(') {
            // Input process substitution
            let cmd = parse_process_sub_input(&mut chars)?;
            let (fifo_path, proc_sub) = expand_process_substitution(
                ProcessSubType::Input,
                &cmd,
                state
            )?;
            result.push_str(&fifo_path);
            proc_subs.push(proc_sub);
        } else if ch == '>' && chars.peek() == Some(&'(') {
            // Output process substitution
            let cmd = parse_process_sub_output(&mut chars)?;
            let (fifo_path, proc_sub) = expand_process_substitution(
                ProcessSubType::Output,
                &cmd,
                state
            )?;
            result.push_str(&fifo_path);
            proc_subs.push(proc_sub);
        }
        // ... handle $VAR, $(cmd), etc.
    }

    Ok((result, proc_subs))
}
```

### Step 5: Integrate with Execution (2 hours)

```rust
// In executable.rs
Command::External { program, args, .. } => {
    let mut all_proc_subs = Vec::new();

    // Expand args (may create process substitutions)
    let expanded_args: Result<Vec<String>> = args
        .iter()
        .map(|arg| {
            let (expanded, proc_subs) = expand_with_process_sub(arg, state)?;
            all_proc_subs.extend(proc_subs);
            Ok(expanded)
        })
        .collect();
    let expanded_args = expanded_args?;

    // Execute main command
    let exit_code = execute_external(&expanded_program, &expanded_args)?;

    // Cleanup process substitutions
    for mut proc_sub in all_proc_subs {
        proc_sub.cleanup()?;
    }

    Ok(ExecutionResult::ExternalCommand { exit_code })
}
```

### Step 6: Add to ShellState (1 hour)

```rust
pub struct ShellState {
    // ... existing fields
    next_fifo_id: AtomicUsize,
}

impl ShellState {
    pub fn next_fifo_id(&self) -> usize {
        self.next_fifo_id.fetch_add(1, Ordering::SeqCst)
    }
}
```

### Step 7: Tests (3-4 hours)

```rust
#[test]
fn test_process_sub_input_parse() {
    let tokens = tokenize("diff <(ls dir1) <(ls dir2)").unwrap();
    // Verify ProcessSub tokens created
}

#[test]
fn test_process_sub_output_parse() {
    let tokens = tokenize("tee >(cat)").unwrap();
    // Verify output process sub
}

#[test]
fn test_process_sub_fifo_created() {
    // Test that FIFO is created and cleaned up
}

#[test]
fn test_process_sub_cat() {
    // Simple test: cat <(echo test)
    // Should output "test"
}
```

## Deferred Features

1. **Process substitution in redirects**: `cmd > >(other)` (complex)
2. **Process substitution nesting**: `<(cmd <(inner))` (very complex)
3. **Error handling for FIFO deadlocks** (advanced)

## POSIX Notes

Process substitution is **NOT POSIX** - it's a bash/zsh extension. However:
- Very useful for avoiding temp files
- Common in modern shell scripts
- Worth implementing for usability

## Platform Support

**Linux/macOS**: FIFOs via `mkfifo()` syscall
**Windows**: NOT SUPPORTED (no FIFOs) - would need named pipes, different API

For now: Linux/macOS only. Windows support deferred.

## Success Criteria

- ✅ `<(cmd)` syntax parses correctly
- ✅ `>(cmd)` syntax parses correctly
- ✅ FIFOs created in /tmp with unique names
- ✅ Background processes started correctly
- ✅ Main command receives FIFO paths
- ✅ FIFOs cleaned up after execution
- ✅ Works with simple commands (cat, diff, etc.)
- ✅ Comprehensive test suite (10+ tests)
- ✅ No resource leaks (FIFOs, processes)

## Version Update

- Previous: v0.10.0 (Phase 6 M6 - Command Substitution)
- Target: v0.11.0 (Phase 6 M7 - Process Substitution)
- Next: v0.12.0 (Phase 6 M8 - Arithmetic Expansion)

---

**Co-Authored-By**: Claude Sonnet 4.5 <noreply@anthropic.com>
