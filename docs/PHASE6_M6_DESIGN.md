# Phase 6 Milestone 6: Command Substitution

**Status**: In Progress
**Version**: 0.10.0
**Date**: 2026-01-29
**Prerequisites**: Phase 6 M5 (Quote Parsing) ✅ Complete

## Overview

Implement POSIX-compliant command substitution for capturing command output and using it as arguments.

**Goals**:
- Backtick syntax: `` `cmd` ``
- Modern syntax: `$(cmd)`
- Nested command substitution: `$(echo $(date))`
- Command substitution in quotes: `"Today is $(date)"`
- Strip trailing newlines (POSIX behavior)

**Timeline**: 2-3 days
**Complexity**: Medium-High (execution context, output capture, parsing)

## POSIX Command Substitution Semantics

### Backtick Syntax (Legacy)

```bash
vsh> echo Current directory: `pwd`
Current directory: /home/user

vsh> FILES=`ls *.txt`
vsh> echo $FILES
file1.txt file2.txt file3.txt
```

**Rules**:
- `` `cmd` `` - Execute cmd and replace with its stdout
- Trailing newlines are stripped
- Interior newlines preserved
- Backslash escaping: `` \` ``, `\\`, `\$`
- Cannot nest easily: `` `echo \`date\`` `` (needs escaping)

### Modern $() Syntax (Preferred)

```bash
vsh> echo Today is $(date +%Y-%m-%d)
Today is 2026-01-29

vsh> echo Nested: $(echo outer $(echo inner))
Nested: outer inner

vsh> COUNT=$(ls | wc -l)
vsh> echo Found $COUNT files
Found 42 files
```

**Rules**:
- `$(cmd)` - Execute cmd and replace with its stdout
- Trailing newlines are stripped
- Interior newlines preserved
- Easy nesting: `$(outer $(inner))`
- No backslash escaping needed for nesting

### In Quotes

```bash
vsh> echo "Today: $(date)"
Today: Wed Jan 29 12:34:56 UTC 2026

vsh> MSG="Files: `ls *.txt`"
vsh> echo $MSG
Files: file1.txt file2.txt
```

**Rules**:
- Command substitution works inside double quotes
- Does NOT work inside single quotes (literal)
- Output preserves spaces when quoted

### Newline Handling

```bash
vsh> echo `printf "a\nb\nc\n"`
a b c                        # Newlines become spaces (word splitting)

vsh> echo "`printf "a\nb\nc\n"`"
a
b
c                            # Newlines preserved in quotes

vsh> VAR=`echo -n test`      # Trailing newline stripped
vsh> echo "$VAR"
test
```

## Architecture

### Current Tokenizer Flow

```
Input: echo $(date)
      ↓
Tokenizer (quote-aware)
      ↓
[Word("echo"), Word("$(date)")]
      ↓
Variable Expansion
      ↓
[Word("echo"), Word("$(date)")]  # Not expanded (not a variable)
```

### With Command Substitution

```
Input: echo $(date)
      ↓
Tokenizer (quote + command sub aware)
      ↓
[Word("echo"), Word with CommandSub("date")]
      ↓
Command Substitution Expansion
      ↓
Execute "date" → capture stdout "Wed Jan 29..."
      ↓
[Word("echo"), Word("Wed Jan 29...")]
      ↓
Variable Expansion (if any $VAR)
      ↓
Execute final command
```

## Implementation Plan

### Step 1: Extend WordPart for Command Substitution (2-3 hours)

Add new `WordPart` variant for command substitution:

```rust
#[derive(Debug, Clone, PartialEq)]
enum WordPart {
    Literal(String),
    Variable(String),          // $VAR
    BracedVariable(String),    // ${VAR}
    CommandSub(String),        // $(cmd) or `cmd`
}
```

### Step 2: Parse Command Substitution in Tokenizer (3-4 hours)

Extend tokenizer to recognize `$(...)` and `` `...` ``:

```rust
fn tokenize(input: &str) -> Result<Vec<Token>> {
    // ... existing code ...

    match ch {
        '$' if peek == Some('(') => {
            // Parse $(...)
            let cmd = parse_command_sub_dollar(&mut chars)?;
            current_word.parts.push(WordPart::CommandSub(cmd));
        }
        '`' => {
            // Parse `...`
            let cmd = parse_command_sub_backtick(&mut chars)?;
            current_word.parts.push(WordPart::CommandSub(cmd));
        }
        // ... existing cases ...
    }
}

fn parse_command_sub_dollar(chars: &mut Peekable<Chars>) -> Result<String> {
    // Skip opening $(
    chars.next(); // consume '('

    let mut cmd = String::new();
    let mut depth = 1;  // Track nesting depth

    while let Some(ch) = chars.next() {
        match ch {
            '(' if cmd.ends_with('$') => {
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

    Err(anyhow!("Unclosed command substitution: $("))
}

fn parse_command_sub_backtick(chars: &mut Peekable<Chars>) -> Result<String> {
    let mut cmd = String::new();
    let mut escaped = false;

    while let Some(ch) = chars.next() {
        match (ch, escaped) {
            ('\\', false) => escaped = true,
            ('`', false) => return Ok(cmd),
            ('`', true) => {
                cmd.push('`');
                escaped = false;
            }
            (_, true) => {
                cmd.push('\\');
                cmd.push(ch);
                escaped = false;
            }
            (_, false) => cmd.push(ch),
        }
    }

    Err(anyhow!("Unclosed command substitution: `"))
}
```

### Step 3: Execute Command Substitution (3-4 hours)

Add function to execute command and capture output:

```rust
pub fn expand_command_substitution(cmd: &str, state: &mut ShellState) -> Result<String> {
    // Parse the command
    let parsed_cmd = parse_command(cmd)?;

    // Execute command and capture stdout
    let output = capture_command_output(&parsed_cmd, state)?;

    // Strip trailing newlines (POSIX behavior)
    let trimmed = output.trim_end_matches('\n');

    Ok(trimmed.to_string())
}

fn capture_command_output(cmd: &Command, state: &mut ShellState) -> Result<String> {
    use std::process::{Command as ProcessCommand, Stdio};

    match cmd {
        Command::External { program, args, .. } => {
            // Execute external command and capture output
            let output = ProcessCommand::new(program)
                .args(args)
                .stdout(Stdio::piped())
                .output()?;

            if output.status.success() {
                Ok(String::from_utf8_lossy(&output.stdout).to_string())
            } else {
                Err(anyhow!("Command failed: {}", program))
            }
        }

        // For builtin commands, redirect stdout to string
        Command::Pwd { .. } => {
            Ok(std::env::current_dir()?
                .to_string_lossy()
                .to_string() + "\n")
        }

        Command::Ls { path, .. } => {
            // Similar to external command capture
            let path = path.as_deref().unwrap_or(".");
            let output = ProcessCommand::new("ls")
                .arg(path)
                .stdout(Stdio::piped())
                .output()?;
            Ok(String::from_utf8_lossy(&output.stdout).to_string())
        }

        _ => Err(anyhow!("Command substitution not supported for this command")),
    }
}
```

### Step 4: Integrate with Variable Expansion (2 hours)

Update `expand_variables()` to also expand command substitutions:

```rust
pub fn expand_quoted_word_with_state(word: &QuotedWord, state: &mut ShellState) -> Result<String> {
    let mut result = String::new();

    for part in &word.parts {
        match part {
            WordPart::Literal(s) => {
                result.push_str(s);
            }
            WordPart::Variable(name) | WordPart::BracedVariable(name) => {
                if word.quote_type != QuoteType::Single {
                    result.push_str(&state.expand_variable(name));
                } else {
                    // Keep literal in single quotes
                    result.push('$');
                    result.push_str(name);
                }
            }
            WordPart::CommandSub(cmd) => {
                if word.quote_type != QuoteType::Single {
                    // Execute command and capture output
                    let output = expand_command_substitution(cmd, state)?;
                    result.push_str(&output);
                } else {
                    // Keep literal in single quotes
                    result.push_str("$(");
                    result.push_str(cmd);
                    result.push(')');
                }
            }
        }
    }

    Ok(result)
}
```

### Step 5: Tests (3-4 hours)

Comprehensive test suite:

```rust
#[test]
fn test_command_sub_dollar_simple() {
    let tokens = tokenize("echo $(pwd)").unwrap();
    assert_eq!(tokens.len(), 2);

    if let Token::Word(w) = &tokens[1] {
        assert_eq!(w.parts.len(), 1);
        if let WordPart::CommandSub(cmd) = &w.parts[0] {
            assert_eq!(cmd, "pwd");
        } else {
            panic!("Expected CommandSub");
        }
    }
}

#[test]
fn test_command_sub_backtick_simple() {
    let tokens = tokenize("echo `date`").unwrap();
    assert_eq!(tokens.len(), 2);

    if let Token::Word(w) = &tokens[1] {
        if let WordPart::CommandSub(cmd) = &w.parts[0] {
            assert_eq!(cmd, "date");
        }
    }
}

#[test]
fn test_command_sub_nested() {
    let tokens = tokenize("echo $(echo $(date))").unwrap();
    // Verify nested command substitution parsed correctly
}

#[test]
fn test_command_sub_in_double_quotes() {
    let tokens = tokenize("echo \"Today: $(date)\"").unwrap();
    // Should parse command sub inside quotes
}

#[test]
fn test_command_sub_in_single_quotes() {
    let tokens = tokenize("echo '$(date)'").unwrap();
    // Should be literal, not parsed as command sub
}

#[test]
fn test_command_sub_strip_trailing_newline() {
    let mut state = ShellState::new("/tmp/test").unwrap();
    let output = expand_command_substitution("echo test", &mut state).unwrap();
    assert_eq!(output, "test");  // Newline stripped
}

#[test]
fn test_command_sub_preserve_interior_newlines() {
    let mut state = ShellState::new("/tmp/test").unwrap();
    let output = expand_command_substitution("printf 'a\\nb'", &mut state).unwrap();
    assert_eq!(output, "a\nb");  // Interior newline preserved
}

#[test]
fn test_unclosed_command_sub_dollar() {
    let result = tokenize("echo $(date");
    assert!(result.is_err());
}

#[test]
fn test_unclosed_command_sub_backtick() {
    let result = tokenize("echo `date");
    assert!(result.is_err());
}
```

### Step 6: Integration & Documentation (2 hours)

- Update executable.rs to use new expansion
- Update documentation
- Manual testing
- Performance verification

## Test Cases

### Basic Command Substitution

| Input | Expected Output | Notes |
|-------|----------------|-------|
| `echo $(pwd)` | Current directory | Simple $() |
| `` echo `pwd` `` | Current directory | Backtick syntax |
| `echo $(echo test)` | test | Simple command |
| `VAR=$(date); echo $VAR` | Date output | Assignment |

### Nesting

| Input | Expected Output | Notes |
|-------|----------------|-------|
| `echo $(echo $(echo nested))` | nested | Double nesting |
| `echo $(echo a $(echo b) c)` | a b c | Multiple nested |

### In Quotes

| Input | Expected Output | Notes |
|-------|----------------|-------|
| `echo "Result: $(pwd)"` | Result: /path | In double quotes |
| `echo '$(pwd)'` | $(pwd) | Literal in single quotes |
| `echo "$(echo a b c)"` | a b c | Preserves spaces |

### Newline Handling

| Input | Expected Output | Notes |
|-------|----------------|-------|
| `echo $(printf "a\nb")` | a b | Newlines → spaces |
| `echo "$(printf "a\nb")"` | a<br>b | Preserved in quotes |
| `VAR=$(echo -n test)` | test | Trailing newline stripped |

### Edge Cases

| Input | Expected Behavior | Notes |
|-------|------------------|-------|
| `echo $(` | Error: Unclosed | Parser error |
| `` echo ` `` | Error: Unclosed | Parser error |
| `echo $()` | Empty string | Empty command |
| `echo $(exit 1)` | Error | Failed command |

## Deferred Features

The following will be implemented in later phases:

1. **Process Substitution** - `<(cmd)` and `>(cmd)` (Phase 6 M7)
2. **Arithmetic Expansion** - `$((expr))` (Phase 6 M8)
3. **Here Documents** - `<<EOF` (Phase 6 M9)

## POSIX Compliance Checklist

- [ ] `$(cmd)` syntax works
- [ ] `` `cmd` `` backtick syntax works
- [ ] Nested `$(outer $(inner))` works
- [ ] Command sub in double quotes works
- [ ] Command sub literal in single quotes
- [ ] Trailing newlines stripped
- [ ] Interior newlines preserved
- [ ] Unclosed substitutions are errors
- [ ] Empty `$()` returns empty string
- [ ] Failed commands return error

## Success Criteria

- ✅ Both `$()` and `` `...` `` syntax work
- ✅ Nested command substitution works
- ✅ Works correctly in double quotes
- ✅ Literal in single quotes
- ✅ POSIX newline handling
- ✅ Comprehensive test suite (15+ tests)
- ✅ No regressions in existing functionality
- ✅ Documentation updated

## Version Update

- Previous: v0.9.0 (Phase 6 M5 - Quote Parsing)
- Target: v0.10.0 (Phase 6 M6 - Command Substitution)
- Next: v0.11.0 (Phase 6 M7 - Process Substitution)

---

**Co-Authored-By**: Claude Sonnet 4.5 <noreply@anthropic.com>
