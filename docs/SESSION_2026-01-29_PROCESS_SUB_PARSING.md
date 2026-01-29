# Phase 6 Milestone 7: Process Substitution Parsing - Session Report

**Date**: 2026-01-29
**Status**: ✅ Parsing Infrastructure Complete (Execution Deferred)
**Version**: 0.10.0 (no version bump - parsing only)

## Summary

Successfully implemented parsing infrastructure for process substitution (`<(cmd)` and `>(cmd)`) in valence-shell (vsh). The syntax is recognized, parsed, and validated, but execution is deferred until FIFO (named pipe) support is added.

## Features Implemented

### 1. Process Substitution Syntax Parsing

**Input Process Substitution: `<(cmd)`**
- Creates placeholder for command output as readable file
- Syntax fully parsed and validated
- Example: `diff <(ls dir1) <(ls dir2)`

**Output Process Substitution: `>(cmd)`**
- Creates placeholder for command input as writable file
- Syntax fully parsed and validated
- Example: `tee >(wc -l) >(grep pattern)`

### 2. Parsing Infrastructure

Added new types to represent process substitution:

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

**Parser Functions Added**:
```rust
fn parse_process_sub_input(chars) -> Result<String>   // Parse <(...)
fn parse_process_sub_output(chars) -> Result<String>  // Parse >(...)
```

### 3. Tokenizer Updates

Extended tokenizer to recognize `<(` and `>(` syntax:

- `<(` triggers input process substitution parsing
- `>(` triggers output process substitution parsing
- `<` alone still triggers input redirection (backward compatible)
- `>` alone still triggers output redirection (backward compatible)
- Tracks parenthesis depth for nested `(` inside process substitution

### 4. Expansion Placeholder

Updated `expand_with_command_sub()` to detect process substitution:

```rust
// In expand_with_command_sub():
if ch == '<' && chars.peek() == Some(&'(') {
    // Parse but return error - execution deferred
    return Err(anyhow!("Process substitution not yet implemented..."));
}
```

Updated `expand_quoted_word_with_state()` to handle `ProcessSub` variant:
- In double quotes: Returns helpful error message
- In single quotes: Treated as literal text `<(cmd)`

### 5. Quote Awareness

Process substitution respects quote context:
- **Double quotes**: `"<(ls)"` - Parses but errors on execution
- **Single quotes**: `'<(ls)'` - Literal text, no parsing
- **Unquoted**: `<(ls)` - Parses and will execute (when implemented)

### 6. Error Messages

Clear error messages guide users:
```
Process substitution not yet implemented: execution requires FIFO support (<(ls))
```

## Code Changes

### Files Modified

1. **src/parser.rs** (major additions - parsing only)
   - Added `ProcessSubType` enum (Input/Output)
   - Added `WordPart::ProcessSub(ProcessSubType, String)` variant
   - Added `parse_process_sub_input()` for `<(cmd)` parsing
   - Added `parse_process_sub_output()` for `>(cmd)` parsing
   - Added `push_process_sub()` method to `QuotedWord`
   - Updated `tokenize()` to recognize `<(...)` and `>(...)` syntax
   - Updated `quoted_word_to_string()` to handle `ProcessSub` variant
   - Updated `expand_quoted_word_with_state()` to handle `ProcessSub` (returns error)
   - Updated `expand_with_command_sub()` to detect and reject `<(` and `>(`
   - Added 10 new unit tests for process substitution parsing

2. **Cargo.toml**
   - No version bump (parsing infrastructure only, not a feature)

## Test Results

### New Process Substitution Tests (10 tests)
- ✅ `test_process_sub_input_parse` - Parse `<(ls dir1)` correctly
- ✅ `test_process_sub_output_parse` - Parse `>(wc -l)` correctly
- ✅ `test_process_sub_in_double_quotes` - Parses in `"..."`
- ✅ `test_process_sub_in_single_quotes` - Literal in `'...'`
- ✅ `test_process_sub_unclosed_input` - Error for unclosed `<(`
- ✅ `test_process_sub_unclosed_output` - Error for unclosed `>(`
- ✅ `test_process_sub_empty` - Empty `<()` parses
- ✅ `test_process_sub_with_redirects` - `<(ls > file)` works
- ✅ `test_process_sub_nested_parens` - `<(echo (test))` tracks depth
- ✅ `test_process_sub_vs_redirect` - `<` vs `<(` distinguished correctly

### All Tests Pass
```
Unit tests: 92 passed (was 82, +10 new process sub tests)
Integration tests: 27 passed
Property tests: 19 passed
Total: 138 tests passed
```

## Manual Testing

```bash
vsh> echo <(ls)
Error: Process substitution not yet implemented: execution requires FIFO support (<(ls))

vsh> tee >(cat)
Error: Process substitution not yet implemented: execution requires FIFO support (>(cat))

vsh> echo '<(ls)'
<(ls)                     # Literal in single quotes

vsh> diff <(ls dir1) <(ls dir2)
Error: Process substitution not yet implemented: execution requires FIFO support (<(ls dir1))
```

## Architecture Decisions

### Parsing vs. Execution Split
**Decision**: Implement parsing infrastructure first, defer execution until later.

**Rationale**:
- Parsing is complex but well-defined (syntax recognition, depth tracking)
- Execution requires FIFO support (platform-specific, Unix-only)
- Execution requires background process management
- Execution requires cleanup logic (remove FIFOs, wait for processes)
- Splitting allows incremental progress and testing
- Users get clear error messages instead of "syntax error"

### Error Message Strategy
**Decision**: Return helpful error explaining what's missing, not just "not implemented".

**Rationale**:
- Users understand process substitution is recognized but not yet functional
- Error message explains the blocker (FIFO support required)
- Shows the exact syntax that was attempted
- Guides future implementation direction

### Quote Context Handling
**Decision**: Process substitution in single quotes is literal (like variables).

**Rationale**:
- Matches bash/POSIX behavior for consistency
- Single quotes prevent all expansions (variables, command subs, process subs)
- Double quotes allow parsing (though execution still errors for now)

## Implementation Details

### Depth Tracking for Nested Parentheses

```rust
fn parse_process_sub_input(chars: &mut Peekable<Chars>) -> Result<String> {
    chars.next(); // consume '('
    let mut cmd = String::new();
    let mut depth = 1;  // Track nesting

    while let Some(ch) = chars.next() {
        match ch {
            '(' => {
                depth += 1;
                cmd.push(ch);
            }
            ')' => {
                depth -= 1;
                if depth == 0 {
                    return Ok(cmd);  // Found matching ')'
                }
                cmd.push(ch);
            }
            _ => cmd.push(ch),
        }
    }

    Err(anyhow!("Unclosed process substitution: <("))
}
```

### Tokenizer Integration

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
```

## Deferred Features (Future Implementation)

1. **FIFO Creation**: Create named pipes using `mkfifo()` syscall
2. **Background Processes**: Start commands in background writing to/reading from FIFOs
3. **FIFO Cleanup**: Remove FIFOs after main command completes
4. **Process Waiting**: Wait for background processes to finish
5. **Error Handling**: Handle deadlocks, broken pipes, process failures
6. **Platform Support**: Windows named pipes (different API from Unix FIFOs)

## Known Limitations

1. **Execution not implemented**: All process substitutions return error
2. **Platform-specific**: Will be Unix/Linux/macOS only (no Windows FIFOs)
3. **No nesting**: `<(cmd <(inner))` parses but execution complexity deferred

## Next Steps (Phase 6 M7 - Execution)

When ready to implement execution:

1. Add FIFO creation with `libc::mkfifo()`
2. Add background process spawning with proper file descriptor setup
3. Add process management (track PIDs, wait for completion)
4. Add cleanup logic (remove FIFOs, reap child processes)
5. Add to `ShellState`: FIFO counter for unique names
6. Update `expand_process_substitution()` to create FIFOs and start processes
7. Extensive testing for edge cases (deadlocks, errors, cleanup)

Reference: `docs/PHASE6_M7_DESIGN.md` for full execution design.

## Version Update

- Previous: v0.10.0 (Phase 6 M6 - Command Substitution) ✅
- Current: v0.10.0 (Phase 6 M7 - Process Substitution **Parsing**) ✅
- Next: v0.11.0 (Phase 6 M7 - Process Substitution **Execution**)

## Commit Summary

```
feat(shell): add process substitution parsing infrastructure (Phase 6 M7 partial)

- Add ProcessSubType enum (Input/Output)
- Add WordPart::ProcessSub variant
- Parse <(cmd) and >(cmd) syntax in tokenizer
- Track parenthesis depth for nested parens
- Distinguish <( from < (process sub vs redirect)
- Handle process sub in quotes (literal in '', error in "")
- Return helpful error for execution attempts (FIFO support needed)
- Add 10 new unit tests for process sub parsing

All 138 tests passing (92 unit + 27 integration + 19 property).

Execution deferred to future milestone (requires FIFO support).

Ref: docs/PHASE6_M7_DESIGN.md
```

---

**Co-Authored-By**: Claude Sonnet 4.5 <noreply@anthropic.com>
