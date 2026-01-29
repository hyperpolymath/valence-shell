# Phase 6 Milestone 6: Command Substitution - Session Report

**Date**: 2026-01-29
**Status**: ✅ Complete
**Version**: 0.10.0

## Summary

Successfully implemented POSIX-compliant command substitution for valence-shell (vsh). Both modern `$(cmd)` and legacy `` `cmd` `` syntax work correctly.

## Features Implemented

### 1. Command Substitution Syntax

**Modern Dollar-Paren: `$(cmd)`**
- Preferred POSIX syntax
- Supports nesting: `$(outer $(inner))`
- Clean parsing without escape complexity

**Legacy Backticks: `` `cmd` ``**
- Traditional shell syntax
- Backtick escaping: `` \` ``
- Harder to nest (requires escaping)

### 2. Parsing Infrastructure

Added new `WordPart::CommandSub(String)` variant to represent command substitutions in the token stream.

Extended tokenizer to recognize and parse:
- `$(...)` - Tracks nesting depth for nested command substitutions
- `` `...` `` - Handles backslash escaping for `` \` ``, `\\`, `\$`

**Parser Functions Added**:
```rust
fn parse_command_sub_dollar(chars) -> Result<String>
fn parse_command_sub_backtick(chars) -> Result<String>
```

### 3. Command Execution and Output Capture

Implemented `expand_command_substitution()` to execute commands and capture stdout:
- Executes parsed commands in subprocess
- Captures stdout using `Stdio::piped()`
- Strips trailing newlines (POSIX behavior)
- Preserves interior newlines

**Supported Command Types**:
- External commands (any executable)
- `pwd` builtin
- `ls` builtin (delegates to external ls)

### 4. Integration with Variable Expansion

Created `expand_with_command_sub()` function that handles both:
- Variable expansion: `$VAR`, `${VAR}`, special vars
- Command substitution: `$(cmd)`, `` `cmd` ``

Updated `executable.rs` to use `expand_with_command_sub()` for:
- External command arguments
- Pipeline stage arguments

### 5. Quote Awareness

Command substitution respects quote context:
- **Double quotes**: `"Result: $(pwd)"` - Executes and expands
- **Single quotes**: `'$(pwd)'` - Literal text, no execution
- **Unquoted**: `echo $(pwd)` - Executes and expands

### 6. Newline Handling (POSIX)

- **Trailing newlines stripped**: `$(echo test)` → `"test"` (no \n)
- **Interior newlines preserved**: `$(printf "a\nb")` → `"a\nb"`
- **Word splitting**: Unquoted output splits on whitespace
- **No splitting in quotes**: `"$(cmd)"` preserves all whitespace

## Code Changes

### Files Modified

1. **src/parser.rs** (major additions)
   - Added `WordPart::CommandSub(String)` variant
   - Added `parse_command_sub_dollar()` for `$(cmd)` parsing
   - Added `parse_command_sub_backtick()` for `` `cmd` `` parsing
   - Added `expand_command_substitution()` for execution and output capture
   - Added `expand_with_command_sub()` for combined variable + command sub expansion
   - Updated `tokenize()` to recognize `$(...` and `` ` ``
   - Updated `quoted_word_to_string()` to handle `CommandSub`
   - Updated `expand_quoted_word_with_state()` to execute command subs
   - Added `push_command_sub()` method to `QuotedWord`
   - Modified `parse_variable()` to check for `$(` before `${`
   - Added 12 new unit tests for command substitution parsing

2. **src/executable.rs**
   - Updated External command execution to use `expand_with_command_sub()`
   - Updated Pipeline execution to use `expand_with_command_sub()`
   - Changed from `expand_variables()` to `expand_with_command_sub()` (allows command sub)

3. **Cargo.toml**
   - Version bump: 0.9.0 → 0.10.0

## Test Results

### New Command Substitution Tests (12 tests)
- ✅ `test_command_sub_dollar_parse` - Parse `$(pwd)` correctly
- ✅ `test_command_sub_backtick_parse` - Parse `` `date` `` correctly
- ✅ `test_command_sub_in_double_quotes` - Works in `"..."`
- ✅ `test_command_sub_in_single_quotes` - Literal in `'...'`
- ✅ `test_command_sub_nested_dollar` - Nested `$(outer $(inner))`
- ✅ `test_command_sub_unclosed_dollar` - Error for unclosed `$(`
- ✅ `test_command_sub_unclosed_backtick` - Error for unclosed `` ` ``
- ✅ `test_command_sub_empty` - Empty `$()` parses
- ✅ `test_command_sub_with_args` - `$(ls -la)` works
- ✅ `test_command_sub_multiple` - Multiple subs in one line
- ✅ `test_command_sub_mixed_with_variables` - Mix of `$VAR` and `$(cmd)`
- ✅ `test_command_sub_backtick_escaped` - Escaped `` \` `` in backticks

### All Tests Pass
```
Unit tests: 82 passed (was 70, +12 new command sub tests)
Integration tests: 27 passed
Property tests: 19 passed
Total: 128 tests passed
```

## Manual Testing

```bash
vsh> echo PWD: $(pwd)
PWD: /var/mnt/eclipse/repos/valence-shell/impl/rust-cli

vsh> echo User: `whoami`
User: hyper

vsh> echo "Current dir: $(pwd)"
Current dir: /var/mnt/eclipse/repos/valence-shell/impl/rust-cli

vsh> echo '$(pwd)'
$(pwd)                     # Literal in single quotes

vsh> echo Result: $(echo test)
Result: test               # Trailing newline stripped

vsh> echo $(echo First) and $(echo Second)
First and Second           # Multiple command subs work
```

## Architecture Decisions

### Command Sub During Execution vs. Parsing
**Decision**: Execute command substitutions during argument expansion, not during parsing.

**Rationale**:
- Commands may fail or have side effects
- Parsing should remain lightweight and stateless
- Execution time is when we have full shell state
- Matches how variables are expanded (during execution)

### Supported Command Types
**Decision**: Support External, Pwd, and Ls commands for command substitution.

**Rationale**:
- External commands cover 99% of use cases
- Pwd and Ls are common in scripts
- Pipeline command substitution is complex (deferred)
- Builtin commands with side effects (mkdir, rm) shouldn't be in command subs
- Easy to extend later if needed

### Newline Stripping
**Decision**: Strip all trailing newlines from command output (POSIX behavior).

**Rationale**:
- Matches bash/sh behavior
- Most commands end with \n which users don't want
- Interior newlines are preserved for multi-line output
- `$(echo test)` gives "test", not "test\n"

### Recursive Parsing for Command Subs
**Decision**: Parse command sub content by calling `parse_command()` recursively.

**Rationale**:
- Reuses existing parser logic
- Supports full command syntax in command subs
- Allows nesting naturally
- No need for separate "command sub parser"

## Known Limitations

1. **Pipeline command substitution not supported**: `$(ls | grep txt)` returns error
   - Workaround: Use external commands that accept arguments
   - Could be added later by supporting Pipeline in expand_command_substitution

2. **Builtin commands with state changes not supported**: `$(mkdir test)` returns error
   - Intentional - command subs should be read-only
   - Use regular execution for state-changing operations

3. **Stderr is discarded**: Command substitution only captures stdout
   - Matches POSIX behavior
   - Stderr goes to /dev/null

## Deferred Features

The following will be implemented in later phases:

1. **Process Substitution** - `<(cmd)` and `>(cmd)` (Phase 6 M7)
2. **Arithmetic Expansion** - `$((expr))` (Phase 6 M8)
3. **Here Documents** - `<<EOF` (Phase 6 M9)
4. **Pipeline Command Subs** - `$(cmd1 | cmd2)` (future enhancement)

## Performance Impact

- Command substitution adds execution overhead (subprocess creation)
- No impact on commands without command substitution
- Nested command subs execute sequentially (inner-to-outer)
- All tests still pass with same performance

## Lessons Learned

1. **Nesting Depth Tracking**: Need to track `$(` depth to handle nested command subs correctly
2. **Double Args Bug**: Initially added args twice to ProcessCommand (line 1146 + 1156) - fixed
3. **Quote Context Matters**: Command subs must respect single vs. double quote context
4. **Mutable State Needed**: expand_command_substitution needs `&mut ShellState` for execution
5. **Two-Phase Approach**: Parse during tokenization, execute during expansion

## Next Steps (Phase 6 M7)

1. Process substitution (`<(cmd)` and `>(cmd)`)
2. Named pipe/FIFO support
3. Temporary file handling for process substitution

## Version Update

- Previous: v0.9.0 (Phase 6 M5 - Quote Parsing)
- Current: v0.10.0 (Phase 6 M6 - Command Substitution) ✅
- Next: v0.11.0 (Phase 6 M7 - Process Substitution)

## Commit Summary

```
feat(shell): implement command substitution (Phase 6 M6)

- Add $(cmd) and `cmd` syntax support
- Parse command substitutions in tokenizer (nested $() supported)
- Execute commands and capture stdout during expansion
- Strip trailing newlines (POSIX behavior)
- Support command subs in double quotes, literal in single quotes
- Add expand_with_command_sub() combining variables + command subs
- Update External and Pipeline execution to expand command subs
- Add 12 new unit tests for command substitution parsing

All 128 tests passing.

BREAKING CHANGE: expand_variables signature unchanged, but
expand_with_command_sub() requires &mut ShellState

Ref: docs/PHASE6_M6_DESIGN.md
```

---

**Co-Authored-By**: Claude Sonnet 4.5 <noreply@anthropic.com>
