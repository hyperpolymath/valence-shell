# Phase 6 Milestone 5: Quote Parsing & Positional Parameters

**Status**: In Progress
**Version**: 0.9.0
**Date**: 2026-01-29
**Prerequisites**: Phase 6 M4 (Variables) ✅ Complete

## Overview

Implement POSIX-compliant quote parsing for proper string handling and argument separation.

**Goals**:
- Single quotes (`'...'`) - literal strings, no expansion
- Double quotes (`"..."`) - expansion allowed, preserves spaces
- Backslash escaping (`\`)
- Quote-aware variable expansion
- Positional parameters (`$1`, `$2`, `$@`, `$*`)
- Proper argument splitting

**Timeline**: 2-3 weeks
**Complexity**: High (quote nesting, escaping rules, edge cases)

## POSIX Quote Semantics

### Single Quotes

```bash
vsh> echo 'Hello $NAME'
Hello $NAME               # No expansion

vsh> echo 'Multiple   spaces   preserved'
Multiple   spaces   preserved
```

**Rules**:
- Everything between `'` and `'` is literal
- Cannot escape `'` inside single quotes
- No variable expansion
- Preserves all whitespace

### Double Quotes

```bash
vsh> NAME=World
vsh> echo "Hello $NAME"
Hello World               # Variable expansion

vsh> echo "Path: $HOME/bin"
Path: /home/user/bin      # Expansion works

vsh> echo "Multiple   spaces   preserved"
Multiple   spaces   preserved
```

**Rules**:
- Variables expand (`$VAR`, `${VAR}`)
- Special variables expand (`$?`, `$$`)
- Command substitution expands (future: `$(cmd)`)
- Preserves whitespace
- Can escape with backslash: `\"`, `\$`, `\\`

### Backslash Escaping

```bash
vsh> echo Hello\ World
Hello World               # Space escaped

vsh> echo \$HOME
$HOME                     # Dollar literal

vsh> echo \\
\                         # Backslash literal
```

**Rules**:
- `\<newline>` - line continuation
- `\$` - literal dollar
- `\\` - literal backslash
- `\ ` - literal space (prevents word splitting)
- Inside double quotes: only `\"`, `\$`, `\\`, `\n` escape

### Word Splitting

```bash
vsh> VAR="one two three"
vsh> echo $VAR           # Unquoted: splits
one two three            # (3 arguments)

vsh> echo "$VAR"         # Quoted: preserves
one two three            # (1 argument)
```

## Architecture

### Current Tokenizer (v0.8.0)

```
Input: echo $NAME > file.txt
      ↓
Tokenizer (char-by-char)
      ↓
[Word("echo"), Word("$NAME"), OutputRedirect, Word("file.txt")]
      ↓
Variable Expansion (during execution)
      ↓
[Word("echo"), Word("Alice"), OutputRedirect, Word("file.txt")]
```

### With Quotes (v0.9.0)

```
Input: echo "Hello $NAME" 'no expansion' escaped\ space
      ↓
Tokenizer with Quote State Machine
      ↓
[
  Word("echo"),
  DoubleQuotedWord("Hello $NAME"),
  SingleQuotedWord("no expansion"),
  Word("escaped space")
]
      ↓
Quote Removal + Variable Expansion
      ↓
[
  Word("echo"),
  Word("Hello Alice"),    # Expanded inside ""
  Word("no expansion"),   # Literal from ''
  Word("escaped space")   # Backslash removed
]
```

## Implementation Plan

### Step 1: Quote-Aware Tokenizer (4-6 hours)

Extend `tokenize()` to handle quote states:

```rust
enum QuoteState {
    None,
    SingleQuote,    // Inside '...'
    DoubleQuote,    // Inside "..."
    Backslash,      // After \ (escape next char)
}

enum TokenPart {
    Literal(String),         // Plain text
    Variable(String),        // $VAR to expand
    BracedVariable(String),  // ${VAR} to expand
}

struct QuotedWord {
    parts: Vec<TokenPart>,
    quote_type: QuoteType,   // None, Single, Double
}
```

**Key changes**:
- Track quote state during tokenization
- Build words from multiple `TokenPart`s
- Handle backslash escaping in all contexts
- Preserve quote information for expansion phase

### Step 2: Quote Removal & Expansion (2-3 hours)

Process `QuotedWord` into final string:

```rust
fn process_quoted_word(word: &QuotedWord, state: &ShellState) -> String {
    let mut result = String::new();

    for part in &word.parts {
        match part {
            TokenPart::Literal(s) => result.push_str(s),
            TokenPart::Variable(name) => {
                // Only expand if not in single quotes
                if word.quote_type != QuoteType::Single {
                    result.push_str(&state.expand_variable(name));
                } else {
                    result.push('$');
                    result.push_str(name);
                }
            }
            TokenPart::BracedVariable(name) => {
                // Same expansion rules
                if word.quote_type != QuoteType::Single {
                    result.push_str(&state.expand_variable(name));
                } else {
                    result.push_str("${");
                    result.push_str(name);
                    result.push('}');
                }
            }
        }
    }

    result
}
```

### Step 3: Positional Parameters (2-3 hours)

Add positional parameter support:

```rust
pub struct ShellState {
    // ... existing fields
    positional_params: Vec<String>,  // $1, $2, $3, ...
}

impl ShellState {
    pub fn set_positional_params(&mut self, params: Vec<String>) {
        self.positional_params = params;
    }

    pub fn get_positional_param(&self, index: usize) -> Option<&str> {
        if index == 0 {
            Some("vsh")  // $0 is shell name
        } else {
            self.positional_params.get(index - 1).map(|s| s.as_str())
        }
    }
}
```

**Special variables to add**:
- `$0` - Shell name ("vsh")
- `$1`, `$2`, ..., `$9` - Positional parameters
- `$#` - Number of positional parameters
- `$@` - All parameters as separate words
- `$*` - All parameters as single word

### Step 4: Tests (3-4 hours)

Comprehensive test suite:

```rust
#[test]
fn test_single_quotes_no_expansion() {
    let mut state = ShellState::new("/tmp/test").unwrap();
    state.set_variable("NAME", "Alice");

    let result = parse_and_expand("echo '$NAME'", &state);
    assert_eq!(result.args, vec!["echo", "$NAME"]);
}

#[test]
fn test_double_quotes_with_expansion() {
    let mut state = ShellState::new("/tmp/test").unwrap();
    state.set_variable("NAME", "Alice");

    let result = parse_and_expand("echo \"Hello $NAME\"", &state);
    assert_eq!(result.args, vec!["echo", "Hello Alice"]);
}

#[test]
fn test_quote_preserves_spaces() {
    let result = parse_and_expand("echo \"one   two   three\"");
    assert_eq!(result.args, vec!["echo", "one   two   three"]);
}

#[test]
fn test_backslash_escaping() {
    let result = parse_and_expand("echo \\$HOME");
    assert_eq!(result.args, vec!["echo", "$HOME"]);
}

#[test]
fn test_positional_parameters() {
    let mut state = ShellState::new("/tmp/test").unwrap();
    state.set_positional_params(vec!["arg1".into(), "arg2".into()]);

    let result = parse_and_expand("echo $1 $2", &state);
    assert_eq!(result.args, vec!["echo", "arg1", "arg2"]);
}
```

### Step 5: Integration & Polish (2-3 hours)

- Update variable expansion to respect quotes
- Update argument parsing in all commands
- Handle edge cases (nested quotes, empty strings, etc.)
- Update documentation
- Add examples

## Test Cases

### Quote Parsing

| Input | Expected Args | Notes |
|-------|---------------|-------|
| `echo hello` | `["echo", "hello"]` | No quotes |
| `echo 'hello'` | `["echo", "hello"]` | Single quotes |
| `echo "hello"` | `["echo", "hello"]` | Double quotes |
| `echo 'don'\''t'` | `["echo", "don't"]` | Escaping in single quotes (workaround) |
| `echo "say \"hi\""` | `["echo", "say \"hi\""]` | Escaped double quotes |
| `echo one\ two` | `["echo", "one two"]` | Backslash space |
| `echo ''` | `["echo", ""]` | Empty string |

### Variable Expansion in Quotes

| Input | NAME=Alice | Expected Args |
|-------|------------|---------------|
| `echo $NAME` | ✓ | `["echo", "Alice"]` |
| `echo '$NAME'` | ✓ | `["echo", "$NAME"]` |
| `echo "$NAME"` | ✓ | `["echo", "Alice"]` |
| `echo "${NAME}!"` | ✓ | `["echo", "Alice!"]` |
| `echo '$HOME'` | - | `["echo", "$HOME"]` |
| `echo "$HOME"` | - | `["echo", "/home/user"]` |

### Positional Parameters

| Input | $1=foo $2=bar | Expected Args |
|-------|---------------|---------------|
| `echo $1` | ✓ | `["echo", "foo"]` |
| `echo $@` | ✓ | `["echo", "foo", "bar"]` |
| `echo "$@"` | ✓ | `["echo", "foo", "bar"]` |
| `echo $*` | ✓ | `["echo", "foo bar"]` |
| `echo "$*"` | ✓ | `["echo", "foo bar"]` |
| `echo $#` | ✓ | `["echo", "2"]` |

## Edge Cases to Handle

1. **Unclosed quotes**: `echo "hello` → Error
2. **Nested quotes**: `echo "it's fine"` → OK (single quote inside double)
3. **Empty arguments**: `echo "" ''` → `["echo", "", ""]`
4. **Backslash at EOL**: `echo hello\<newline>world` → Line continuation
5. **Mixed quoting**: `echo "Hello "'$NAME' "$USER"` → Complex parsing
6. **Unicode**: `echo "日本語"` → UTF-8 safe
7. **Special chars in quotes**: `echo "!@#$%"` → All literal

## POSIX Compliance Checklist

- [ ] Single quotes preserve all characters literally
- [ ] Double quotes allow `$`, `` ` ``, `\` expansion
- [ ] Backslash escapes work outside quotes
- [ ] Backslash in double quotes: only `\"`, `\$`, `\\`, `\n`
- [ ] Unclosed quotes are an error
- [ ] Empty strings are valid arguments
- [ ] Positional parameters `$1` through `$9`
- [ ] Special `$@`, `$*`, `$#` work correctly
- [ ] `$@` vs `$*` behave differently in quotes
- [ ] Whitespace preserved in quotes
- [ ] Word splitting disabled inside quotes

## Deferred Features

The following will be implemented in later phases:

1. **Command Substitution** - `` `cmd` `` and `$(cmd)` (Phase 6 M6)
2. **Arithmetic Expansion** - `$((expr))` (Phase 6 M7)
3. **Parameter Expansion** - `${VAR:-default}`, `${VAR#pattern}` (Phase 6 M8)
4. **Glob Expansion** - `*.txt`, `[a-z]` (Phase 6 M9)
5. **Here Documents** - `<<EOF` (Phase 6 M10)

## Success Criteria

- ✅ All POSIX quote behaviors work correctly
- ✅ Variable expansion respects quote context
- ✅ Positional parameters accessible
- ✅ Comprehensive test suite (20+ tests)
- ✅ No regressions in existing functionality
- ✅ Documentation updated
- ✅ Manual testing passes

## Version Update

- Previous: v0.8.0 (Phase 6 M4 - Variables)
- Target: v0.9.0 (Phase 6 M5 - Quotes & Positional Params)
- Next: v0.10.0 (Phase 6 M6 - Command Substitution)

---

**Co-Authored-By**: Claude Sonnet 4.5 <noreply@anthropic.com>
