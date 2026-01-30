# Phase 6 Milestone 13: Quote Processing

**Status**: Design Phase
**Version**: 0.15.0 (planned)
**Date**: 2026-01-29

## Overview

Implement POSIX-compliant quote processing for the Valence Shell parser. Quote processing is essential for:
- Preserving whitespace in arguments
- Preventing glob expansion when needed
- Literal interpretation of special characters
- Variable expansion control
- Proper command argument parsing

## POSIX Quote Semantics

### Single Quotes (')

**Behavior**:
- Preserve all characters literally (no expansion)
- Cannot contain a single quote (even escaped)
- No variable expansion, command substitution, or glob expansion
- Whitespace preserved as-is

**Examples**:
```bash
echo 'hello world'           # Output: hello world
echo '$HOME'                 # Output: $HOME (literal)
echo '*.txt'                 # Output: *.txt (no glob)
echo 'line1
line2'                       # Preserves newline
```

**Use Cases**:
- Literal strings with special characters
- Preventing all expansions
- Preserving exact whitespace

### Double Quotes (")

**Behavior**:
- Variable expansion occurs ($VAR, ${VAR})
- Command substitution occurs ($(cmd), `cmd`)
- Arithmetic expansion occurs ($((expr)))
- Glob expansion DOES NOT occur
- Backslash escapes work for: \$ \` \" \\ \n
- Whitespace preserved

**Examples**:
```bash
echo "hello world"           # Output: hello world
echo "$HOME"                 # Output: /home/user (expanded)
echo "*.txt"                 # Output: *.txt (no glob)
echo "value: $((2+2))"       # Output: value: 4
echo "quote: \"yes\""        # Output: quote: "yes"
```

**Use Cases**:
- Strings with variable interpolation
- Preserving whitespace while allowing expansion
- Preventing glob expansion only

### Backslash Escaping (\)

**Behavior**:
- Outside quotes: Escapes next character literally
- Inside single quotes: Literal backslash (no escaping)
- Inside double quotes: Escapes only $, `, ", \, newline
- At end of line: Line continuation

**Examples**:
```bash
echo hello\ world            # Output: hello world
echo \$HOME                  # Output: $HOME (literal)
echo "value: \$50"           # Output: value: $50
echo first\
line                         # Continues to next line
```

**Use Cases**:
- Escaping single special characters
- Line continuation
- Literal $ or " in double quotes

## Implementation Design

### Architecture

```
┌─────────────────────────────────────────────────────────┐
│                    Parser Layer                         │
│  ┌────────────┐   ┌──────────────┐   ┌──────────────┐ │
│  │ Tokenizer  │ → │ Quote Parser │ → │  Expander    │ │
│  │  (lexer)   │   │  (this M13)  │   │  (existing)  │ │
│  └────────────┘   └──────────────┘   └──────────────┘ │
└─────────────────────────────────────────────────────────┘
         ↓                   ↓                   ↓
    Raw tokens        Quoted tokens      Expanded args
```

### Data Structures

```rust
/// Quote state for a token
#[derive(Debug, Clone, PartialEq)]
pub enum QuoteState {
    /// No quotes (full expansion)
    Unquoted,

    /// Single-quoted (no expansion)
    SingleQuoted,

    /// Double-quoted (variable/command expansion only)
    DoubleQuoted,

    /// Mixed quoting (different parts have different states)
    Mixed(Vec<QuotedSegment>),
}

/// A segment of a token with quote state
#[derive(Debug, Clone, PartialEq)]
pub struct QuotedSegment {
    pub content: String,
    pub state: QuoteState,
}

/// A token with quote information
#[derive(Debug, Clone, PartialEq)]
pub struct QuotedToken {
    /// Raw content (including quotes)
    pub raw: String,

    /// Parsed segments
    pub segments: Vec<QuotedSegment>,

    /// Whether this token should undergo glob expansion
    pub allow_glob: bool,
}
```

### Quote Parser Module

Create `src/quotes.rs`:

```rust
/// Parse a string into quoted segments
pub fn parse_quotes(input: &str) -> Result<Vec<QuotedSegment>> {
    let mut segments = Vec::new();
    let mut current = String::new();
    let mut state = QuoteState::Unquoted;
    let mut chars = input.chars().peekable();

    while let Some(ch) = chars.next() {
        match (state.clone(), ch) {
            // Unquoted → single quote
            (QuoteState::Unquoted, '\'') => {
                if !current.is_empty() {
                    segments.push(QuotedSegment {
                        content: current.clone(),
                        state: QuoteState::Unquoted,
                    });
                    current.clear();
                }
                state = QuoteState::SingleQuoted;
            }

            // Unquoted → double quote
            (QuoteState::Unquoted, '"') => {
                if !current.is_empty() {
                    segments.push(QuotedSegment {
                        content: current.clone(),
                        state: QuoteState::Unquoted,
                    });
                    current.clear();
                }
                state = QuoteState::DoubleQuoted;
            }

            // Unquoted backslash escape
            (QuoteState::Unquoted, '\\') => {
                if let Some(next) = chars.next() {
                    current.push(next);
                }
            }

            // Single quote → close
            (QuoteState::SingleQuoted, '\'') => {
                segments.push(QuotedSegment {
                    content: current.clone(),
                    state: QuoteState::SingleQuoted,
                });
                current.clear();
                state = QuoteState::Unquoted;
            }

            // Double quote → close
            (QuoteState::DoubleQuoted, '"') => {
                segments.push(QuotedSegment {
                    content: current.clone(),
                    state: QuoteState::DoubleQuoted,
                });
                current.clear();
                state = QuoteState::Unquoted;
            }

            // Double quote backslash (limited escaping)
            (QuoteState::DoubleQuoted, '\\') => {
                if let Some(&next) = chars.peek() {
                    if matches!(next, '$' | '`' | '"' | '\\' | '\n') {
                        chars.next();
                        current.push(next);
                    } else {
                        current.push('\\');
                    }
                }
            }

            // Regular character
            (_, ch) => {
                current.push(ch);
            }
        }
    }

    // Handle unclosed quotes
    if state != QuoteState::Unquoted {
        anyhow::bail!("Unclosed quote");
    }

    if !current.is_empty() {
        segments.push(QuotedSegment {
            content: current,
            state,
        });
    }

    Ok(segments)
}

/// Check if a token should undergo glob expansion
pub fn should_expand_glob(segments: &[QuotedSegment]) -> bool {
    segments.iter().any(|seg| {
        seg.state == QuoteState::Unquoted &&
        crate::glob::contains_glob_pattern(&seg.content)
    })
}

/// Apply expansions to quoted segments
pub fn expand_segments(
    segments: &[QuotedSegment],
    state: &ShellState,
) -> Result<String> {
    let mut result = String::new();

    for segment in segments {
        match segment.state {
            QuoteState::Unquoted | QuoteState::DoubleQuoted => {
                // Variable and command expansion
                let expanded = crate::parser::expand_variables(&segment.content, state);
                result.push_str(&expanded);
            }
            QuoteState::SingleQuoted => {
                // No expansion
                result.push_str(&segment.content);
            }
            QuoteState::Mixed(_) => unreachable!("Mixed handled recursively"),
        }
    }

    Ok(result)
}
```

## Integration Points

### 1. Tokenizer Integration

Modify `src/parser.rs` tokenizer:

```rust
// Before: Simple whitespace splitting
fn tokenize(input: &str) -> Vec<String> {
    input.split_whitespace().map(String::from).collect()
}

// After: Quote-aware tokenization
fn tokenize(input: &str) -> Result<Vec<QuotedToken>> {
    let mut tokens = Vec::new();
    let mut current = String::new();
    let mut in_quotes = false;
    let mut quote_char = None;

    for ch in input.chars() {
        match (in_quotes, ch) {
            (false, ' ' | '\t') if !in_quotes => {
                if !current.is_empty() {
                    tokens.push(parse_quoted_token(&current)?);
                    current.clear();
                }
            }
            (false, '\'' | '"') => {
                current.push(ch);
                in_quotes = true;
                quote_char = Some(ch);
            }
            (true, ch) if Some(ch) == quote_char => {
                current.push(ch);
                in_quotes = false;
                quote_char = None;
            }
            (_, ch) => {
                current.push(ch);
            }
        }
    }

    if !current.is_empty() {
        tokens.push(parse_quoted_token(&current)?);
    }

    if in_quotes {
        anyhow::bail!("Unclosed quote");
    }

    Ok(tokens)
}
```

### 2. Glob Expansion Integration

Modify `src/external.rs` glob expansion:

```rust
// Before: Always expand globs
fn expand_glob_args(args: &[String], state: &ShellState) -> Result<Vec<String>> {
    for arg in args {
        if glob::contains_glob_pattern(arg) {
            // Expand...
        }
    }
}

// After: Respect quote state
fn expand_glob_args(args: &[QuotedToken], state: &ShellState) -> Result<Vec<String>> {
    for token in args {
        if token.allow_glob && should_expand_glob(&token.segments) {
            // Expand...
        } else {
            // Use literal...
        }
    }
}
```

### 3. Variable Expansion Integration

Modify variable expansion to respect quotes:

```rust
fn expand_variables(segments: &[QuotedSegment], state: &ShellState) -> String {
    let mut result = String::new();

    for segment in segments {
        match segment.state {
            QuoteState::SingleQuoted => {
                // No expansion - literal
                result.push_str(&segment.content);
            }
            QuoteState::DoubleQuoted | QuoteState::Unquoted => {
                // Expand variables
                let expanded = do_variable_expansion(&segment.content, state);
                result.push_str(&expanded);
            }
            QuoteState::Mixed(_) => unreachable!(),
        }
    }

    result
}
```

## Edge Cases

### 1. Empty Quotes

```bash
echo ''                      # Empty string argument
echo ""                      # Empty string argument
cmd '' arg2                  # Three arguments: ["cmd", "", "arg2"]
```

**Handling**: Preserve empty quotes as empty string arguments.

### 2. Adjacent Quotes

```bash
echo "hello"'world'          # Output: helloworld
echo "$HOME"/.config         # Output: /home/user/.config
echo 'literal'$VAR           # Output: literal + expanded VAR
```

**Handling**: Concatenate adjacent quoted/unquoted segments.

### 3. Nested Quotes (Invalid)

```bash
echo "outer 'inner' outer"   # Valid: single quotes literal in double
echo 'outer "inner" outer'   # Valid: double quotes literal in single
echo "outer "inner" outer"   # INVALID: cannot nest same quote type
```

**Handling**: Treat as adjacent segments (close first, open second).

### 4. Backslash in Single Quotes

```bash
echo 'back\slash'            # Output: back\slash (literal)
echo 'can'\''t'              # Output: can't (workaround for ')
```

**Handling**: All characters literal in single quotes, including backslash.

### 5. Line Continuation

```bash
echo "multi\
line"                        # Backslash-newline removed
echo 'no\
continuation'                # Backslash literal in single quotes
```

**Handling**: Remove backslash-newline in unquoted/double-quoted context.

## Testing Strategy

### Unit Tests (src/quotes.rs)

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_single_quotes_literal() {
        let segments = parse_quotes("'$HOME'").unwrap();
        assert_eq!(segments.len(), 1);
        assert_eq!(segments[0].content, "$HOME");
        assert_eq!(segments[0].state, QuoteState::SingleQuoted);
    }

    #[test]
    fn test_double_quotes_expansion() {
        let segments = parse_quotes("\"$HOME\"").unwrap();
        assert_eq!(segments.len(), 1);
        assert_eq!(segments[0].content, "$HOME");
        assert_eq!(segments[0].state, QuoteState::DoubleQuoted);
    }

    #[test]
    fn test_adjacent_quotes() {
        let segments = parse_quotes("'hello'\"world\"").unwrap();
        assert_eq!(segments.len(), 2);
        assert_eq!(segments[0].content, "hello");
        assert_eq!(segments[0].state, QuoteState::SingleQuoted);
        assert_eq!(segments[1].content, "world");
        assert_eq!(segments[1].state, QuoteState::DoubleQuoted);
    }

    #[test]
    fn test_backslash_escape_unquoted() {
        let segments = parse_quotes("hello\\ world").unwrap();
        assert_eq!(segments.len(), 1);
        assert_eq!(segments[0].content, "hello world");
    }

    #[test]
    fn test_backslash_in_double_quotes() {
        let segments = parse_quotes("\"\\$HOME\"").unwrap();
        assert_eq!(segments[0].content, "$HOME");
    }

    #[test]
    fn test_unclosed_quote_error() {
        assert!(parse_quotes("'unclosed").is_err());
        assert!(parse_quotes("\"unclosed").is_err());
    }

    #[test]
    fn test_empty_quotes() {
        let segments = parse_quotes("''").unwrap();
        assert_eq!(segments.len(), 1);
        assert_eq!(segments[0].content, "");
    }

    #[test]
    fn test_glob_no_expansion_in_quotes() {
        let segments = parse_quotes("'*.txt'").unwrap();
        assert!(!should_expand_glob(&segments));

        let segments = parse_quotes("\"*.txt\"").unwrap();
        assert!(!should_expand_glob(&segments));

        let segments = parse_quotes("*.txt").unwrap();
        assert!(should_expand_glob(&segments));
    }
}
```

### Integration Tests (tests/integration_test.rs)

```rust
#[test]
fn test_quotes_preserve_whitespace() {
    let output = Command::new("vsh")
        .arg("-c")
        .arg("echo 'hello  world'")
        .output()
        .unwrap();

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert_eq!(stdout.trim(), "hello  world");
}

#[test]
fn test_single_quotes_no_expansion() {
    let output = Command::new("vsh")
        .arg("-c")
        .arg("echo '$HOME'")
        .output()
        .unwrap();

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert_eq!(stdout.trim(), "$HOME");
}

#[test]
fn test_double_quotes_expansion() {
    let output = Command::new("vsh")
        .arg("-c")
        .arg("echo \"$HOME\"")
        .output()
        .unwrap();

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(!stdout.contains("$HOME")); // Should be expanded
    assert!(stdout.contains("/")); // Should be a path
}

#[test]
fn test_quotes_prevent_glob() {
    let temp = fixtures::test_sandbox("quotes_glob");
    fs::write(temp.path().join("file.txt"), "").unwrap();

    // Unquoted - should expand
    let output = Command::new("ls")
        .arg("*.txt")
        .current_dir(temp.path())
        .output()
        .unwrap();
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.contains("file.txt"));

    // Quoted - should not expand
    let output = Command::new("echo")
        .arg("'*.txt'")
        .current_dir(temp.path())
        .output()
        .unwrap();
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert_eq!(stdout.trim(), "*.txt");
}

#[test]
fn test_backslash_escape() {
    let output = Command::new("echo")
        .arg("hello\\ world")
        .output()
        .unwrap();

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert_eq!(stdout.trim(), "hello world");
}

#[test]
fn test_empty_quotes() {
    // Should pass empty string as argument
    let output = Command::new("vsh")
        .arg("-c")
        .arg("test_cmd '' arg2")
        .output()
        .unwrap();

    // Verify argument count is 3
}
```

## Implementation Phases

### Phase 1: Quote Parser (Week 1)

**Deliverables**:
- [ ] Create `src/quotes.rs` module
- [ ] Implement `parse_quotes()` function
- [ ] Implement `QuoteState` and `QuotedSegment` types
- [ ] Handle single quotes, double quotes, backslash escaping
- [ ] 15+ unit tests covering all quote types

**Acceptance**:
- All unit tests passing
- Edge cases handled (empty quotes, adjacent quotes, unclosed quotes)

### Phase 2: Tokenizer Integration (Week 2)

**Deliverables**:
- [ ] Modify `src/parser.rs` tokenizer for quote-aware splitting
- [ ] Update `Command` enum to use `QuotedToken`
- [ ] Preserve whitespace within quotes
- [ ] Handle quote boundaries correctly

**Acceptance**:
- Tokenizer respects quote boundaries
- Whitespace preserved in quoted strings

### Phase 3: Expansion Integration (Week 2)

**Deliverables**:
- [ ] Modify `expand_glob_args()` to respect quotes
- [ ] Modify `expand_variables()` to respect quotes
- [ ] Single quotes prevent all expansion
- [ ] Double quotes allow variable/command expansion only
- [ ] Glob expansion blocked in all quotes

**Acceptance**:
- Glob expansion works only in unquoted context
- Variables expand in double quotes but not single quotes

### Phase 4: Testing & Polish (Week 3)

**Deliverables**:
- [ ] 10+ integration tests
- [ ] Manual testing with real-world commands
- [ ] Documentation updates
- [ ] Error message improvements
- [ ] STATE.scm updates

**Acceptance**:
- All tests passing
- Common shell patterns work correctly
- Edge cases handled gracefully

## POSIX Compliance Checklist

- [ ] Single quotes preserve all characters literally
- [ ] Double quotes allow variable/command/arithmetic expansion
- [ ] Double quotes prevent glob expansion
- [ ] Backslash escapes next character (outside quotes)
- [ ] Backslash in double quotes escapes $, `, ", \, newline only
- [ ] Backslash in single quotes is literal
- [ ] Adjacent quotes concatenate
- [ ] Empty quotes create empty string argument
- [ ] Unclosed quotes produce error
- [ ] Whitespace preserved within quotes

## Verification

### Manual Test Cases

```bash
# Basic quoting
vsh> echo 'hello world'
hello world

vsh> echo "hello world"
hello world

vsh> echo hello\ world
hello world

# Variable expansion
vsh> VAR=test
vsh> echo '$VAR'
$VAR

vsh> echo "$VAR"
test

vsh> echo \$VAR
$VAR

# Glob expansion
vsh> touch file.txt
vsh> echo *.txt
file.txt

vsh> echo '*.txt'
*.txt

vsh> echo "*.txt"
*.txt

# Adjacent quotes
vsh> echo 'hello'"world"
helloworld

vsh> echo "$HOME"/.config
/home/user/.config

# Empty quotes
vsh> echo ''
<empty line>

vsh> echo "" something
 something
```

## Dependencies

**Crates**:
- None (use standard library only)

**Modified Files**:
- `src/quotes.rs` (new)
- `src/parser.rs` (tokenizer modifications)
- `src/external.rs` (glob expansion modifications)
- `tests/integration_test.rs` (new tests)

## Performance Considerations

**Quote Parsing**:
- Single pass through string: O(n)
- Minimal allocations (reuse buffers where possible)
- No regex (simple state machine)

**Memory**:
- Store quote state with tokens (small overhead)
- Avoid duplicating string content

## Documentation Updates

- [ ] Update README.adoc with quote processing examples
- [ ] Update CHANGELOG.adoc with M13 entry
- [ ] Update STATE.scm with progress
- [ ] Add rustdoc comments to quotes.rs

## Success Criteria

1. **POSIX Compliance**: All POSIX quote rules implemented correctly
2. **Test Coverage**: 90%+ code coverage in quotes module
3. **Integration**: Seamless integration with existing parser/expander
4. **Performance**: No measurable performance regression
5. **Documentation**: Complete rustdoc and user documentation

## Timeline

- **Week 1**: Quote parser implementation + unit tests
- **Week 2**: Tokenizer integration + expansion integration
- **Week 3**: Testing, polish, documentation
- **Total**: 3 weeks

## Next Milestone

After M13 completion:
- **M14**: Full POSIX shell compliance (subset)
  - Command substitution edge cases
  - Here document improvements
  - Additional built-ins (test, [ ], etc.)
  - Full bash compatibility for common patterns
