# Phase 6 Milestone 9: Here Documents

**Version**: 0.13.0
**Status**: Planning
**Date**: 2026-01-29

---

## Overview

Implement POSIX here documents (`<<EOF`) and here strings (`<<<`). These provide multi-line input to commands without needing temporary files.

## Syntax

### Here Documents (`<<DELIMITER`)

```bash
# Basic here document
cat <<EOF
Line 1
Line 2
Line 3
EOF

# With variable expansion
name="World"
cat <<EOF
Hello, $name!
Today is $(date)
EOF

# Quoted delimiter (no expansion)
cat <<'EOF'
Literal $variable
Not expanded: $(command)
EOF

# Indented here document (<<- strips leading tabs)
cat <<-EOF
	Line with tab
	Another tabbed line
EOF
```

### Here Strings (`<<<`)

```bash
# Single-line input
grep pattern <<<"Some text to search"

# With variable expansion
name="test"
wc -w <<<"Hello $name world"

# Literal (single quotes)
grep '$' <<<'Literal $dollar'
```

## POSIX Compliance

**From POSIX.1-2017 Section 2.7.4:**

> The redirection operators `<<` and `<<-` both allow redirection of subsequent lines read by the shell to the input of a command.
>
> The here-document shall be treated as a single word that begins after the next newline and continues until a line containing only the delimiter (with no trailing blanks).
>
> If any part of the delimiter is quoted, the lines of the here-document shall not be expanded. Otherwise, parameter expansion, command substitution, and arithmetic expansion shall occur.
>
> If the redirection operator is `<<-`, all leading `<tab>` characters shall be stripped from input lines and the line containing the delimiter.

**Key Points:**
1. Delimiter can be any word (typically EOF, END, or 'MARKER')
2. Delimiter line must contain ONLY the delimiter (no whitespace after)
3. Quoted delimiter (`<<'EOF'` or `<<"EOF"` or `<<\EOF`) disables expansion
4. `<<-` strips leading tabs (not spaces!) from each line
5. Expansion happens unless delimiter is quoted
6. Here document is treated as single redirected input

## Implementation Plan

### 1. Parser Extensions

**Add to Token enum:**

```rust
#[derive(Debug, Clone, PartialEq)]
pub enum Token {
    // ... existing tokens ...
    HereDoc,        // <<
    HereDocDash,    // <<-
    HereString,     // <<<
}
```

**Add to Redirection enum:**

```rust
#[derive(Debug, Clone, PartialEq)]
pub enum Redirection {
    // ... existing redirections ...
    HereDoc {
        delimiter: String,
        content: String,
        expand: bool,
        strip_tabs: bool,
    },
    HereString {
        content: String,
        expand: bool,
    },
}
```

### 2. Tokenizer Updates

**In `tokenize()`:**

```rust
'<' => {
    chars.next();
    if chars.peek() == Some(&'<') {
        chars.next();
        if chars.peek() == Some(&'<') {
            chars.next();
            tokens.push(Token::HereString);  // <<<
        } else if chars.peek() == Some(&'-') {
            chars.next();
            tokens.push(Token::HereDocDash); // <<-
        } else {
            tokens.push(Token::HereDoc);      // <<
        }
    } else {
        tokens.push(Token::InputRedirect);    // <
    }
}
```

### 3. Here Document Parsing

**New function in `parser.rs`:**

```rust
fn parse_heredoc(
    input: &str,
    delimiter: &str,
    strip_tabs: bool,
    expand: bool,
) -> Result<String> {
    let mut lines: Vec<&str> = input.lines().collect();
    let mut content_lines = Vec::new();

    // Find delimiter line
    let mut found_delimiter = false;
    for line in &lines {
        if line.trim() == delimiter {
            found_delimiter = true;
            break;
        }

        let processed_line = if strip_tabs {
            line.trim_start_matches('\t')
        } else {
            line
        };

        content_lines.push(processed_line);
    }

    if !found_delimiter {
        return Err(anyhow!("Here document not closed: missing delimiter {}", delimiter));
    }

    let content = content_lines.join("\n");

    if expand {
        // Perform variable expansion, command substitution, arithmetic
        expand_with_command_sub(&content, state)
    } else {
        // Literal content (delimiter was quoted)
        Ok(content)
    }
}
```

### 4. Here String Parsing

**Add to `parse_command()`:**

```rust
Token::HereString => {
    // Next token should be the string content
    let content_token = expect_word(&tokens, i + 1, "here string")?;

    // Check if content is quoted (disables expansion)
    let (content, expand) = if content_token.starts_with('\'') || content_token.starts_with('"') {
        (strip_quotes(&content_token), false)
    } else {
        (content_token.clone(), true)
    };

    redirects.push(Redirection::HereString { content, expand });
    i += 2;
}
```

### 5. Redirection Setup

**Update `RedirectSetup` in `redirection.rs`:**

```rust
impl RedirectSetup {
    pub fn setup_heredoc(&mut self, content: &str) -> Result<()> {
        // Create temporary file for here document content
        let temp_path = format!("/tmp/vsh-heredoc-{}-{}",
            std::process::id(),
            self.heredoc_counter.fetch_add(1, Ordering::SeqCst)
        );

        // Write content to temp file
        std::fs::write(&temp_path, content)?;

        // Open as stdin
        let file = File::open(&temp_path)?;
        self.stdin = Some(file);
        self.temp_files.push(PathBuf::from(temp_path));

        Ok(())
    }

    pub fn setup_herestring(&mut self, content: &str) -> Result<()> {
        // Similar to heredoc, but adds trailing newline
        let content_with_newline = format!("{}\n", content);
        self.setup_heredoc(&content_with_newline)
    }
}
```

### 6. Cleanup

**Ensure temporary files are removed:**

```rust
impl Drop for RedirectSetup {
    fn drop(&mut self) {
        for temp_file in &self.temp_files {
            let _ = std::fs::remove_file(temp_file);
        }
    }
}
```

## Parsing Strategy

### Challenge: Multi-line Input

Here documents span multiple lines, but current `parse_command()` operates on single-line input.

**Solution**: Pre-process here documents before main parsing

```rust
pub fn preprocess_heredocs(input: &str) -> Result<(String, Vec<(String, String, bool, bool)>)> {
    // Scan for << and <<- redirections
    // Extract delimiter
    // Read subsequent lines until delimiter found
    // Store (delimiter, content, expand, strip_tabs) tuples
    // Return modified command line + heredoc data
}
```

**Example**:

Input:
```
cat <<EOF
line 1
line 2
EOF
```

After preprocessing:
- Command: `cat <<HEREDOC_0`
- Heredocs: `[("EOF", "line 1\nline 2", true, false)]`

### Integration with REPL

**Update `main.rs` REPL loop:**

```rust
loop {
    let mut line = read_line()?;

    // Check for here document
    if line.contains("<<") {
        line = read_heredoc(&mut reader, line)?;
    }

    // Parse and execute
    execute_line(&line, &mut state)?;
}

fn read_heredoc(reader: &mut impl BufRead, initial_line: String) -> Result<String> {
    // Extract delimiter from initial line
    let delimiter = extract_heredoc_delimiter(&initial_line)?;

    let mut full_input = initial_line;
    full_input.push('\n');

    // Read until delimiter found
    loop {
        let mut line = String::new();
        reader.read_line(&mut line)?;

        if line.trim() == delimiter {
            full_input.push_str(&line);
            break;
        }

        full_input.push_str(&line);
    }

    Ok(full_input)
}
```

## Testing Strategy

### Unit Tests

```rust
#[test]
fn test_heredoc_basic() {
    let input = "cat <<EOF\nLine 1\nLine 2\nEOF";
    // Should create temp file with content "Line 1\nLine 2"
}

#[test]
fn test_heredoc_expansion() {
    let mut state = ShellState::new("/tmp").unwrap();
    state.set_variable("name", "World");

    let input = "cat <<EOF\nHello, $name!\nEOF";
    // Should expand to "Hello, World!"
}

#[test]
fn test_heredoc_quoted_delimiter() {
    let input = "cat <<'EOF'\n$variable\nEOF";
    // Should NOT expand, content is literal "$variable"
}

#[test]
fn test_heredoc_strip_tabs() {
    let input = "cat <<-EOF\n\tLine 1\n\tLine 2\nEOF";
    // Should produce "Line 1\nLine 2" (tabs stripped)
}

#[test]
fn test_herestring_basic() {
    let input = "cat <<<\"test string\"";
    // Should pass "test string\n" as stdin
}

#[test]
fn test_herestring_expansion() {
    let mut state = ShellState::new("/tmp").unwrap();
    state.set_variable("x", "value");

    let input = "cat <<<\"$x\"";
    // Should expand to "value\n"
}
```

### Integration Tests

```bash
# Basic here document
vsh> cat <<EOF
Line 1
Line 2
EOF
Line 1
Line 2

# With expansion
vsh> name=Test
vsh> cat <<EOF
Hello $name
Result: $((5 + 3))
EOF
Hello Test
Result: 8

# Quoted delimiter (no expansion)
vsh> cat <<'END'
$variable $(command)
END
$variable $(command)

# Here string
vsh> wc -w <<<"one two three"
3
```

## Edge Cases

1. **Delimiter with special characters**: `<<'EOF$'`, `<<"END)"`
2. **Empty here document**: `cat <<EOF\nEOF`
3. **Here document with only whitespace**
4. **Multiple here documents in one command**: `cmd <<EOF1 ... EOF1 <<EOF2 ... EOF2`
5. **Here document in pipeline**: `cat <<EOF | grep pattern\ndata\nEOF`
6. **Here string with quotes**: `<<<"test \"quoted\" string"`
7. **Tab vs space stripping**: `<<-` only strips tabs, not spaces

## Deferred Features

**For later:**
1. **Multiple here documents per command** - requires tracking multiple temp files
2. **Here documents in background jobs** - need job control (M10)
3. **Here documents in scripts** - need script execution support

## Success Criteria

- [ ] Parse `<<DELIMITER` syntax
- [ ] Parse `<<-DELIMITER` syntax (tab stripping)
- [ ] Parse `<<<string` syntax
- [ ] Detect quoted vs unquoted delimiters
- [ ] Read multi-line input until delimiter
- [ ] Create temporary files for here doc content
- [ ] Expand variables/commands/arithmetic (when not quoted)
- [ ] Strip leading tabs with `<<-`
- [ ] Clean up temporary files after command
- [ ] All unit tests pass
- [ ] Integration tests pass
- [ ] REPL handles multi-line here documents
- [ ] Documentation complete

## Architecture Notes

### Temporary File Management

- Path: `/tmp/vsh-heredoc-<pid>-<counter>`
- Created before command execution
- Removed after command completes (Drop impl)
- Permissions: 0600 (owner read/write only)

### Expansion Rules

| Syntax | Expansion |
|--------|-----------|
| `<<EOF` | Yes |
| `<<'EOF'` | No |
| `<<"EOF"` | No |
| `<<\EOF` | No |
| `<<<word` | Yes |
| `<<<'word'` | No |

### Integration with Existing Features

- Here docs work with command substitution: `cat <<EOF\n$(ls)\nEOF`
- Here docs work with arithmetic: `cat <<EOF\n$((5+3))\nEOF`
- Here docs work with pipelines: `cat <<EOF | grep test\ntest\nEOF`
- Here docs work with process sub: `diff <(cat <<EOF\nA\nEOF) <(cat <<EOF\nB\nEOF)`

## Proven Integration (Future)

**Current** (Rust temp files):
```rust
std::fs::write(temp_path, content)?;
```

**Future** (Proven SafeFile):
```rust
extern "C" {
    fn idris_create_temp_heredoc(content: *const u8, len: usize) -> i32;
}
```

**Benefits**:
- ✅ Temp file creation proven leak-free
- ✅ File descriptor tracking proven correct
- ✅ Cleanup proven complete (no orphaned files)
- ✅ Race conditions proven impossible

See: `proven/src/Proven/SafeFile.idr`

---

**Next Steps:**
1. Update tokenizer for `<<`, `<<-`, `<<<`
2. Add here document REPL reading logic
3. Add here document redirection setup
4. Add temporary file cleanup
5. Write comprehensive tests
6. Update version to 0.13.0
