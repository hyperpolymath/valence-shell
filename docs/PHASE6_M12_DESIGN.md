# Phase 6 Milestone 12: Glob Expansion - Design Document

**Version**: 0.15.0
**Status**: Design Phase
**Created**: 2026-01-29
**Author**: Claude Sonnet 4.5 + Jonathan D.A. Jewell

---

## Overview

Implement POSIX-compliant filename globbing (wildcard expansion) for the Valence Shell. Glob patterns allow users to match multiple files with a single pattern, essential for any practical shell.

**Goal**: Users can use `*`, `?`, `[...]`, and `{...}` patterns in commands to match filenames.

---

## Requirements

### Functional Requirements

1. **Wildcard Patterns**
   - `*` - Match zero or more characters
   - `?` - Match exactly one character
   - `[abc]` - Match one character from set {a, b, c}
   - `[a-z]` - Match one character in range a-z
   - `[!abc]` or `[^abc]` - Match one character NOT in set
   - `{a,b,c}` - Brace expansion (match any of a, b, or c)

2. **Pattern Locations**
   - Command arguments: `ls *.txt`
   - Multiple patterns: `cat file1.* file2.*`
   - Nested directories: `src/**/*.rs` (recursive glob)
   - In redirections: `cat file.txt > output_*.log` (expand output filename)

3. **POSIX Behavior**
   - Patterns that match nothing expand to themselves (literal)
   - Hidden files (starting with `.`) require explicit match: `.* or .config`
   - Sorted expansion (alphabetical order)
   - No expansion in single quotes: `'*.txt'` stays literal
   - Expansion in double quotes depends on shell mode

### Non-Functional Requirements

1. **Performance**
   - Fast glob expansion (<10ms for typical patterns)
   - Efficient for large directories (>1000 files)
   - Lazy evaluation where possible

2. **Correctness**
   - Match POSIX glob semantics exactly
   - Handle edge cases (empty dirs, permission errors)
   - Proper escaping (`\*` = literal asterisk)

3. **Reversibility**
   - Glob expansion itself is not reversible (read-only)
   - But operations on globbed files ARE reversible via undo

---

## Architecture

### Components

```
┌─────────────────────────────────────────────┐
│ Parser (parser.rs)                          │
│ - Tokenizes glob patterns                  │
│ - Distinguishes literals from patterns     │
└─────────────┬───────────────────────────────┘
              │
              ↓
┌─────────────────────────────────────────────┐
│ Glob Expander (glob.rs) - NEW MODULE        │
│ - expand_glob(pattern, cwd) -> Vec<String> │
│ - Implements *, ?, [...], {...}            │
│ - Handles hidden files, sorting            │
└─────────────┬───────────────────────────────┘
              │
              ↓
┌─────────────────────────────────────────────┐
│ Command Executor (executable.rs)           │
│ - Receives expanded file list              │
│ - Executes command with expanded args      │
└─────────────────────────────────────────────┘
```

### New File: `src/glob.rs`

```rust
// SPDX-License-Identifier: PMPL-1.0-or-later
//! Glob pattern expansion (filename wildcards)
//!
//! Implements POSIX-compliant glob expansion with *, ?, [...], and {...}.

use anyhow::Result;
use std::path::{Path, PathBuf};

/// Expand a glob pattern to matching file paths
///
/// # Examples
/// ```
/// let matches = expand_glob("*.txt", Path::new("/tmp"))?;
/// // Returns: ["file1.txt", "file2.txt", ...]
/// ```
pub fn expand_glob(pattern: &str, base_dir: &Path) -> Result<Vec<PathBuf>>;

/// Check if a string contains glob metacharacters
pub fn contains_glob_pattern(s: &str) -> bool;

/// Match a single path component against a pattern
fn match_component(component: &str, pattern: &str) -> bool;

/// Expand brace patterns: a{b,c}d -> abd, acd
fn expand_braces(pattern: &str) -> Vec<String>;
```

---

## Implementation Plan

### Phase 1: Basic Wildcards (Week 1)

**Goal**: Implement `*` and `?` wildcards

1. **Create `src/glob.rs`**
   - `expand_glob()` function
   - `contains_glob_pattern()` detector
   - `match_component()` for single-component matching

2. **Implement `*` wildcard**
   - Match zero or more characters
   - Don't match directory separators (`/`)
   - Don't match leading `.` (hidden files) by default

3. **Implement `?` wildcard**
   - Match exactly one character
   - Don't match directory separator

4. **Integration with parser**
   - Detect glob patterns during tokenization
   - Mark tokens as "needs expansion"
   - Call `expand_glob()` before command execution

5. **Testing**
   - Unit tests for pattern matching
   - Integration tests: `ls *.txt`, `cat file?.log`
   - Edge cases: empty results, escaping, hidden files

**Deliverable**: `ls *.txt` and `cat file?.rs` work correctly

---

### Phase 2: Character Classes (Week 2)

**Goal**: Implement `[...]` character classes

1. **Implement `[abc]` - literal set**
   - Match one character from set
   - Example: `file[123].txt` matches `file1.txt`, `file2.txt`, `file3.txt`

2. **Implement `[a-z]` - ranges**
   - Support numeric ranges: `[0-9]`
   - Support alpha ranges: `[a-z]`, `[A-Z]`
   - Support mixed: `[a-zA-Z0-9]`

3. **Implement `[!abc]` and `[^abc]` - negation**
   - Match one character NOT in set
   - Example: `file[!0-9].txt` matches `filea.txt` but not `file1.txt`

4. **Edge cases**
   - `[]` - empty set (invalid, literal)
   - `[` - unclosed bracket (literal)
   - `[-a]` - literal hyphen at start/end
   - `[]]` - literal `]` at start

5. **Testing**
   - Unit tests for character class matching
   - Integration tests with real files
   - Edge case validation

**Deliverable**: `ls file[0-9].txt` and `cat [a-z]*.log` work correctly

---

### Phase 3: Brace Expansion (Week 3)

**Goal**: Implement `{...}` brace expansion

1. **Implement simple braces: `{a,b,c}`**
   - Expand to multiple patterns: `file{1,2,3}.txt` → `file1.txt file2.txt file3.txt`
   - Not a glob pattern (pure string expansion)
   - Happens BEFORE glob expansion

2. **Implement nested braces: `{a,{b,c}}`**
   - Recursive expansion
   - Example: `{a,{b,c}}` → `a b c`

3. **Implement ranges: `{1..5}`, `{a..z}`**
   - Numeric ranges: `file{1..10}.txt` → `file1.txt file2.txt ... file10.txt`
   - Alpha ranges: `{a..c}` → `a b c`
   - Step support: `{1..10..2}` → `1 3 5 7 9`

4. **Combine with globs**
   - `*.{rs,txt}` → expand braces first, then glob each result
   - `src/**/*.{rs,toml}` → find all Rust and TOML files recursively

5. **Edge cases**
   - `{}` - empty braces (literal)
   - `{` - unclosed brace (literal)
   - `{a}` - single element (literal)
   - Escaped braces: `\{a,b\}` (literal)

6. **Testing**
   - Unit tests for brace expansion
   - Integration tests combining braces and globs
   - Edge case validation

**Deliverable**: `ls file{1..5}.txt` and `cat *.{rs,toml}` work correctly

---

### Phase 4: Advanced Features (Week 4)

**Goal**: Recursive globs, escaping, and optimizations

1. **Recursive glob: `**`**
   - `src/**/*.rs` matches all `.rs` files in `src/` and subdirectories
   - Depth-first traversal
   - Symlink handling (follow or not - configurable)
   - Performance: limit depth to avoid infinite loops

2. **Escaping**
   - `\*` → literal asterisk
   - `\?` → literal question mark
   - `\\` → literal backslash
   - Works in all pattern contexts

3. **Tilde expansion: `~`**
   - `~/file.txt` → `/home/user/file.txt`
   - `~user/file.txt` → `/home/user/file.txt`
   - Only at start of path

4. **Hidden file control**
   - `.*` explicitly matches hidden files
   - `*` does NOT match hidden files (POSIX behavior)
   - Option to change behavior (non-standard)

5. **Performance optimizations**
   - Cache directory listings
   - Early exit on first match (for existence checks)
   - Parallel glob expansion for multiple patterns

6. **Error handling**
   - Permission denied → skip directory, continue
   - Non-existent base path → return empty
   - Invalid pattern → return literal (POSIX)

**Deliverable**: All glob features working, well-tested, fast

---

## Testing Strategy

### Unit Tests

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_star_wildcard() {
        assert!(match_component("file.txt", "*.txt"));
        assert!(match_component("abc", "*"));
        assert!(!match_component("file.rs", "*.txt"));
    }

    #[test]
    fn test_question_wildcard() {
        assert!(match_component("a", "?"));
        assert!(match_component("file1.txt", "file?.txt"));
        assert!(!match_component("ab", "?"));
    }

    #[test]
    fn test_character_class() {
        assert!(match_component("a", "[abc]"));
        assert!(match_component("5", "[0-9]"));
        assert!(!match_component("x", "[abc]"));
    }

    #[test]
    fn test_brace_expansion() {
        let expanded = expand_braces("file{1,2,3}.txt");
        assert_eq!(expanded, vec!["file1.txt", "file2.txt", "file3.txt"]);
    }
}
```

### Integration Tests

```rust
// tests/glob_tests.rs

#[test]
fn test_glob_star_expansion() -> Result<()> {
    let temp = tempdir()?;
    touch("file1.txt")?;
    touch("file2.txt")?;
    touch("other.rs")?;

    // Execute: ls *.txt
    let output = shell.execute("ls *.txt")?;
    assert!(output.contains("file1.txt"));
    assert!(output.contains("file2.txt"));
    assert!(!output.contains("other.rs"));

    Ok(())
}

#[test]
fn test_glob_empty_match() -> Result<()> {
    let temp = tempdir()?;

    // Execute: ls *.nonexistent
    // POSIX: expands to literal "*.nonexistent"
    let result = shell.execute("ls *.nonexistent");
    assert!(result.is_err()); // ls fails on non-existent file

    Ok(())
}
```

### Property Tests

```rust
proptest! {
    #[test]
    fn prop_glob_expansion_sorted(pattern in "[a-z]{1,5}\\*") {
        let matches = expand_glob(&pattern, Path::new("/tmp"))?;
        // Result must be sorted
        assert!(matches.windows(2).all(|w| w[0] <= w[1]));
    }

    #[test]
    fn prop_glob_no_expansion_when_escaped(s in "[a-z]{1,10}") {
        let escaped = format!("\\{}", s);
        let matches = expand_glob(&escaped, Path::new("/tmp"))?;
        // Escaped patterns return literal
        assert_eq!(matches, vec![s]);
    }
}
```

---

## Edge Cases

### 1. No Matches
**POSIX**: Pattern expands to itself (literal)

```bash
$ ls *.nonexistent
ls: cannot access '*.nonexistent': No such file or directory
```

**Implementation**: If `expand_glob()` returns empty, return original pattern as literal string.

---

### 2. Hidden Files

**POSIX**: `*` does NOT match files starting with `.`

```bash
$ ls *          # Does NOT show .hidden
$ ls .*         # Shows .hidden
$ ls .config*   # Shows .config and .config.backup
```

**Implementation**: `match_component()` checks if pattern starts with `.` before matching hidden files.

---

### 3. Directory Separators

**POSIX**: `*` and `?` do NOT match `/`

```bash
$ ls src/*/*.rs    # Match one level deep
$ ls src/**/*.rs   # Match all levels (bash extension)
```

**Implementation**: Split pattern by `/`, expand each component separately.

---

### 4. Escaping

```bash
$ ls \*.txt        # Literal "*.txt" (if file exists)
$ ls 'file*.txt'   # Single quotes prevent expansion
$ ls "file*.txt"   # Double quotes still expand in bash (shell-dependent)
```

**Implementation**:
- Backslash escaping in tokenizer
- Single quotes prevent glob expansion
- Double quotes: expand or not? (shell-dependent behavior)

---

### 5. Permission Errors

```bash
$ ls /root/*       # Permission denied, but don't crash
ls: cannot open directory '/root': Permission denied
```

**Implementation**: Skip directories we can't read, log warning, continue with accessible matches.

---

### 6. Symlinks

```bash
$ ls link/*        # Follow symlink if it points to directory?
```

**Options**:
- Follow symlinks (default)
- Don't follow (require flag)
- Follow only non-recursive (depth=1)

**Implementation**: Use `std::fs::metadata()` vs `std::fs::symlink_metadata()`.

---

## Dependencies

### Rust Crates

Option 1: **Use `glob` crate** (most common)
```toml
[dependencies]
glob = "0.3"
```
- Pros: Battle-tested, POSIX-compliant, handles edge cases
- Cons: External dependency, less control

Option 2: **Use `globset` crate** (from `ripgrep`)
```toml
[dependencies]
globset = "0.4"
```
- Pros: Very fast, supports gitignore-style patterns, used by `rg`
- Cons: Slightly different semantics, more complex API

Option 3: **Implement from scratch**
- Pros: Full control, educational, no dependencies
- Cons: More work, more bugs, harder to get POSIX-compliant

**Recommendation**: Start with `glob` crate for correctness, optimize later if needed.

---

## Integration Points

### 1. Parser (`parser.rs`)

**Before glob expansion:**
```rust
Token::Word("*.txt")  // Unparsed token
```

**After tokenization (new):**
```rust
Token::GlobPattern("*.txt")  // Mark as glob pattern
```

**Changes needed:**
- Detect glob metacharacters during tokenization
- Mark tokens as `GlobPattern` vs `Word`
- Don't expand inside quotes

---

### 2. Executor (`executable.rs`)

**Current:**
```rust
fn execute_external(args: Vec<String>, ...) { ... }
```

**New:**
```rust
fn execute_external(args: Vec<Token>, state: &ShellState, ...) {
    let expanded_args: Vec<String> = args.iter()
        .flat_map(|token| match token {
            Token::GlobPattern(pattern) => {
                expand_glob(pattern, state.cwd())
                    .unwrap_or_else(|_| vec![pattern.clone()])
            }
            Token::Word(word) => vec![word.clone()],
            _ => vec![],
        })
        .collect();

    // Execute with expanded args
    Command::new(&expanded_args[0])
        .args(&expanded_args[1..])
        .spawn()?;
}
```

---

### 3. Redirections (`redirection.rs`)

**Support glob in redirection targets:**
```rust
Redirection::Output { file } => {
    // Expand glob pattern
    let files = expand_glob(file, state.cwd())?;

    if files.len() != 1 {
        bail!("Ambiguous redirect: {} matches {} files", file, files.len());
    }

    let target = &files[0];
    // Open file for writing...
}
```

**POSIX**: Redirects must expand to exactly one file, otherwise error.

---

## Correspondence to Lean Proofs

**Glob expansion is NOT formally verified** (it's a shell convenience, not a filesystem primitive).

However:
- Operations on globbed files ARE verified (mkdir, rm, etc.)
- Glob expansion is pure (no side effects)
- Testing ensures correctness

**Relationship to proofs:**
```
ls *.txt  →  expand("*.txt")  →  ["a.txt", "b.txt"]
          →  ls("a.txt"); ls("b.txt")
                ↑ Each operation verified
```

Glob expansion is a **pre-processing step** before verified operations.

---

## Rollout Plan

### v0.15.0-alpha (Week 1)
- Basic `*` and `?` wildcards
- Unit tests passing
- `ls *.txt` works

### v0.15.0-beta (Week 2-3)
- Character classes `[...]`
- Brace expansion `{...}`
- Integration tests passing

### v0.15.0-rc (Week 4)
- Recursive globs `**`
- Escaping, hidden files
- Performance optimization
- All tests passing

### v0.15.0 (Release)
- Full glob support
- Documentation complete
- Update STATE.scm, CHANGELOG.adoc

---

## Success Criteria

✅ **Functional**:
- All POSIX glob patterns work correctly
- `ls *.txt`, `cat file?.log`, `rm [0-9]*.tmp` all work
- Matches bash behavior on standard test cases

✅ **Testing**:
- 30+ unit tests covering all patterns
- 15+ integration tests with real files
- 5+ property tests for edge cases
- All tests passing

✅ **Performance**:
- Glob expansion <10ms for typical use (100 files)
- <100ms for large directories (10,000 files)
- No noticeable lag in interactive use

✅ **Documentation**:
- PHASE6_M12_COMPLETE.md written
- Examples in GETTING_STARTED.md
- Help text updated

---

## References

- [POSIX Pattern Matching](https://pubs.opengroup.org/onlinepubs/9699919799/utilities/V3_chap02.html#tag_18_13)
- [Bash Glob Patterns](https://www.gnu.org/software/bash/manual/html_node/Pattern-Matching.html)
- [Rust `glob` crate](https://docs.rs/glob/latest/glob/)
- [Rust `globset` crate](https://docs.rs/globset/latest/globset/)

---

## Next Steps

1. Review this design document ✅
2. Choose glob implementation approach (crate vs from-scratch)
3. Create `src/glob.rs` module
4. Implement Phase 1 (basic wildcards)
5. Write tests and iterate

**Estimated timeline**: 4 weeks to full implementation (v0.15.0)
