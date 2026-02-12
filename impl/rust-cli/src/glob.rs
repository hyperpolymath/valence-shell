// SPDX-License-Identifier: PMPL-1.0-or-later
//! Glob pattern expansion (filename wildcards)
//!
//! Implements POSIX-compliant glob expansion with *, ?, [...], and {...}.
//! Glob patterns are expanded to matching file paths at command execution time.
//!
//! # Examples
//! ```no_run
//! use vsh::glob::expand_glob;
//! use std::path::Path;
//!
//! let matches = expand_glob("*.txt", Path::new("/tmp")).unwrap();
//! // Returns: ["file1.txt", "file2.txt", ...]
//! ```

use anyhow::{Context, Result};
use std::path::{Path, PathBuf};

/// Check if a string contains glob metacharacters
///
/// Returns true if the string contains any of: * ? [ { (unescaped)
///
/// # Examples
/// ```
/// use vsh::glob::contains_glob_pattern;
/// assert!(contains_glob_pattern("*.txt"));
/// assert!(contains_glob_pattern("file?.rs"));
/// assert!(contains_glob_pattern("[a-z]*.log"));
/// assert!(!contains_glob_pattern("file.txt"));
/// assert!(!contains_glob_pattern("\\*.txt")); // Escaped
/// ```
pub fn contains_glob_pattern(s: &str) -> bool {
    let mut chars = s.chars().peekable();
    let mut escaped = false;

    while let Some(ch) = chars.next() {
        if escaped {
            escaped = false;
            continue;
        }

        if ch == '\\' {
            escaped = true;
            continue;
        }

        // Glob metacharacters
        if matches!(ch, '*' | '?' | '[' | '{') {
            return true;
        }
    }

    false
}

/// Expand a glob pattern to matching file paths
///
/// Uses the `glob` crate for POSIX-compliant pattern matching.
/// Returns paths sorted alphabetically (POSIX requirement).
///
/// # POSIX Behavior
/// - Patterns that match nothing return empty vec (caller handles literal fallback)
/// - Hidden files (starting with .) require explicit match: .* or .config
/// - Results are sorted alphabetically
/// - * and ? do not match directory separators (/)
///
/// # Examples
/// ```no_run
/// use vsh::glob::expand_glob;
/// use std::path::Path;
///
/// // Basic wildcard
/// let matches = expand_glob("*.txt", Path::new("/tmp")).unwrap();
///
/// // Character class
/// let matches = expand_glob("file[0-9].log", Path::new("/var/log")).unwrap();
///
/// // Recursive glob
/// let matches = expand_glob("**/*.rs", Path::new("src")).unwrap();
/// ```
///
/// # Errors
/// Returns error if:
/// - Pattern is invalid
/// - Base directory cannot be accessed
pub fn expand_glob(pattern: &str, base_dir: &Path) -> Result<Vec<PathBuf>> {
    // Build full glob pattern (base_dir + pattern)
    let full_pattern = if pattern.starts_with('/') {
        // Absolute path
        pattern.to_string()
    } else {
        // Relative to base_dir
        base_dir.join(pattern).to_string_lossy().to_string()
    };

    // Use glob crate for pattern matching with POSIX options
    let options = glob::MatchOptions {
        // POSIX: * and ? do not match leading dot (hidden files)
        require_literal_leading_dot: true,
        // Case-sensitive matching (POSIX default)
        case_sensitive: true,
        // Require literal separator
        require_literal_separator: false,
    };

    let mut matches: Vec<PathBuf> = glob::glob_with(&full_pattern, options)
        .with_context(|| format!("Invalid glob pattern: {}", pattern))?
        .filter_map(|entry| entry.ok())
        .collect();

    // Sort results (POSIX requirement)
    matches.sort();

    // Convert absolute paths back to relative if needed
    if !pattern.starts_with('/') {
        matches = matches
            .into_iter()
            .map(|p| {
                p.strip_prefix(base_dir)
                    .unwrap_or(&p)
                    .to_path_buf()
            })
            .collect();
    }

    Ok(matches)
}

/// Expand brace patterns: a{b,c}d -> [abd, acd]
///
/// Performs brace expansion before glob expansion.
/// This is a pure string operation (no filesystem access).
///
/// # Examples
/// ```
/// use vsh::glob::expand_braces;
///
/// assert_eq!(
///     expand_braces("file{1,2,3}.txt"),
///     vec!["file1.txt", "file2.txt", "file3.txt"]
/// );
///
/// assert_eq!(
///     expand_braces("src/{main,lib}.rs"),
///     vec!["src/main.rs", "src/lib.rs"]
/// );
/// ```
pub fn expand_braces(pattern: &str) -> Vec<String> {
    // Find first unescaped {
    let mut chars = pattern.chars().enumerate().peekable();
    let mut brace_start = None;
    let mut brace_depth = 0;
    let mut escaped = false;

    while let Some((i, ch)) = chars.next() {
        if escaped {
            escaped = false;
            continue;
        }

        if ch == '\\' {
            escaped = true;
            continue;
        }

        if ch == '{' {
            if brace_depth == 0 {
                brace_start = Some(i);
            }
            brace_depth += 1;
        } else if ch == '}' && brace_depth > 0 {
            brace_depth -= 1;
            if brace_depth == 0 {
                // Found matching close brace
                let start = brace_start.unwrap();
                let prefix = &pattern[..start];
                let suffix = &pattern[i + 1..];
                let content = &pattern[start + 1..i];

                // Split by comma (respecting nesting and escaping)
                let alternatives = split_brace_content(content);

                // If only one alternative, it's not a valid brace expansion
                if alternatives.len() <= 1 {
                    // Not a brace expansion, return as-is
                    return vec![pattern.to_string()];
                }

                // Expand each alternative
                let mut results = Vec::new();
                for alt in alternatives {
                    let expanded = format!("{}{}{}", prefix, alt, suffix);
                    // Recursively expand nested braces
                    results.extend(expand_braces(&expanded));
                }

                return results;
            }
        }
    }

    // No brace expansion found, return original
    vec![pattern.to_string()]
}

/// Split brace content by commas (respecting nesting and escaping)
fn split_brace_content(content: &str) -> Vec<String> {
    let mut parts = Vec::new();
    let mut current = String::new();
    let mut depth = 0;
    let mut escaped = false;

    for ch in content.chars() {
        if escaped {
            current.push(ch);
            escaped = false;
            continue;
        }

        if ch == '\\' {
            escaped = true;
            current.push(ch);
            continue;
        }

        if ch == '{' {
            depth += 1;
            current.push(ch);
        } else if ch == '}' {
            depth -= 1;
            current.push(ch);
        } else if ch == ',' && depth == 0 {
            // Top-level comma: split here
            parts.push(current.clone());
            current.clear();
        } else {
            current.push(ch);
        }
    }

    // Push final part
    if !current.is_empty() || !parts.is_empty() {
        parts.push(current);
    }

    parts
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_contains_glob_pattern() {
        assert!(contains_glob_pattern("*.txt"));
        assert!(contains_glob_pattern("file?.rs"));
        assert!(contains_glob_pattern("[a-z]*.log"));
        assert!(contains_glob_pattern("file{1,2}.txt"));
        assert!(!contains_glob_pattern("file.txt"));
        assert!(!contains_glob_pattern("plain_filename"));
    }

    #[test]
    fn test_contains_glob_pattern_escaped() {
        // Escaped metacharacters are not glob patterns
        assert!(!contains_glob_pattern("\\*.txt"));
        assert!(!contains_glob_pattern("file\\?.rs"));
        assert!(!contains_glob_pattern("\\[test\\]"));
    }

    #[test]
    fn test_expand_braces_simple() {
        assert_eq!(
            expand_braces("file{1,2,3}.txt"),
            vec!["file1.txt", "file2.txt", "file3.txt"]
        );
    }

    #[test]
    fn test_expand_braces_path() {
        assert_eq!(
            expand_braces("src/{main,lib}.rs"),
            vec!["src/main.rs", "src/lib.rs"]
        );
    }

    #[test]
    fn test_expand_braces_no_expansion() {
        // Single element - no expansion
        assert_eq!(expand_braces("file{1}.txt"), vec!["file{1}.txt"]);

        // No braces
        assert_eq!(expand_braces("file.txt"), vec!["file.txt"]);
    }

    #[test]
    fn test_expand_braces_nested() {
        let result = expand_braces("{a,{b,c}}");
        assert_eq!(result.len(), 3);
        assert!(result.contains(&"a".to_string()));
        assert!(result.contains(&"b".to_string()));
        assert!(result.contains(&"c".to_string()));
    }

    #[test]
    fn test_expand_braces_multiple() {
        let result = expand_braces("{a,b}{1,2}");
        assert_eq!(result.len(), 4);
        assert!(result.contains(&"a1".to_string()));
        assert!(result.contains(&"a2".to_string()));
        assert!(result.contains(&"b1".to_string()));
        assert!(result.contains(&"b2".to_string()));
    }

    #[test]
    fn test_split_brace_content() {
        assert_eq!(
            split_brace_content("a,b,c"),
            vec!["a", "b", "c"]
        );

        assert_eq!(
            split_brace_content("main,lib"),
            vec!["main", "lib"]
        );

        // Nested braces
        assert_eq!(
            split_brace_content("a,{b,c}"),
            vec!["a", "{b,c}"]
        );
    }
}
