// SPDX-License-Identifier: PMPL-1.0-or-later
//! Quote Processing (Phase 6 M13)
//!
//! Implements POSIX-compliant quote processing for shell arguments:
//! - Single quotes (') - preserve all characters literally
//! - Double quotes (") - allow variable/command expansion, prevent glob
//! - Backslash (\) - escape next character
//!
//! # POSIX Semantics
//!
//! **Single Quotes**:
//! - All characters literal (no expansion whatsoever)
//! - Cannot contain single quote (even escaped)
//! - Whitespace preserved
//!
//! **Double Quotes**:
//! - Variable expansion: $VAR, ${VAR}
//! - Command substitution: $(cmd), `cmd`
//! - Arithmetic expansion: $((expr))
//! - NO glob expansion
//! - Backslash escapes: \$, \`, \", \\, \newline
//! - Whitespace preserved
//!
//! **Backslash (unquoted)**:
//! - Escapes next character literally
//! - At end of line: line continuation
//!
//! # Examples
//!
//! ```no_run
//! use vsh::quotes::{parse_quotes, QuoteState};
//!
//! // Single quotes - no expansion
//! let segments = parse_quotes("'$HOME'").unwrap();
//! assert_eq!(segments[0].state, QuoteState::SingleQuoted);
//!
//! // Double quotes - expansion allowed
//! let segments = parse_quotes("\"$HOME\"").unwrap();
//! assert_eq!(segments[0].state, QuoteState::DoubleQuoted);
//!
//! // Backslash escape
//! let segments = parse_quotes("hello\\ world").unwrap();
//! // Content will be "hello world"
//! ```

use anyhow::{Context, Result};

/// Quote state for a segment of text
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum QuoteState {
    /// No quotes - full expansion (variables, globs, command substitution)
    Unquoted,

    /// Single-quoted - literal text (no expansion)
    SingleQuoted,

    /// Double-quoted - variable/command expansion only (no globs)
    DoubleQuoted,
}

/// A segment of text with its quote state
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct QuotedSegment {
    /// The text content (quotes removed)
    pub content: String,

    /// The quote state of this segment
    pub state: QuoteState,
}

impl QuotedSegment {
    /// Create a new quoted segment
    pub fn new(content: String, state: QuoteState) -> Self {
        Self { content, state }
    }

    /// Check if this segment allows variable expansion
    pub fn allows_variable_expansion(&self) -> bool {
        matches!(
            self.state,
            QuoteState::Unquoted | QuoteState::DoubleQuoted
        )
    }

    /// Check if this segment allows glob expansion
    pub fn allows_glob_expansion(&self) -> bool {
        self.state == QuoteState::Unquoted
    }
}

/// Parse a string into quoted segments
///
/// Processes quotes and backslash escapes according to POSIX rules.
/// Returns a vector of segments, each with its quote state.
///
/// # POSIX Quote Rules
///
/// - `'...'` - Single quotes: all characters literal
/// - `"..."` - Double quotes: expansion allowed except globs
/// - `\x` - Backslash: escapes next character (outside quotes)
/// - `\x` in `"..."` - Escapes only: $ ` " \ newline
/// - `\x` in `'...'` - Literal backslash (no escaping)
///
/// # Examples
///
/// ```no_run
/// use vsh::quotes::parse_quotes;
///
/// // Single quotes
/// let segments = parse_quotes("'hello world'").unwrap();
/// assert_eq!(segments.len(), 1);
/// assert_eq!(segments[0].content, "hello world");
///
/// // Double quotes
/// let segments = parse_quotes("\"$HOME/.config\"").unwrap();
/// assert_eq!(segments[0].content, "$HOME/.config");
///
/// // Mixed quotes
/// let segments = parse_quotes("'hello'\" world\"").unwrap();
/// assert_eq!(segments.len(), 2);
/// ```
///
/// # Errors
///
/// Returns error if:
/// - Quote is unclosed (missing closing quote)
pub fn parse_quotes(input: &str) -> Result<Vec<QuotedSegment>> {
    let mut segments = Vec::new();
    let mut current = String::new();
    let mut state = QuoteState::Unquoted;
    let mut chars = input.chars().peekable();

    while let Some(ch) = chars.next() {
        match (state.clone(), ch) {
            // === UNQUOTED STATE ===

            // Unquoted → single quote
            (QuoteState::Unquoted, '\'') => {
                if !current.is_empty() {
                    segments.push(QuotedSegment::new(current.clone(), QuoteState::Unquoted));
                    current.clear();
                }
                state = QuoteState::SingleQuoted;
            }

            // Unquoted → double quote
            (QuoteState::Unquoted, '"') => {
                if !current.is_empty() {
                    segments.push(QuotedSegment::new(current.clone(), QuoteState::Unquoted));
                    current.clear();
                }
                state = QuoteState::DoubleQuoted;
            }

            // Unquoted backslash escape
            (QuoteState::Unquoted, '\\') => {
                if let Some(next) = chars.next() {
                    // Backslash-newline removed (line continuation)
                    if next != '\n' {
                        current.push(next);
                    }
                } else {
                    // Backslash at end of input - keep it
                    current.push('\\');
                }
            }

            // === SINGLE QUOTE STATE ===

            // Single quote → close
            (QuoteState::SingleQuoted, '\'') => {
                segments.push(QuotedSegment::new(
                    current.clone(),
                    QuoteState::SingleQuoted,
                ));
                current.clear();
                state = QuoteState::Unquoted;
            }

            // Single quote - all characters literal
            (QuoteState::SingleQuoted, ch) => {
                current.push(ch);
            }

            // === DOUBLE QUOTE STATE ===

            // Double quote → close
            (QuoteState::DoubleQuoted, '"') => {
                segments.push(QuotedSegment::new(
                    current.clone(),
                    QuoteState::DoubleQuoted,
                ));
                current.clear();
                state = QuoteState::Unquoted;
            }

            // Double quote backslash (limited escaping)
            (QuoteState::DoubleQuoted, '\\') => {
                if let Some(&next) = chars.peek() {
                    // Only escape these special characters in double quotes
                    if matches!(next, '$' | '`' | '"' | '\\' | '\n') {
                        chars.next(); // Consume the next character
                        if next != '\n' {
                            // Backslash-newline removed
                            current.push(next);
                        }
                    } else {
                        // Other characters: keep the backslash
                        current.push('\\');
                    }
                } else {
                    // Backslash at end of input
                    current.push('\\');
                }
            }

            // Double quote - regular character
            (QuoteState::DoubleQuoted, ch) => {
                current.push(ch);
            }

            // === UNQUOTED REGULAR CHARACTER ===
            (QuoteState::Unquoted, ch) => {
                current.push(ch);
            }
        }
    }

    // Check for unclosed quotes
    if state != QuoteState::Unquoted {
        anyhow::bail!("Unclosed quote (expected closing {})",
            match state {
                QuoteState::SingleQuoted => "'",
                QuoteState::DoubleQuoted => "\"",
                QuoteState::Unquoted => unreachable!(),
            }
        );
    }

    // Push final segment if any
    if !current.is_empty() {
        segments.push(QuotedSegment::new(current, state));
    }

    Ok(segments)
}

/// Check if quoted segments should undergo glob expansion
///
/// Returns true if any unquoted segment contains glob patterns.
/// Quoted segments (single or double) never expand globs.
///
/// # Examples
///
/// ```no_run
/// use vsh::quotes::{parse_quotes, should_expand_glob};
///
/// // Unquoted glob pattern → expand
/// let segments = parse_quotes("*.txt").unwrap();
/// assert!(should_expand_glob(&segments));
///
/// // Single-quoted glob → no expansion
/// let segments = parse_quotes("'*.txt'").unwrap();
/// assert!(!should_expand_glob(&segments));
///
/// // Double-quoted glob → no expansion
/// let segments = parse_quotes("\"*.txt\"").unwrap();
/// assert!(!should_expand_glob(&segments));
/// ```
pub fn should_expand_glob(segments: &[QuotedSegment]) -> bool {
    segments.iter().any(|seg| {
        seg.allows_glob_expansion() && crate::glob::contains_glob_pattern(&seg.content)
    })
}

/// Reconstruct the expanded string from quoted segments
///
/// For each segment:
/// - Unquoted/DoubleQuoted: content as-is (caller handles expansion)
/// - SingleQuoted: content as-is (literal)
///
/// This function does NOT perform variable/command expansion.
/// Use `expand_segments_with_state()` for full expansion.
///
/// # Examples
///
/// ```no_run
/// use vsh::quotes::{parse_quotes, reconstruct_string};
///
/// let segments = parse_quotes("'hello'\" world\"").unwrap();
/// let result = reconstruct_string(&segments);
/// assert_eq!(result, "hello world");
/// ```
pub fn reconstruct_string(segments: &[QuotedSegment]) -> String {
    segments
        .iter()
        .map(|seg| seg.content.as_str())
        .collect::<Vec<_>>()
        .join("")
}

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
    fn test_double_quotes() {
        let segments = parse_quotes("\"$HOME\"").unwrap();
        assert_eq!(segments.len(), 1);
        assert_eq!(segments[0].content, "$HOME");
        assert_eq!(segments[0].state, QuoteState::DoubleQuoted);
    }

    #[test]
    fn test_unquoted() {
        let segments = parse_quotes("hello").unwrap();
        assert_eq!(segments.len(), 1);
        assert_eq!(segments[0].content, "hello");
        assert_eq!(segments[0].state, QuoteState::Unquoted);
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
    fn test_mixed_quotes() {
        let segments = parse_quotes("pre'quoted'post").unwrap();
        assert_eq!(segments.len(), 3);
        assert_eq!(segments[0].content, "pre");
        assert_eq!(segments[0].state, QuoteState::Unquoted);
        assert_eq!(segments[1].content, "quoted");
        assert_eq!(segments[1].state, QuoteState::SingleQuoted);
        assert_eq!(segments[2].content, "post");
        assert_eq!(segments[2].state, QuoteState::Unquoted);
    }

    #[test]
    fn test_backslash_escape_unquoted() {
        let segments = parse_quotes("hello\\ world").unwrap();
        assert_eq!(segments.len(), 1);
        assert_eq!(segments[0].content, "hello world");
        assert_eq!(segments[0].state, QuoteState::Unquoted);
    }

    #[test]
    fn test_backslash_in_single_quotes() {
        let segments = parse_quotes("'back\\slash'").unwrap();
        assert_eq!(segments.len(), 1);
        assert_eq!(segments[0].content, "back\\slash");
        assert_eq!(segments[0].state, QuoteState::SingleQuoted);
    }

    #[test]
    fn test_backslash_in_double_quotes() {
        let segments = parse_quotes("\"\\$HOME\"").unwrap();
        assert_eq!(segments.len(), 1);
        assert_eq!(segments[0].content, "$HOME");
        assert_eq!(segments[0].state, QuoteState::DoubleQuoted);

        // Backslash before non-special character stays
        let segments = parse_quotes("\"\\a\"").unwrap();
        assert_eq!(segments[0].content, "\\a");
    }

    #[test]
    fn test_empty_quotes() {
        let segments = parse_quotes("''").unwrap();
        assert_eq!(segments.len(), 1);
        assert_eq!(segments[0].content, "");
        assert_eq!(segments[0].state, QuoteState::SingleQuoted);

        let segments = parse_quotes("\"\"").unwrap();
        assert_eq!(segments.len(), 1);
        assert_eq!(segments[0].content, "");
        assert_eq!(segments[0].state, QuoteState::DoubleQuoted);
    }

    #[test]
    fn test_unclosed_single_quote_error() {
        let result = parse_quotes("'unclosed");
        assert!(result.is_err());
        assert!(result.unwrap_err().to_string().contains("Unclosed quote"));
    }

    #[test]
    fn test_unclosed_double_quote_error() {
        let result = parse_quotes("\"unclosed");
        assert!(result.is_err());
        assert!(result.unwrap_err().to_string().contains("Unclosed quote"));
    }

    #[test]
    fn test_glob_no_expansion_in_quotes() {
        // Unquoted - should expand
        let segments = parse_quotes("*.txt").unwrap();
        assert!(should_expand_glob(&segments));

        // Single quoted - no expansion
        let segments = parse_quotes("'*.txt'").unwrap();
        assert!(!should_expand_glob(&segments));

        // Double quoted - no expansion
        let segments = parse_quotes("\"*.txt\"").unwrap();
        assert!(!should_expand_glob(&segments));
    }

    #[test]
    fn test_reconstruct_string() {
        let segments = parse_quotes("'hello'\" world\"").unwrap();
        let result = reconstruct_string(&segments);
        assert_eq!(result, "hello world");

        let segments = parse_quotes("one'two'three").unwrap();
        let result = reconstruct_string(&segments);
        assert_eq!(result, "onetwothree");
    }

    #[test]
    fn test_allows_variable_expansion() {
        let segments = parse_quotes("'$VAR'").unwrap();
        assert!(!segments[0].allows_variable_expansion());

        let segments = parse_quotes("\"$VAR\"").unwrap();
        assert!(segments[0].allows_variable_expansion());

        let segments = parse_quotes("$VAR").unwrap();
        assert!(segments[0].allows_variable_expansion());
    }

    #[test]
    fn test_allows_glob_expansion() {
        let segments = parse_quotes("'*.txt'").unwrap();
        assert!(!segments[0].allows_glob_expansion());

        let segments = parse_quotes("\"*.txt\"").unwrap();
        assert!(!segments[0].allows_glob_expansion());

        let segments = parse_quotes("*.txt").unwrap();
        assert!(segments[0].allows_glob_expansion());
    }

    #[test]
    fn test_line_continuation() {
        // Backslash-newline in unquoted context
        let segments = parse_quotes("hello\\\nworld").unwrap();
        assert_eq!(segments[0].content, "helloworld");

        // Backslash-newline in double quotes
        let segments = parse_quotes("\"hello\\\nworld\"").unwrap();
        assert_eq!(segments[0].content, "helloworld");

        // Backslash-newline in single quotes (literal)
        let segments = parse_quotes("'hello\\\nworld'").unwrap();
        assert_eq!(segments[0].content, "hello\\\nworld");
    }

    #[test]
    fn test_whitespace_preservation() {
        let segments = parse_quotes("'hello  world'").unwrap();
        assert_eq!(segments[0].content, "hello  world");

        let segments = parse_quotes("\"hello  world\"").unwrap();
        assert_eq!(segments[0].content, "hello  world");
    }
}
