// SPDX-License-Identifier: PLMP-1.0-or-later
//! Syntax Highlighting for VSH
//!
//! Provides real-time syntax highlighting in the REPL using nu-ansi-term colors.
//! Highlights:
//! - Built-in commands (green)
//! - External commands (blue)
//! - Paths (cyan if exist, yellow if not)
//! - Strings (magenta)
//! - Operators and redirections (bright white)
//! - Comments (dark gray)
//! - Invalid syntax (red)

use nu_ansi_term::{Color, Style};
use reedline::{Highlighter, StyledText};
use std::path::Path;

/// VSH syntax highlighter
pub struct VshHighlighter {
    /// List of built-in commands
    builtins: Vec<String>,
}

impl Default for VshHighlighter {
    fn default() -> Self {
        Self::new()
    }
}

impl VshHighlighter {
    /// Create new syntax highlighter
    pub fn new() -> Self {
        let builtins = vec![
            // Navigation
            "cd", "pwd", "pushd", "popd", "dirs",
            // File operations
            "mkdir", "rmdir", "touch", "rm", "cp", "mv", "cat", "ls",
            // VSH-specific
            "undo", "redo", "history",
            // Transactions
            "begin", "commit", "rollback",
            // Utilities
            "echo", "help", "exit",
            // Test
            "test", "[",
            // Variables
            "export", "unset", "set",
            // Jobs
            "jobs", "fg", "bg", "kill",
        ]
        .iter()
        .map(|s| s.to_string())
        .collect();

        Self { builtins }
    }

    /// Check if a command is a built-in
    fn is_builtin(&self, cmd: &str) -> bool {
        self.builtins.contains(&cmd.to_string())
    }

    /// Check if a command exists in PATH
    fn is_external_command(&self, cmd: &str) -> bool {
        if let Ok(path_var) = std::env::var("PATH") {
            for dir in path_var.split(':') {
                let exe_path = Path::new(dir).join(cmd);
                if exe_path.exists() && exe_path.is_file() {
                    // Check if executable (Unix)
                    #[cfg(unix)]
                    {
                        use std::os::unix::fs::PermissionsExt;
                        if let Ok(metadata) = std::fs::metadata(&exe_path) {
                            if metadata.permissions().mode() & 0o111 != 0 {
                                return true;
                            }
                        }
                    }

                    #[cfg(not(unix))]
                    return true;
                }
            }
        }
        false
    }

    /// Check if a path exists
    fn path_exists(&self, path: &str) -> bool {
        Path::new(path).exists()
    }

    /// Tokenize input for highlighting
    ///
    /// Returns (token, is_command, is_quoted, is_operator, is_comment)
    fn tokenize(&self, input: &str) -> Vec<(String, TokenType)> {
        let mut tokens = Vec::new();
        let mut current_token = String::new();
        let mut in_single_quote = false;
        let mut in_double_quote = false;
        let mut is_first_word = true;
        let mut chars = input.chars().peekable();

        while let Some(ch) = chars.next() {
            match ch {
                // Comment
                '#' if !in_single_quote && !in_double_quote && current_token.is_empty() => {
                    // Rest of line is comment
                    let mut comment = String::from("#");
                    comment.extend(chars.by_ref());
                    tokens.push((comment, TokenType::Comment));
                    break;
                }

                // Single quote
                '\'' if !in_double_quote => {
                    if in_single_quote {
                        current_token.push(ch);
                        tokens.push((current_token.clone(), TokenType::String));
                        current_token.clear();
                        in_single_quote = false;
                        is_first_word = false;
                    } else {
                        if !current_token.is_empty() {
                            tokens.push((
                                current_token.clone(),
                                if is_first_word {
                                    TokenType::Command
                                } else {
                                    TokenType::Argument
                                },
                            ));
                            current_token.clear();
                        }
                        current_token.push(ch);
                        in_single_quote = true;
                    }
                }

                // Double quote
                '"' if !in_single_quote => {
                    if in_double_quote {
                        current_token.push(ch);
                        tokens.push((current_token.clone(), TokenType::String));
                        current_token.clear();
                        in_double_quote = false;
                        is_first_word = false;
                    } else {
                        if !current_token.is_empty() {
                            tokens.push((
                                current_token.clone(),
                                if is_first_word {
                                    TokenType::Command
                                } else {
                                    TokenType::Argument
                                },
                            ));
                            current_token.clear();
                        }
                        current_token.push(ch);
                        in_double_quote = true;
                    }
                }

                // Operators and redirections
                '|' | '>' | '<' | '&' | ';' if !in_single_quote && !in_double_quote => {
                    if !current_token.is_empty() {
                        tokens.push((
                            current_token.clone(),
                            if is_first_word {
                                TokenType::Command
                            } else {
                                TokenType::Argument
                            },
                        ));
                        current_token.clear();
                    }

                    // Check for multi-character operators
                    let mut op = String::from(ch);
                    if let Some(&next_ch) = chars.peek() {
                        if (ch == '>' || ch == '<' || ch == '&' || ch == '|') && next_ch == ch {
                            chars.next();
                            op.push(next_ch);
                        } else if ch == '>' && next_ch == '&' {
                            chars.next();
                            op.push(next_ch);
                        } else if ch == '<' && next_ch == '(' {
                            // Process substitution
                            chars.next();
                            op.push(next_ch);
                        }
                    }

                    tokens.push((op, TokenType::Operator));
                    is_first_word = true; // Next word after | or ; is a command
                }

                // Whitespace
                ' ' | '\t' if !in_single_quote && !in_double_quote => {
                    if !current_token.is_empty() {
                        tokens.push((
                            current_token.clone(),
                            if is_first_word {
                                TokenType::Command
                            } else {
                                TokenType::Argument
                            },
                        ));
                        current_token.clear();
                        is_first_word = false;
                    }
                }

                // Regular character
                _ => {
                    current_token.push(ch);
                }
            }
        }

        // Push remaining token
        if !current_token.is_empty() {
            let token_type = if in_single_quote || in_double_quote {
                TokenType::UnclosedString
            } else if is_first_word {
                TokenType::Command
            } else {
                TokenType::Argument
            };
            tokens.push((current_token, token_type));
        }

        tokens
    }

    /// Apply colors to a token based on its type
    fn colorize_token(&self, token: &str, token_type: TokenType) -> (String, Style) {
        match token_type {
            TokenType::Command => {
                if self.is_builtin(token) {
                    (token.to_string(), Style::new().fg(Color::Green).bold())
                } else if self.is_external_command(token) {
                    (token.to_string(), Style::new().fg(Color::Blue))
                } else {
                    // Unknown command - red
                    (token.to_string(), Style::new().fg(Color::Red))
                }
            }

            TokenType::Argument => {
                // Check if it's a path
                if token.starts_with('/') || token.starts_with('.') || token.starts_with('~') {
                    if self.path_exists(token) {
                        (token.to_string(), Style::new().fg(Color::Cyan))
                    } else {
                        (token.to_string(), Style::new().fg(Color::Yellow))
                    }
                } else {
                    // Regular argument - default color
                    (token.to_string(), Style::new())
                }
            }

            TokenType::String | TokenType::UnclosedString => {
                let style = if matches!(token_type, TokenType::UnclosedString) {
                    Style::new().fg(Color::Red) // Unclosed string = error
                } else {
                    Style::new().fg(Color::Magenta)
                };
                (token.to_string(), style)
            }

            TokenType::Operator => {
                (token.to_string(), Style::new().fg(Color::White).bold())
            }

            TokenType::Comment => {
                (token.to_string(), Style::new().fg(Color::DarkGray))
            }
        }
    }
}

/// Token types for syntax highlighting
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum TokenType {
    /// Command (first word in statement)
    Command,
    /// Argument (non-command word)
    Argument,
    /// Quoted string
    String,
    /// Unclosed string (syntax error)
    UnclosedString,
    /// Operator (|, >, <, &, ;, etc.)
    Operator,
    /// Comment (# ...)
    Comment,
}

impl Highlighter for VshHighlighter {
    fn highlight(&self, line: &str, _cursor: usize) -> StyledText {
        let mut styled = StyledText::new();

        if line.is_empty() {
            return styled;
        }

        let tokens = self.tokenize(line);
        let mut position = 0;

        for (token, token_type) in tokens {
            // Find token position in original line (accounting for whitespace)
            if let Some(token_pos) = line[position..].find(&token) {
                // Add any whitespace before token as unstyled
                if token_pos > 0 {
                    styled.push((Style::new(), line[position..position + token_pos].to_string()));
                    position += token_pos;
                }
            }

            // Add styled token
            let (text, style) = self.colorize_token(&token, token_type);
            styled.push((style, text));
            position += token.len();
        }

        // Add any remaining characters (trailing whitespace)
        if position < line.len() {
            styled.push((Style::new(), line[position..].to_string()));
        }

        styled
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_tokenize_simple_command() {
        let highlighter = VshHighlighter::new();
        let tokens = highlighter.tokenize("ls -la /tmp");

        assert_eq!(tokens.len(), 3);
        assert_eq!(tokens[0].0, "ls");
        assert_eq!(tokens[0].1, TokenType::Command);
        assert_eq!(tokens[1].0, "-la");
        assert_eq!(tokens[1].1, TokenType::Argument);
        assert_eq!(tokens[2].0, "/tmp");
        assert_eq!(tokens[2].1, TokenType::Argument);
    }

    #[test]
    fn test_tokenize_with_quotes() {
        let highlighter = VshHighlighter::new();
        let tokens = highlighter.tokenize("echo 'hello world' \"test\"");

        assert_eq!(tokens.len(), 3);
        assert_eq!(tokens[0].0, "echo");
        assert_eq!(tokens[1].0, "'hello world'");
        assert_eq!(tokens[1].1, TokenType::String);
        assert_eq!(tokens[2].0, "\"test\"");
        assert_eq!(tokens[2].1, TokenType::String);
    }

    #[test]
    fn test_tokenize_pipeline() {
        let highlighter = VshHighlighter::new();
        let tokens = highlighter.tokenize("cat file.txt | grep test");

        assert_eq!(tokens[0].0, "cat");
        assert_eq!(tokens[0].1, TokenType::Command);
        assert_eq!(tokens[2].0, "|");
        assert_eq!(tokens[2].1, TokenType::Operator);
        assert_eq!(tokens[3].0, "grep");
        assert_eq!(tokens[3].1, TokenType::Command); // After |, it's a command
    }

    #[test]
    fn test_tokenize_comment() {
        let highlighter = VshHighlighter::new();
        let tokens = highlighter.tokenize("ls # this is a comment");

        assert_eq!(tokens[0].0, "ls");
        assert_eq!(tokens[1].0, "# this is a comment");
        assert_eq!(tokens[1].1, TokenType::Comment);
    }

    #[test]
    fn test_tokenize_unclosed_string() {
        let highlighter = VshHighlighter::new();
        let tokens = highlighter.tokenize("echo 'unclosed");

        assert_eq!(tokens[1].1, TokenType::UnclosedString);
    }

    #[test]
    fn test_is_builtin() {
        let highlighter = VshHighlighter::new();
        assert!(highlighter.is_builtin("ls"));
        assert!(highlighter.is_builtin("cd"));
        assert!(highlighter.is_builtin("undo"));
        assert!(!highlighter.is_builtin("nonexistent"));
    }
}
