// SPDX-License-Identifier: PMPL-1.0-or-later
//! Command Parser
//!
//! Parses shell input into structured commands.
//! Distinguishes between built-in commands and external programs.
//! Supports I/O redirections (>, <, >>, 2>, etc.)

use anyhow::{anyhow, Result};

use crate::redirection::Redirection;

/// Token from lexical analysis
#[derive(Debug, Clone, PartialEq)]
enum Token {
    /// Regular word (command, argument, filename)
    Word(String),

    /// Output redirection operator: >
    OutputRedirect,

    /// Append redirection operator: >>
    AppendRedirect,

    /// Input redirection operator: <
    InputRedirect,

    /// Error output redirection operator: 2>
    ErrorRedirect,

    /// Error append redirection operator: 2>>
    ErrorAppendRedirect,

    /// Error to output redirection: 2>&1
    ErrorToOutput,

    /// Both output redirection (bash extension): &>
    BothRedirect,

    /// Pipeline operator: |
    Pipe,
}

/// Parsed command with arguments and redirections.
///
/// Represents all built-in and external commands that can be executed.
/// Built-in commands are variants of this enum; external commands use
/// [`Command::External`].
///
/// # Examples
/// ```
/// use vsh::parser::{parse_command, Command};
///
/// let cmd = parse_command("mkdir test")?;
/// match cmd {
///     Command::Mkdir { path, .. } => assert_eq!(path, "test"),
///     _ => panic!("Wrong command"),
/// }
/// # Ok::<(), anyhow::Error>(())
/// ```
#[derive(Debug, PartialEq)]
pub enum Command {
    // Built-ins (existing)
    Mkdir {
        path: String,
        redirects: Vec<Redirection>,
    },
    Rmdir {
        path: String,
        redirects: Vec<Redirection>,
    },
    Touch {
        path: String,
        redirects: Vec<Redirection>,
    },
    Rm {
        path: String,
        redirects: Vec<Redirection>,
    },
    Undo {
        count: usize,
    },
    Redo {
        count: usize,
    },
    History {
        count: usize,
        show_proofs: bool,
    },
    Exit,
    Quit,

    // Transactions
    Begin {
        name: String,
    },
    Commit,
    Rollback,

    // Display commands
    Graph,
    Proofs,
    Ls {
        path: Option<String>,
        redirects: Vec<Redirection>,
    },
    Pwd {
        redirects: Vec<Redirection>,
    },
    Cd {
        path: Option<String>,
    },

    // External command
    External {
        program: String,
        args: Vec<String>,
        redirects: Vec<Redirection>,
    },

    /// Pipeline of external commands (cmd1 | cmd2 | cmd3)
    ///
    /// Each stage is a (program, args) pair. Intermediate stages use piped stdio.
    /// Final redirections apply to the last stage only.
    Pipeline {
        stages: Vec<(String, Vec<String>)>,
        redirects: Vec<Redirection>,
    },
}

/// Tokenize input string into words and redirection operators
///
/// Handles:
/// - >> before > (longest match first)
/// - 2>> before 2>
/// - 2>&1 as single token
/// - &> as single token
fn tokenize(input: &str) -> Vec<Token> {
    let mut tokens = Vec::new();
    let mut chars = input.chars().peekable();
    let mut current_word = String::new();

    while let Some(ch) = chars.next() {
        match ch {
            // Whitespace: end current word
            ' ' | '\t' => {
                if !current_word.is_empty() {
                    tokens.push(Token::Word(current_word.clone()));
                    current_word.clear();
                }
            }

            // Redirection operators
            '>' => {
                // End current word
                if !current_word.is_empty() {
                    tokens.push(Token::Word(current_word.clone()));
                    current_word.clear();
                }

                // Check for >>
                if chars.peek() == Some(&'>') {
                    chars.next(); // consume second >
                    tokens.push(Token::AppendRedirect);
                } else {
                    tokens.push(Token::OutputRedirect);
                }
            }

            '<' => {
                // End current word
                if !current_word.is_empty() {
                    tokens.push(Token::Word(current_word.clone()));
                    current_word.clear();
                }

                tokens.push(Token::InputRedirect);
            }

            '2' => {
                // Check if this is start of 2> or 2>&1
                if chars.peek() == Some(&'>') {
                    // End current word if not empty
                    if !current_word.is_empty() {
                        tokens.push(Token::Word(current_word.clone()));
                        current_word.clear();
                    }

                    chars.next(); // consume >

                    // Check for 2>> or 2>&1
                    match chars.peek() {
                        Some(&'>') => {
                            chars.next();
                            tokens.push(Token::ErrorAppendRedirect);
                        }
                        Some(&'&') => {
                            chars.next();
                            if chars.peek() == Some(&'1') {
                                chars.next();
                                tokens.push(Token::ErrorToOutput);
                            } else {
                                // Invalid: 2>&[not 1]
                                // Put back as word
                                current_word.push_str("2>&");
                            }
                        }
                        _ => {
                            tokens.push(Token::ErrorRedirect);
                        }
                    }
                } else {
                    // Regular '2' character, part of word
                    current_word.push(ch);
                }
            }

            '&' => {
                // Check for &>
                if chars.peek() == Some(&'>') {
                    // End current word
                    if !current_word.is_empty() {
                        tokens.push(Token::Word(current_word.clone()));
                        current_word.clear();
                    }

                    chars.next(); // consume >
                    tokens.push(Token::BothRedirect);
                } else {
                    // Regular & (background job - not implemented yet)
                    current_word.push(ch);
                }
            }

            '|' => {
                // End current word
                if !current_word.is_empty() {
                    tokens.push(Token::Word(current_word.clone()));
                    current_word.clear();
                }

                tokens.push(Token::Pipe);
            }

            // Regular character
            _ => {
                current_word.push(ch);
            }
        }
    }

    // Add final word if any
    if !current_word.is_empty() {
        tokens.push(Token::Word(current_word));
    }

    tokens
}

/// Parse a command line into a structured [`Command`] with redirections.
///
/// Tokenizes the input, identifies built-in commands vs external programs,
/// and extracts I/O redirections.
///
/// # Arguments
/// * `input` - Raw command line string (e.g., "ls -la > output.txt")
///
/// # Returns
/// Parsed [`Command`] ready for execution
///
/// # Errors
/// Returns error if:
/// - Invalid redirection syntax
/// - Missing redirection target
/// - Malformed command
///
/// # Examples
/// ```
/// use vsh::parser::parse_command;
///
/// let cmd = parse_command("mkdir project > log.txt")?;
/// // Creates Mkdir command with Output redirection
/// # Ok::<(), anyhow::Error>(())
/// ```
pub fn parse_command(input: &str) -> Result<Command> {
    // Tokenize input
    let tokens = tokenize(input);

    if tokens.is_empty() {
        return Err(anyhow!("Empty command"));
    }

    // Separate command tokens from redirections
    let mut command_tokens = Vec::new();
    let mut redirects = Vec::new();

    let mut i = 0;
    while i < tokens.len() {
        match &tokens[i] {
            Token::Word(w) => {
                command_tokens.push(w.clone());
                i += 1;
            }

            Token::OutputRedirect => {
                let file = expect_word(&tokens, i + 1, "output redirection")?;
                redirects.push(Redirection::Output { file });
                i += 2;
            }

            Token::AppendRedirect => {
                let file = expect_word(&tokens, i + 1, "append redirection")?;
                redirects.push(Redirection::Append { file });
                i += 2;
            }

            Token::InputRedirect => {
                let file = expect_word(&tokens, i + 1, "input redirection")?;
                redirects.push(Redirection::Input { file });
                i += 2;
            }

            Token::ErrorRedirect => {
                let file = expect_word(&tokens, i + 1, "error redirection")?;
                redirects.push(Redirection::ErrorOutput { file });
                i += 2;
            }

            Token::ErrorAppendRedirect => {
                let file = expect_word(&tokens, i + 1, "error append redirection")?;
                redirects.push(Redirection::ErrorAppend { file });
                i += 2;
            }

            Token::ErrorToOutput => {
                redirects.push(Redirection::ErrorToOutput);
                i += 1;
            }

            Token::BothRedirect => {
                let file = expect_word(&tokens, i + 1, "both redirection")?;
                redirects.push(Redirection::BothOutput { file });
                i += 2;
            }

            Token::Pipe => {
                return Err(anyhow!("Pipelines not yet implemented (Phase 6 M3)"));
            }
        }
    }

    // Must have at least command name
    if command_tokens.is_empty() {
        return Err(anyhow!("Missing command (only redirections found)"));
    }

    // Parse command from tokens
    let cmd = command_tokens[0].as_str();
    let args: Vec<String> = command_tokens[1..].to_vec();

    // Parse base command with redirections
    parse_base_command(cmd, args, redirects)
}

/// Extract word token at index or return error
fn expect_word(tokens: &[Token], index: usize, context: &str) -> Result<String> {
    match tokens.get(index) {
        Some(Token::Word(w)) => Ok(w.clone()),
        Some(_) => Err(anyhow!("{}: expected filename, got redirection operator", context)),
        None => Err(anyhow!("{}: missing filename", context)),
    }
}

/// Parse base command with arguments and redirections
fn parse_base_command(cmd: &str, args: Vec<String>, redirects: Vec<Redirection>) -> Result<Command> {
    match cmd {
        "mkdir" => {
            if args.is_empty() {
                return Err(anyhow!("mkdir: missing operand"));
            }
            Ok(Command::Mkdir {
                path: args[0].clone(),
                redirects,
            })
        }
        "rmdir" => {
            if args.is_empty() {
                return Err(anyhow!("rmdir: missing operand"));
            }
            Ok(Command::Rmdir {
                path: args[0].clone(),
                redirects,
            })
        }
        "touch" => {
            if args.is_empty() {
                return Err(anyhow!("touch: missing operand"));
            }
            Ok(Command::Touch {
                path: args[0].clone(),
                redirects,
            })
        }
        "rm" => {
            if args.is_empty() {
                return Err(anyhow!("rm: missing operand"));
            }
            Ok(Command::Rm {
                path: args[0].clone(),
                redirects,
            })
        }
        "undo" => {
            let count = args.get(0).and_then(|s| s.parse().ok()).unwrap_or(1);
            Ok(Command::Undo { count })
        }
        "redo" => {
            let count = args.get(0).and_then(|s| s.parse().ok()).unwrap_or(1);
            Ok(Command::Redo { count })
        }
        "history" => {
            let show_proofs = args.contains(&"--proofs".to_string())
                || args.contains(&"-p".to_string());
            let count = args
                .iter()
                .filter(|s| !s.starts_with('-'))
                .find_map(|s| s.parse().ok())
                .unwrap_or(10);
            Ok(Command::History { count, show_proofs })
        }
        "exit" => Ok(Command::Exit),
        "quit" => Ok(Command::Quit),

        // Transactions
        "begin" => {
            if args.is_empty() {
                return Err(anyhow!("begin: missing transaction name"));
            }
            Ok(Command::Begin {
                name: args[0].clone(),
            })
        }
        "commit" => Ok(Command::Commit),
        "rollback" => Ok(Command::Rollback),

        // Display commands
        "graph" => Ok(Command::Graph),
        "proofs" | "proof" => Ok(Command::Proofs),
        "ls" => Ok(Command::Ls {
            path: args.get(0).map(|s| s.to_string()),
            redirects,
        }),
        "pwd" => Ok(Command::Pwd { redirects }),
        "cd" => {
            // cd doesn't support redirections (it's a state change, not output)
            if !redirects.is_empty() {
                return Err(anyhow!("cd: redirections not supported for this command"));
            }
            Ok(Command::Cd {
                path: args.get(0).map(|s| s.to_string()),
            })
        }

        // Everything else: external command
        _ => Ok(Command::External {
            program: cmd.to_string(),
            args,
            redirects,
        }),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_mkdir() {
        let cmd = parse_command("mkdir foo").unwrap();
        assert_eq!(
            cmd,
            Command::Mkdir {
                path: "foo".to_string(),
                redirects: vec![],
            }
        );
    }

    #[test]
    fn test_parse_external() {
        let cmd = parse_command("echo hello world").unwrap();
        match cmd {
            Command::External {
                program,
                args,
                redirects,
            } => {
                assert_eq!(program, "echo");
                assert_eq!(args, vec!["hello", "world"]);
                assert_eq!(redirects, vec![]);
            }
            _ => panic!("Expected External command"),
        }
    }

    #[test]
    fn test_parse_undo() {
        let cmd = parse_command("undo 3").unwrap();
        assert_eq!(cmd, Command::Undo { count: 3 });
    }

    #[test]
    fn test_parse_history() {
        let cmd = parse_command("history 20 --proofs").unwrap();
        assert_eq!(cmd, Command::History {
            count: 20,
            show_proofs: true
        });
    }

    #[test]
    fn test_parse_begin() {
        let cmd = parse_command("begin mytxn").unwrap();
        assert_eq!(cmd, Command::Begin {
            name: "mytxn".to_string()
        });
    }

    #[test]
    fn test_parse_ls() {
        let cmd = parse_command("ls /tmp").unwrap();
        match cmd {
            Command::Ls { path, redirects } => {
                assert_eq!(path, Some("/tmp".to_string()));
                assert_eq!(redirects, vec![]);
            }
            _ => panic!("Expected Ls command"),
        }
    }

    #[test]
    fn test_parse_cd() {
        let cmd = parse_command("cd /home").unwrap();
        match cmd {
            Command::Cd { path } => {
                assert_eq!(path, Some("/home".to_string()));
            }
            _ => panic!("Expected Cd command"),
        }
    }

    #[test]
    fn test_parse_cd_no_args() {
        let cmd = parse_command("cd").unwrap();
        match cmd {
            Command::Cd { path } => {
                assert_eq!(path, None);
            }
            _ => panic!("Expected Cd command"),
        }
    }

    #[test]
    fn test_parse_cd_dash() {
        let cmd = parse_command("cd -").unwrap();
        match cmd {
            Command::Cd { path } => {
                assert_eq!(path, Some("-".to_string()));
            }
            _ => panic!("Expected Cd command"),
        }
    }

    // Redirection parsing tests
    #[test]
    fn test_parse_output_redirect() {
        let cmd = parse_command("ls > output.txt").unwrap();
        match cmd {
            Command::Ls { redirects, .. } => {
                assert_eq!(redirects.len(), 1);
                assert_eq!(
                    redirects[0],
                    Redirection::Output {
                        file: "output.txt".to_string()
                    }
                );
            }
            _ => panic!("Expected Ls command"),
        }
    }

    #[test]
    fn test_parse_append_redirect() {
        let cmd = parse_command("echo test >> log.txt").unwrap();
        match cmd {
            Command::External { redirects, .. } => {
                assert_eq!(redirects.len(), 1);
                assert_eq!(
                    redirects[0],
                    Redirection::Append {
                        file: "log.txt".to_string()
                    }
                );
            }
            _ => panic!("Expected External command"),
        }
    }

    #[test]
    fn test_parse_input_redirect() {
        let cmd = parse_command("cat < input.txt").unwrap();
        match cmd {
            Command::External { redirects, .. } => {
                assert_eq!(redirects.len(), 1);
                assert_eq!(
                    redirects[0],
                    Redirection::Input {
                        file: "input.txt".to_string()
                    }
                );
            }
            _ => panic!("Expected External command"),
        }
    }

    #[test]
    fn test_parse_error_redirect() {
        let cmd = parse_command("make 2> errors.log").unwrap();
        match cmd {
            Command::External { redirects, .. } => {
                assert_eq!(redirects.len(), 1);
                assert_eq!(
                    redirects[0],
                    Redirection::ErrorOutput {
                        file: "errors.log".to_string()
                    }
                );
            }
            _ => panic!("Expected External command"),
        }
    }

    #[test]
    fn test_parse_error_to_output() {
        let cmd = parse_command("make 2>&1").unwrap();
        match cmd {
            Command::External { redirects, .. } => {
                assert_eq!(redirects.len(), 1);
                assert_eq!(redirects[0], Redirection::ErrorToOutput);
            }
            _ => panic!("Expected External command"),
        }
    }

    #[test]
    fn test_parse_multiple_redirects() {
        let cmd = parse_command("cat < in.txt > out.txt 2> err.log").unwrap();
        match cmd {
            Command::External { redirects, .. } => {
                assert_eq!(redirects.len(), 3);
                assert_eq!(
                    redirects[0],
                    Redirection::Input {
                        file: "in.txt".to_string()
                    }
                );
                assert_eq!(
                    redirects[1],
                    Redirection::Output {
                        file: "out.txt".to_string()
                    }
                );
                assert_eq!(
                    redirects[2],
                    Redirection::ErrorOutput {
                        file: "err.log".to_string()
                    }
                );
            }
            _ => panic!("Expected External command"),
        }
    }

    #[test]
    fn test_parse_both_redirect() {
        let cmd = parse_command("make &> output.log").unwrap();
        match cmd {
            Command::External { redirects, .. } => {
                assert_eq!(redirects.len(), 1);
                assert_eq!(
                    redirects[0],
                    Redirection::BothOutput {
                        file: "output.log".to_string()
                    }
                );
            }
            _ => panic!("Expected External command"),
        }
    }

    #[test]
    fn test_tokenize_basic() {
        let tokens = tokenize("echo hello");
        assert_eq!(tokens.len(), 2);
        assert_eq!(tokens[0], Token::Word("echo".to_string()));
        assert_eq!(tokens[1], Token::Word("hello".to_string()));
    }

    #[test]
    fn test_tokenize_output_redirect() {
        let tokens = tokenize("ls > file.txt");
        assert_eq!(tokens.len(), 3);
        assert_eq!(tokens[0], Token::Word("ls".to_string()));
        assert_eq!(tokens[1], Token::OutputRedirect);
        assert_eq!(tokens[2], Token::Word("file.txt".to_string()));
    }

    #[test]
    fn test_tokenize_append_redirect() {
        let tokens = tokenize("echo test >> file.txt");
        assert_eq!(tokens.len(), 4);
        assert_eq!(tokens[1], Token::Word("test".to_string()));
        assert_eq!(tokens[2], Token::AppendRedirect);
    }

    #[test]
    fn test_tokenize_error_redirect() {
        let tokens = tokenize("make 2> err.log");
        assert_eq!(tokens[1], Token::ErrorRedirect);
    }

    #[test]
    fn test_tokenize_error_to_output() {
        let tokens = tokenize("make 2>&1");
        assert_eq!(tokens.len(), 2);
        assert_eq!(tokens[1], Token::ErrorToOutput);
    }

    #[test]
    fn test_tokenize_pipe() {
        let tokens = tokenize("ls | grep test");
        assert_eq!(tokens.len(), 4);
        assert_eq!(tokens[0], Token::Word("ls".to_string()));
        assert_eq!(tokens[1], Token::Pipe);
        assert_eq!(tokens[2], Token::Word("grep".to_string()));
        assert_eq!(tokens[3], Token::Word("test".to_string()));
    }

    #[test]
    fn test_tokenize_multi_pipe() {
        let tokens = tokenize("cat file.txt | grep foo | wc -l");
        assert_eq!(tokens.len(), 8);
        assert_eq!(tokens[0], Token::Word("cat".to_string()));
        assert_eq!(tokens[1], Token::Word("file.txt".to_string()));
        assert_eq!(tokens[2], Token::Pipe);
        assert_eq!(tokens[3], Token::Word("grep".to_string()));
        assert_eq!(tokens[4], Token::Word("foo".to_string()));
        assert_eq!(tokens[5], Token::Pipe);
        assert_eq!(tokens[6], Token::Word("wc".to_string()));
        assert_eq!(tokens[7], Token::Word("-l".to_string()));
    }

    #[test]
    fn test_tokenize_pipe_with_redirect() {
        let tokens = tokenize("ls | grep test > output.txt");
        assert_eq!(tokens.len(), 6);
        assert_eq!(tokens[1], Token::Pipe);
        assert_eq!(tokens[4], Token::OutputRedirect);
        assert_eq!(tokens[5], Token::Word("output.txt".to_string()));
    }

    #[test]
    fn test_parse_empty() {
        assert!(parse_command("").is_err());
        assert!(parse_command("   ").is_err());
    }
}
