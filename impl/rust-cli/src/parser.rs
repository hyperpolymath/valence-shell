// SPDX-License-Identifier: PMPL-1.0-or-later
//! Command Parser
//!
//! Parses shell input into structured commands.
//! Distinguishes between built-in commands and external programs.

use anyhow::{anyhow, Result};

#[derive(Debug, PartialEq)]
pub enum Command {
    // Built-ins (existing)
    Mkdir { path: String },
    Rmdir { path: String },
    Touch { path: String },
    Rm { path: String },
    Undo { count: usize },
    Redo { count: usize },
    History { count: usize, show_proofs: bool },
    Exit,
    Quit,

    // Transactions
    Begin { name: String },
    Commit,
    Rollback,

    // Display commands
    Graph,
    Proofs,
    Ls { path: Option<String> },
    Pwd,
    Cd { path: Option<String> },

    // NEW: External command
    External {
        program: String,
        args: Vec<String>,
    },
}

/// Parse a command line into a Command
pub fn parse_command(input: &str) -> Result<Command> {
    let parts: Vec<&str> = input.split_whitespace().collect();
    if parts.is_empty() {
        return Err(anyhow!("Empty command"));
    }

    let cmd = parts[0];
    let args: Vec<String> = parts[1..].iter().map(|s| s.to_string()).collect();

    match cmd {
        "mkdir" => {
            if args.is_empty() {
                return Err(anyhow!("mkdir: missing operand"));
            }
            Ok(Command::Mkdir {
                path: args[0].clone(),
            })
        }
        "rmdir" => {
            if args.is_empty() {
                return Err(anyhow!("rmdir: missing operand"));
            }
            Ok(Command::Rmdir {
                path: args[0].clone(),
            })
        }
        "touch" => {
            if args.is_empty() {
                return Err(anyhow!("touch: missing operand"));
            }
            Ok(Command::Touch {
                path: args[0].clone(),
            })
        }
        "rm" => {
            if args.is_empty() {
                return Err(anyhow!("rm: missing operand"));
            }
            Ok(Command::Rm {
                path: args[0].clone(),
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
        }),
        "pwd" => Ok(Command::Pwd),
        "cd" => Ok(Command::Cd {
            path: args.get(0).map(|s| s.to_string()),
        }),

        // Everything else: external command
        _ => Ok(Command::External {
            program: cmd.to_string(),
            args,
        }),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_mkdir() {
        let cmd = parse_command("mkdir foo").unwrap();
        assert_eq!(cmd, Command::Mkdir {
            path: "foo".to_string()
        });
    }

    #[test]
    fn test_parse_external() {
        let cmd = parse_command("echo hello world").unwrap();
        match cmd {
            Command::External { program, args } => {
                assert_eq!(program, "echo");
                assert_eq!(args, vec!["hello", "world"]);
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
            Command::Ls { path } => {
                assert_eq!(path, Some("/tmp".to_string()));
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

    #[test]
    fn test_parse_empty() {
        assert!(parse_command("").is_err());
        assert!(parse_command("   ").is_err());
    }
}
