// SPDX-License-Identifier: PLMP-1.0-or-later
//! Executable Command Trait
//!
//! Decouples command parsing from execution, creating a clean seam
//! between Layer 1 (Implementation) and Layer 2 (Parser).

use anyhow::Result;

use crate::parser::Command;
use crate::proof_refs::ProofReference;
use crate::state::ShellState;
use crate::{commands, external};

/// Trait for executable commands
///
/// Separates concerns:
/// - Parser creates Command enum
/// - Command trait handles execution
/// - REPL just calls execute()
pub trait ExecutableCommand {
    /// Execute the command, potentially modifying shell state
    fn execute(&self, state: &mut ShellState) -> Result<ExecutionResult>;

    /// Check if this command is reversible (creates undo entry)
    #[allow(dead_code)]
    fn is_reversible(&self) -> bool;

    /// Get the proof reference for this command (if any)
    #[allow(dead_code)]
    fn proof_reference(&self) -> Option<ProofReference>;

    /// Get command description for display
    #[allow(dead_code)]
    fn description(&self) -> String;
}

/// Result of command execution
#[derive(Debug)]
pub enum ExecutionResult {
    /// Command completed successfully
    Success,

    /// Command requests shell exit
    Exit,

    /// External command executed with exit code
    ExternalCommand { exit_code: i32 },
}

impl ExecutableCommand for Command {
    fn execute(&self, state: &mut ShellState) -> Result<ExecutionResult> {
        match self {
            // Filesystem operations (reversible)
            Command::Mkdir { path, redirects: _ } => {
                // TODO: Handle redirections in Phase 6 M2
                commands::mkdir(state, path, false)?;
                Ok(ExecutionResult::Success)
            }

            Command::Rmdir { path, redirects: _ } => {
                commands::rmdir(state, path, false)?;
                Ok(ExecutionResult::Success)
            }

            Command::Touch { path, redirects: _ } => {
                commands::touch(state, path, false)?;
                Ok(ExecutionResult::Success)
            }

            Command::Rm { path, redirects: _ } => {
                commands::rm(state, path, false)?;
                Ok(ExecutionResult::Success)
            }

            // Undo/redo operations
            Command::Undo { count } => {
                commands::undo(state, *count, false)?;
                Ok(ExecutionResult::Success)
            }

            Command::Redo { count } => {
                commands::redo(state, *count, false)?;
                Ok(ExecutionResult::Success)
            }

            Command::History { count, show_proofs } => {
                commands::history(state, *count, *show_proofs)?;
                Ok(ExecutionResult::Success)
            }

            // Transactions
            Command::Begin { name } => {
                commands::begin_transaction(state, name)?;
                Ok(ExecutionResult::Success)
            }

            Command::Commit => {
                commands::commit_transaction(state)?;
                Ok(ExecutionResult::Success)
            }

            Command::Rollback => {
                commands::rollback_transaction(state)?;
                Ok(ExecutionResult::Success)
            }

            // Display commands
            Command::Graph => {
                commands::show_graph(state)?;
                Ok(ExecutionResult::Success)
            }

            Command::Proofs => {
                commands::show_proofs()?;
                Ok(ExecutionResult::Success)
            }

            // Exit commands
            Command::Exit | Command::Quit => Ok(ExecutionResult::Exit),

            // Navigation (built-ins but not reversible)
            Command::Ls { path, redirects: _ } => {
                // TODO: Handle redirections in Phase 6 M2
                use std::fs;

                let target = if let Some(p) = path {
                    state.resolve_path(p)
                } else {
                    state.root.clone()
                };

                if !target.is_dir() {
                    anyhow::bail!("Not a directory");
                }

                for entry in fs::read_dir(&target)? {
                    let entry = entry?;
                    let name = entry.file_name();
                    let file_type = entry.file_type()?;
                    if file_type.is_dir() {
                        use colored::Colorize;
                        println!("{}/", name.to_string_lossy().bright_blue());
                    } else {
                        println!("{}", name.to_string_lossy());
                    }
                }
                Ok(ExecutionResult::Success)
            }

            Command::Pwd { redirects: _ } => {
                // TODO: Handle redirections in Phase 6 M2
                println!("{}", state.root.display());
                Ok(ExecutionResult::Success)
            }

            Command::Cd { path } => {
                use std::path::PathBuf;

                let target = if let Some(p) = path {
                    if p == "-" {
                        // cd - : swap to previous directory
                        match &state.previous_dir {
                            Some(prev) => {
                                // Print the directory we're switching to (bash behavior)
                                println!("{}", prev.display());
                                prev.clone()
                            }
                            None => {
                                anyhow::bail!("cd: OLDPWD not set");
                            }
                        }
                    } else if p.starts_with('/') {
                        // Absolute path
                        PathBuf::from(p)
                    } else if p.starts_with("~/") {
                        // Home-relative path
                        let home = dirs::home_dir()
                            .ok_or_else(|| anyhow::anyhow!("Could not find home directory"))?;
                        home.join(&p[2..])
                    } else {
                        // Relative to current directory
                        state.root.join(p)
                    }
                } else {
                    // cd with no args goes to home
                    dirs::home_dir()
                        .ok_or_else(|| anyhow::anyhow!("Could not find home directory"))?
                };

                if !target.exists() {
                    anyhow::bail!("cd: {}: No such file or directory", target.display());
                }

                if !target.is_dir() {
                    anyhow::bail!("cd: {}: Not a directory", target.display());
                }

                // Store current directory as previous before changing
                state.previous_dir = Some(state.root.clone());

                // Change the shell's working directory
                std::env::set_current_dir(&target)?;

                // Update state root to track current directory
                state.root = std::fs::canonicalize(target)?;

                Ok(ExecutionResult::Success)
            }

            // External commands (not reversible)
            Command::External {
                program,
                args,
                redirects: _,
            } => {
                // TODO: Handle redirections in Phase 6 M2
                match external::execute_external(program, args) {
                    Ok(exit_code) => Ok(ExecutionResult::ExternalCommand { exit_code }),
                    Err(e) => {
                        eprintln!("{}: {}", program, e);
                        Ok(ExecutionResult::ExternalCommand { exit_code: 127 })
                    }
                }
            }
        }
    }

    fn is_reversible(&self) -> bool {
        matches!(
            self,
            Command::Mkdir { .. }
                | Command::Rmdir { .. }
                | Command::Touch { .. }
                | Command::Rm { .. }
        )
    }

    fn proof_reference(&self) -> Option<ProofReference> {
        use crate::proof_refs::{MKDIR_RMDIR_REVERSIBLE, CREATE_DELETE_REVERSIBLE};

        match self {
            Command::Mkdir { .. } | Command::Rmdir { .. } => {
                Some(MKDIR_RMDIR_REVERSIBLE)
            }
            Command::Touch { .. } | Command::Rm { .. } => {
                Some(CREATE_DELETE_REVERSIBLE)
            }
            _ => None,
        }
    }

    fn description(&self) -> String {
        match self {
            Command::Mkdir { path, .. } => format!("mkdir {}", path),
            Command::Rmdir { path, .. } => format!("rmdir {}", path),
            Command::Touch { path, .. } => format!("touch {}", path),
            Command::Rm { path, .. } => format!("rm {}", path),
            Command::Undo { count } => format!("undo {}", count),
            Command::Redo { count } => format!("redo {}", count),
            Command::History { count, show_proofs } => {
                if *show_proofs {
                    format!("history {} --proofs", count)
                } else {
                    format!("history {}", count)
                }
            }
            Command::Exit => "exit".to_string(),
            Command::Quit => "quit".to_string(),
            Command::Begin { name } => format!("begin {}", name),
            Command::Commit => "commit".to_string(),
            Command::Rollback => "rollback".to_string(),
            Command::Graph => "graph".to_string(),
            Command::Proofs => "proofs".to_string(),
            Command::Ls { path, .. } => {
                if let Some(p) = path {
                    format!("ls {}", p)
                } else {
                    "ls".to_string()
                }
            }
            Command::Pwd { .. } => "pwd".to_string(),
            Command::Cd { path } => {
                if let Some(p) = path {
                    format!("cd {}", p)
                } else {
                    "cd".to_string()
                }
            }
            Command::External { program, args, .. } => {
                if args.is_empty() {
                    program.clone()
                } else {
                    format!("{} {}", program, args.join(" "))
                }
            }
        }
    }
}
