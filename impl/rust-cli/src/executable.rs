// SPDX-License-Identifier: PLMP-1.0-or-later
//! Executable Command Trait
//!
//! Decouples command parsing from execution, creating a clean seam
//! between Layer 1 (Implementation) and Layer 2 (Parser).

use anyhow::Result;

use crate::parser::Command;
use crate::proof_refs::ProofReference;
use crate::redirection;
use crate::state::ShellState;
use crate::{commands, external};

/// Trait for executable commands with proof references.
///
/// Separates concerns between parsing and execution:
/// - Parser creates [`Command`] enum from user input
/// - This trait handles command execution logic
/// - REPL just calls [`execute`](ExecutableCommand::execute)
///
/// # Examples
/// ```no_run
/// use vsh::executable::ExecutableCommand;
/// use vsh::parser::Command;
/// use vsh::state::ShellState;
///
/// let mut state = ShellState::new("/tmp/test")?;
/// let cmd = Command::Mkdir { path: "test".to_string(), redirects: vec![] };
/// cmd.execute(&mut state)?;
/// # Ok::<(), anyhow::Error>(())
/// ```
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

/// Result of command execution indicating next REPL action.
///
/// Determines whether the REPL should continue, exit, or handle
/// external command exit codes.
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
            Command::Mkdir { path, redirects } => {
                let expanded_path = crate::parser::expand_variables(path, state);
                if redirects.is_empty() {
                    commands::mkdir(state, &expanded_path, false)?;
                } else {
                    redirection::capture_and_redirect(redirects, state, |s| {
                        commands::mkdir(s, &expanded_path, false)
                    })?;
                }
                Ok(ExecutionResult::Success)
            }

            Command::Rmdir { path, redirects } => {
                let expanded_path = crate::parser::expand_variables(path, state);
                if redirects.is_empty() {
                    commands::rmdir(state, &expanded_path, false)?;
                } else {
                    redirection::capture_and_redirect(redirects, state, |s| {
                        commands::rmdir(s, &expanded_path, false)
                    })?;
                }
                Ok(ExecutionResult::Success)
            }

            Command::Touch { path, redirects } => {
                let expanded_path = crate::parser::expand_variables(path, state);
                if redirects.is_empty() {
                    commands::touch(state, &expanded_path, false)?;
                } else {
                    redirection::capture_and_redirect(redirects, state, |s| {
                        commands::touch(s, &expanded_path, false)
                    })?;
                }
                Ok(ExecutionResult::Success)
            }

            Command::Rm { path, redirects } => {
                let expanded_path = crate::parser::expand_variables(path, state);
                if redirects.is_empty() {
                    commands::rm(state, &expanded_path, false)?;
                } else {
                    redirection::capture_and_redirect(redirects, state, |s| {
                        commands::rm(s, &expanded_path, false)
                    })?;
                }
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
                let expanded_name = crate::parser::expand_variables(name, state);
                commands::begin_transaction(state, &expanded_name)?;
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
            Command::Ls { path, redirects } => {
                // Expand variables in path
                let expanded_path = path.as_ref().map(|p| crate::parser::expand_variables(p, state));

                if redirects.is_empty() {
                    // Direct output to terminal
                    use std::fs;

                    let target = if let Some(ref p) = expanded_path {
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
                } else {
                    // Capture and redirect output
                    redirection::capture_and_redirect(redirects, state, |s| {
                        use std::fs;

                        let target = if let Some(ref p) = expanded_path {
                            s.resolve_path(p)
                        } else {
                            s.root.clone()
                        };

                        if !target.is_dir() {
                            anyhow::bail!("Not a directory");
                        }

                        for entry in fs::read_dir(&target)? {
                            let entry = entry?;
                            let name = entry.file_name();
                            let file_type = entry.file_type()?;
                            if file_type.is_dir() {
                                // No colors when redirecting
                                println!("{}/", name.to_string_lossy());
                            } else {
                                println!("{}", name.to_string_lossy());
                            }
                        }
                        Ok(())
                    })?;
                }
                Ok(ExecutionResult::Success)
            }

            Command::Pwd { redirects } => {
                if redirects.is_empty() {
                    println!("{}", state.root.display());
                } else {
                    redirection::capture_and_redirect(redirects, state, |s| {
                        println!("{}", s.root.display());
                        Ok(())
                    })?;
                }
                Ok(ExecutionResult::Success)
            }

            Command::Cd { path } => {
                use std::path::PathBuf;

                // Expand variables in path first
                let expanded_path = path.as_ref().map(|p| crate::parser::expand_variables(p, state));

                let target = if let Some(ref p) = expanded_path {
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

            // External commands (not reversible by default, but redirections are)
            Command::External {
                program,
                args,
                redirects,
            } => {
                // Expand variables and command substitutions in program name and arguments
                let expanded_program = crate::parser::expand_with_command_sub(program, state)?;
                let expanded_args: Result<Vec<String>> = args
                    .iter()
                    .map(|arg| crate::parser::expand_with_command_sub(arg, state))
                    .collect();
                let expanded_args = expanded_args?;

                let exit_code = if redirects.is_empty() {
                    // No redirections - use simple path
                    external::execute_external(&expanded_program, &expanded_args)
                } else {
                    // Has redirections - use redirection-aware execution
                    external::execute_external_with_redirects(&expanded_program, &expanded_args, redirects, state)
                }
                .unwrap_or_else(|e| {
                    eprintln!("{}: {}", expanded_program, e);
                    127
                });

                Ok(ExecutionResult::ExternalCommand { exit_code })
            }

            // Pipeline commands (not reversible by default, but redirections are)
            Command::Pipeline { stages, redirects } => {
                // Expand variables and command substitutions in all pipeline stages
                let expanded_stages: Result<Vec<(String, Vec<String>)>> = stages
                    .iter()
                    .map(|(program, args)| {
                        let expanded_program = crate::parser::expand_with_command_sub(program, state)?;
                        let expanded_args: Result<Vec<String>> = args
                            .iter()
                            .map(|arg| crate::parser::expand_with_command_sub(arg, state))
                            .collect();
                        Ok((expanded_program, expanded_args?))
                    })
                    .collect();
                let expanded_stages = expanded_stages?;

                let exit_code = external::execute_pipeline(&expanded_stages, redirects, state)
                    .unwrap_or_else(|e| {
                        eprintln!("Pipeline error: {}", e);
                        127
                    });

                Ok(ExecutionResult::ExternalCommand { exit_code })
            }

            // Variable assignment
            Command::Assignment { name, value } => {
                // Expand variables and command substitutions in the value
                let expanded_value = crate::parser::expand_with_command_sub(value, state)?;
                state.set_variable(name, expanded_value);
                Ok(ExecutionResult::Success)
            }

            // Export command
            Command::Export { name, value } => {
                if let Some(val) = value {
                    // export VAR=value
                    // Expand variables and command substitutions in the value
                    let expanded_value = crate::parser::expand_with_command_sub(val, state)?;
                    state.set_variable(name, expanded_value);
                    state.export_variable(name);
                } else {
                    // export VAR (export existing variable)
                    if state.get_variable(name).is_some() {
                        state.export_variable(name);
                    } else {
                        anyhow::bail!("export: {}: variable not set", name);
                    }
                }
                Ok(ExecutionResult::Success)
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
            Command::Pipeline { stages, .. } => {
                let stage_desc: Vec<_> = stages
                    .iter()
                    .map(|(prog, args)| {
                        if args.is_empty() {
                            prog.clone()
                        } else {
                            format!("{} {}", prog, args.join(" "))
                        }
                    })
                    .collect();
                stage_desc.join(" | ")
            }

            Command::Assignment { name, value } => {
                format!("{}={}", name, value)
            }

            Command::Export { name, value } => {
                if let Some(val) = value {
                    format!("export {}={}", name, val)
                } else {
                    format!("export {}", name)
                }
            }
        }
    }
}
