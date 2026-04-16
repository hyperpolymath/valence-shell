// SPDX-License-Identifier: PMPL-1.0-or-later
//! Valence Shell (vsh) - A Formally Verified Reversible Shell
//!
//! This is the user-facing CLI for Valence Shell. It provides:
//! - Interactive shell with command history
//! - Undo/redo for all filesystem operations
//! - Transaction grouping
//! - Proof references for each operation
//! - Shell script execution (`vsh script.sh`, `vsh -c "cmd"`)
//!
//! Architecture:
//! - This Rust binary handles UI and fast-path operations
//! - Complex operations delegate to BEAM daemon
//! - Zig FFI provides the verified POSIX interface
//!
//! Author: Jonathan D.A. Jewell

use anyhow::{Context, Result};
use clap::{Parser, Subcommand};
use colored::Colorize;

// Use library modules
use vsh::{commands, state};
use vsh::executable::{ExecutableCommand, ExecutionResult};

// REPL modules (choose one based on feature flags)
#[cfg(feature = "enhanced-repl")]
use vsh::enhanced_repl as repl_impl;
#[cfg(not(feature = "enhanced-repl"))]
use vsh::repl as repl_impl;

/// Valence Shell - Every operation is reversible
#[derive(Parser)]
#[command(name = "vsh")]
#[command(author = "Hyperpolymath")]
#[command(version = "0.9.0")]
#[command(about = "A formally verified reversible shell", long_about = None)]
struct Cli {
    /// Enable verbose output showing proof references
    #[arg(short, long)]
    verbose: bool,

    /// Path to sandbox root (default: current directory)
    #[arg(short, long)]
    root: Option<String>,

    /// Execute command string and exit (like bash -c)
    #[arg(short = 'c')]
    command_string: Option<String>,

    /// Script file to execute (positional argument)
    #[arg(value_name = "SCRIPT")]
    script: Option<String>,

    /// Arguments passed to the script ($1, $2, etc.)
    #[arg(value_name = "ARGS", trailing_var_arg = true)]
    script_args: Vec<String>,

    /// Subcommand to run (or enter interactive mode if none)
    #[command(subcommand)]
    command: Option<Commands>,
}

#[derive(Subcommand)]
enum Commands {
    /// Create a directory (reversible)
    Mkdir {
        /// Path to create
        path: String,
    },

    /// Remove a directory (reversible)
    Rmdir {
        /// Path to remove
        path: String,
    },

    /// Create an empty file (reversible)
    Touch {
        /// Path to create
        path: String,
    },

    /// Remove a file (reversible)
    Rm {
        /// Path to remove
        path: String,
    },

    /// Undo the last operation
    Undo {
        /// Number of operations to undo (default: 1)
        #[arg(short, long, default_value = "1")]
        count: usize,
    },

    /// Redo the last undone operation
    Redo {
        /// Number of operations to redo (default: 1)
        #[arg(short, long, default_value = "1")]
        count: usize,
    },

    /// Show operation history with proof references
    History {
        /// Show last N operations
        #[arg(short, long, default_value = "10")]
        count: usize,

        /// Show full proof references
        #[arg(short, long)]
        proofs: bool,
    },

    /// Start a transaction group
    Begin {
        /// Transaction name
        name: String,
    },

    /// Commit current transaction
    Commit,

    /// Rollback current transaction
    Rollback,

    /// Show undo graph
    Graph,

    /// Enter interactive shell mode
    Shell,

    /// Show proof status and verification info
    Proofs,
}

fn main() -> Result<()> {
    let cli = Cli::parse();

    // Initialize shell state
    let root = match cli.root {
        Some(r) => r,
        None => {
            let current = std::env::current_dir()
                .context("Failed to get current directory")?;
            current.to_string_lossy().to_string()
        }
    };

    let mut state = state::ShellState::new(&root)?;

    // Mode 1: Execute inline command string (-c "command")
    if let Some(ref cmd_string) = cli.command_string {
        // Set positional parameters: $0 = "vsh", $1.. = script_args
        state.set_positional_params(cli.script_args.clone());
        return execute_script_content(cmd_string, &mut state);
    }

    // Mode 2: Execute a script file (vsh script.sh [args...])
    if let Some(ref script_path) = cli.script {
        // Check for shebang or just execute
        let script_content = std::fs::read_to_string(script_path)
            .context(format!("Cannot read script: {}", script_path))?;

        // Set positional parameters: $0 = script_path, $1.. = script_args
        state.set_positional_params(cli.script_args.clone());

        // Skip shebang line if present
        let content = if script_content.starts_with("#!") {
            // Skip first line (shebang)
            match script_content.find('\n') {
                Some(pos) => &script_content[pos + 1..],
                None => "",
            }
        } else {
            &script_content
        };

        return execute_script_content(content, &mut state);
    }

    // Mode 3: Interactive or subcommand mode

    // Print banner in interactive mode or verbose
    if cli.command.is_none() || cli.verbose {
        print_banner();
    }

    match cli.command {
        Some(Commands::Mkdir { path }) => {
            commands::mkdir(&mut state, &path, cli.verbose)?;
        }
        Some(Commands::Rmdir { path }) => {
            commands::rmdir(&mut state, &path, cli.verbose)?;
        }
        Some(Commands::Touch { path }) => {
            commands::touch(&mut state, &path, cli.verbose)?;
        }
        Some(Commands::Rm { path }) => {
            commands::rm(&mut state, &path, cli.verbose)?;
        }
        Some(Commands::Undo { count }) => {
            commands::undo(&mut state, count, cli.verbose)?;
        }
        Some(Commands::Redo { count }) => {
            commands::redo(&mut state, count, cli.verbose)?;
        }
        Some(Commands::History { count, proofs }) => {
            commands::history(&state, count, proofs)?;
        }
        Some(Commands::Begin { name }) => {
            commands::begin_transaction(&mut state, &name)?;
        }
        Some(Commands::Commit) => {
            commands::commit_transaction(&mut state)?;
        }
        Some(Commands::Rollback) => {
            commands::rollback_transaction(&mut state)?;
        }
        Some(Commands::Graph) => {
            commands::show_graph(&state)?;
        }
        Some(Commands::Shell) | None => {
            // Use enhanced REPL with tab completion and syntax highlighting
            repl_impl::run(&mut state)?;
        }
        Some(Commands::Proofs) => {
            commands::show_proofs()?;
        }
    }

    // Run EXIT trap if registered
    if let Some(exit_cmd) = state.traps.get(vsh::posix_builtins::TrapSignal::Exit).map(|s| s.to_string()) {
        if let Ok(cmd) = vsh::parser::parse_command(&exit_cmd) {
            let _ = cmd.execute(&mut state);
        }
    }

    Ok(())
}

/// Execute script content (string of commands, one per line or semicolon-separated)
fn execute_script_content(content: &str, state: &mut state::ShellState) -> Result<()> {
    for line in content.lines() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }

        // Split on semicolons
        let segments = vsh::parser::split_on_semicolons(line);
        for segment in segments {
            let segment = segment.trim();
            if segment.is_empty() || segment.starts_with('#') {
                continue;
            }

            match vsh::parser::parse_command(segment) {
                Ok(cmd) => {
                    let result = cmd.execute(state)?;
                    match result {
                        ExecutionResult::Exit => return Ok(()),
                        ExecutionResult::ExternalCommand { exit_code }
                        | ExecutionResult::Return { exit_code } => {
                            state.last_exit_code = exit_code;
                        }
                        ExecutionResult::Success => {
                            state.last_exit_code = 0;
                        }
                    }
                }
                Err(e) => {
                    eprintln!("vsh: {}", e);
                    state.last_exit_code = 1;
                }
            }
        }
    }

    // Run EXIT trap if registered
    if let Some(exit_cmd) = state.traps.get(vsh::posix_builtins::TrapSignal::Exit).map(|s| s.to_string()) {
        if let Ok(cmd) = vsh::parser::parse_command(&exit_cmd) {
            let _ = cmd.execute(state);
        }
    }

    std::process::exit(state.last_exit_code);
}

fn print_banner() {
    println!(
        "{}",
        r#"
╔═══════════════════════════════════════════════════════════╗
║  ██╗   ██╗ █████╗ ██╗     ███████╗███╗   ██╗ ██████╗███████╗ ║
║  ██║   ██║██╔══██╗██║     ██╔════╝████╗  ██║██╔════╝██╔════╝ ║
║  ██║   ██║███████║██║     █████╗  ██╔██╗ ██║██║     █████╗   ║
║  ╚██╗ ██╔╝██╔══██║██║     ██╔══╝  ██║╚██╗██║██║     ██╔══╝   ║
║   ╚████╔╝ ██║  ██║███████╗███████╗██║ ╚████║╚██████╗███████╗ ║
║    ╚═══╝  ╚═╝  ╚═╝╚══════╝╚══════╝╚═╝  ╚═══╝ ╚═════╝╚══════╝ ║
║                                                               ║
║  The Thermodynamic Shell - Every operation is reversible     ║
║  Backed by 200+ formal theorems across 6 verification systems ║
╚═══════════════════════════════════════════════════════════╝
"#
        .bright_blue()
    );
    println!(
        "{}",
        "Type 'help' for commands, 'undo' to reverse, 'history --proofs' for proof refs\n"
            .bright_black()
    );
}
