// SPDX-License-Identifier: PLMP-1.0-or-later
//! Valence Shell (vsh) - A Formally Verified Reversible Shell
//!
//! This is the user-facing CLI for Valence Shell. It provides:
//! - Interactive shell with command history
//! - Undo/redo for all filesystem operations
//! - Transaction grouping
//! - Proof references for each operation
//!
//! Architecture:
//! - This Rust binary handles UI and fast-path operations
//! - Complex operations delegate to BEAM daemon
//! - Zig FFI provides the verified POSIX interface

mod commands;
mod external;
mod history;
mod parser;
mod proof_refs;
mod repl;
mod state;

use anyhow::Result;
use clap::{Parser, Subcommand};
use colored::Colorize;

/// Valence Shell - Every operation is reversible
#[derive(Parser)]
#[command(name = "vsh")]
#[command(author = "Hyperpolymath")]
#[command(version = "0.6.0")]
#[command(about = "A formally verified reversible shell", long_about = None)]
struct Cli {
    /// Enable verbose output showing proof references
    #[arg(short, long)]
    verbose: bool,

    /// Path to sandbox root (default: current directory)
    #[arg(short, long)]
    root: Option<String>,

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
    let root = cli
        .root
        .unwrap_or_else(|| std::env::current_dir().unwrap().to_string_lossy().to_string());

    let mut state = state::ShellState::new(&root)?;

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
            repl::run(&mut state)?;
        }
        Some(Commands::Proofs) => {
            commands::show_proofs()?;
        }
    }

    Ok(())
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
║  Backed by 256 formal proofs across 6 verification systems   ║
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
