// SPDX-License-Identifier: AGPL-3.0-or-later
//! Interactive REPL
//!
//! Provides an interactive shell experience with:
//! - Command history
//! - Tab completion
//! - Colored prompts showing transaction state

use anyhow::Result;
use colored::Colorize;
use std::io::{self, BufRead, Write};

use crate::commands;
use crate::state::ShellState;

/// Run the interactive REPL
pub fn run(state: &mut ShellState) -> Result<()> {
    let stdin = io::stdin();
    let mut stdout = io::stdout();

    loop {
        // Build prompt
        let prompt = build_prompt(state);
        print!("{}", prompt);
        stdout.flush()?;

        // Read line
        let mut input = String::new();
        if stdin.lock().read_line(&mut input)? == 0 {
            // EOF
            break;
        }

        let input = input.trim();
        if input.is_empty() {
            continue;
        }

        // Parse and execute
        match execute_line(state, input) {
            Ok(should_exit) => {
                if should_exit {
                    break;
                }
            }
            Err(e) => {
                eprintln!("{} {}", "Error:".bright_red(), e);
            }
        }
    }

    println!("{}", "\nGoodbye!".bright_blue());
    Ok(())
}

fn build_prompt(state: &ShellState) -> String {
    let txn_indicator = if state.active_transaction.is_some() {
        format!(
            "{}/",
            format!("txn:{}", state.active_transaction.as_ref().unwrap().name)
                .bright_cyan()
        )
    } else {
        String::new()
    };

    let undo_count = state.history.iter().filter(|o| !o.undone).count();
    let undo_indicator = if undo_count > 0 {
        format!(" {}", format!("[{}↩]", undo_count).bright_black())
    } else {
        String::new()
    };

    format!(
        "{}{}{}> ",
        "vsh".bright_blue().bold(),
        txn_indicator,
        undo_indicator
    )
}

fn execute_line(state: &mut ShellState, input: &str) -> Result<bool> {
    let parts: Vec<&str> = input.split_whitespace().collect();
    if parts.is_empty() {
        return Ok(false);
    }

    let cmd = parts[0];
    let args = &parts[1..];

    match cmd {
        // Exit commands
        "exit" | "quit" | "q" => {
            return Ok(true);
        }

        // Help
        "help" | "?" => {
            print_help();
        }

        // Directory operations
        "mkdir" => {
            if args.is_empty() {
                anyhow::bail!("Usage: mkdir <path>");
            }
            commands::mkdir(state, args[0], false)?;
        }

        "rmdir" => {
            if args.is_empty() {
                anyhow::bail!("Usage: rmdir <path>");
            }
            commands::rmdir(state, args[0], false)?;
        }

        // File operations
        "touch" => {
            if args.is_empty() {
                anyhow::bail!("Usage: touch <path>");
            }
            commands::touch(state, args[0], false)?;
        }

        "rm" => {
            if args.is_empty() {
                anyhow::bail!("Usage: rm <path>");
            }
            commands::rm(state, args[0], false)?;
        }

        // Undo/Redo
        "undo" | "u" => {
            let count = args.first().and_then(|s| s.parse().ok()).unwrap_or(1);
            commands::undo(state, count, false)?;
        }

        "redo" | "r" => {
            let count = args.first().and_then(|s| s.parse().ok()).unwrap_or(1);
            commands::redo(state, count, false)?;
        }

        // History
        "history" | "h" => {
            let show_proofs = args.contains(&"--proofs") || args.contains(&"-p");
            let count = args
                .iter()
                .filter(|s| !s.starts_with('-'))
                .find_map(|s| s.parse().ok())
                .unwrap_or(10);
            commands::history(state, count, show_proofs)?;
        }

        // Transactions
        "begin" => {
            if args.is_empty() {
                anyhow::bail!("Usage: begin <name>");
            }
            commands::begin_transaction(state, args[0])?;
        }

        "commit" => {
            commands::commit_transaction(state)?;
        }

        "rollback" => {
            commands::rollback_transaction(state)?;
        }

        // Graph
        "graph" | "g" => {
            commands::show_graph(state)?;
        }

        // Proofs
        "proofs" | "proof" => {
            commands::show_proofs()?;
        }

        // List (convenience)
        "ls" => {
            let path = args.first().map(|s| state.resolve_path(s)).unwrap_or(state.root.clone());
            if path.is_dir() {
                for entry in std::fs::read_dir(&path)? {
                    let entry = entry?;
                    let name = entry.file_name();
                    let file_type = entry.file_type()?;
                    if file_type.is_dir() {
                        println!("{}/", name.to_string_lossy().bright_blue());
                    } else {
                        println!("{}", name.to_string_lossy());
                    }
                }
            } else {
                anyhow::bail!("Not a directory");
            }
        }

        // pwd
        "pwd" => {
            println!("{}", state.root.display());
        }

        // Clear screen
        "clear" => {
            print!("\x1B[2J\x1B[1;1H");
        }

        // Status
        "status" => {
            print_status(state);
        }

        // Unknown command
        _ => {
            eprintln!(
                "{} Unknown command: {}",
                "?".bright_yellow(),
                cmd.bright_red()
            );
            eprintln!("Type 'help' for available commands");
        }
    }

    Ok(false)
}

fn print_help() {
    println!("{}", "═══ Valence Shell Commands ═══".bright_blue().bold());
    println!();

    println!("{}", "Filesystem Operations:".bright_yellow());
    println!("  {}      Create a directory", "mkdir <path>".bright_green());
    println!("  {}      Remove an empty directory", "rmdir <path>".bright_green());
    println!("  {}      Create an empty file", "touch <path>".bright_green());
    println!("  {}         Remove a file", "rm <path>".bright_green());
    println!("  {}         List directory contents", "ls [path]".bright_green());
    println!("  {}            Show current directory", "pwd".bright_green());
    println!();

    println!("{}", "Reversibility:".bright_yellow());
    println!("  {}        Undo last operation(s)", "undo [N]".bright_cyan());
    println!("  {}        Redo last undone operation(s)", "redo [N]".bright_cyan());
    println!("  {} Show operation history", "history [N]".bright_cyan());
    println!("  {}       Add --proofs to see theorems", "history -p".bright_cyan());
    println!("  {}           Show operation DAG", "graph".bright_cyan());
    println!();

    println!("{}", "Transactions:".bright_yellow());
    println!("  {}  Start a transaction group", "begin <name>".bright_magenta());
    println!("  {}         Commit current transaction", "commit".bright_magenta());
    println!("  {}       Rollback current transaction", "rollback".bright_magenta());
    println!();

    println!("{}", "Information:".bright_yellow());
    println!("  {}         Show verification info", "proofs".bright_white());
    println!("  {}         Show shell status", "status".bright_white());
    println!("  {}           Show this help", "help".bright_white());
    println!();

    println!("{}", "Other:".bright_yellow());
    println!("  {}          Clear screen", "clear".bright_black());
    println!("  {}           Exit shell", "exit".bright_black());
    println!();

    println!(
        "{}",
        "All filesystem operations are reversible with 'undo'".bright_black()
    );
    println!(
        "{}",
        "Backed by formal proofs - use 'proofs' to see details".bright_black()
    );
}

fn print_status(state: &ShellState) {
    println!("{}", "═══ Shell Status ═══".bright_blue().bold());
    println!();
    println!("  {}: {}", "Sandbox root".bright_black(), state.root.display());
    println!(
        "  {}: {}",
        "Total operations".bright_black(),
        state.history.len()
    );
    println!(
        "  {}: {}",
        "Undoable ops".bright_black(),
        state.history.iter().filter(|o| !o.undone).count()
    );
    println!(
        "  {}: {}",
        "Redo stack".bright_black(),
        state.get_redo_stack().len()
    );

    if let Some(ref txn) = state.active_transaction {
        println!();
        println!(
            "  {}: {} ({})",
            "Active transaction".bright_cyan(),
            txn.name,
            format!("{} ops", txn.operations.len()).bright_black()
        );
    }

    println!(
        "  {}: {}",
        "Completed transactions".bright_black(),
        state.transactions.len()
    );
}
