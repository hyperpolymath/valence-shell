// SPDX-License-Identifier: PLMP-1.0-or-later
//! Interactive REPL
//!
//! Provides an interactive shell experience with:
//! - Command history
//! - Tab completion
//! - Colored prompts showing transaction state

use anyhow::Result;
use colored::Colorize;
use std::io::{self, BufRead, Write};
use std::path::PathBuf;

use crate::{commands, external, parser};
use crate::parser::Command;
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
    // Handle special commands first (not parsed)
    let trimmed = input.trim();

    match trimmed {
        "help" | "?" => {
            print_help();
            return Ok(false);
        }
        "clear" => {
            print!("\x1B[2J\x1B[1;1H");
            return Ok(false);
        }
        "status" => {
            print_status(state);
            return Ok(false);
        }
        _ => {}
    }

    // Handle aliases before parsing
    let input_normalized = match trimmed {
        s if s.starts_with("u ") || s == "u" => {
            trimmed.replacen("u", "undo", 1)
        }
        s if s.starts_with("r ") || s == "r" => {
            trimmed.replacen("r", "redo", 1)
        }
        s if s.starts_with("h ") || s == "h" => {
            trimmed.replacen("h", "history", 1)
        }
        s if s.starts_with("g ") || s == "g" => {
            trimmed.replacen("g", "graph", 1)
        }
        "q" => "quit".to_string(),
        _ => trimmed.to_string(),
    };

    // Parse command using the new parser
    let cmd = parser::parse_command(&input_normalized)?;

    // Execute command
    match cmd {
        Command::Exit | Command::Quit => {
            return Ok(true);
        }

        Command::Mkdir { path } => {
            commands::mkdir(state, &path, false)?;
        }

        Command::Rmdir { path } => {
            commands::rmdir(state, &path, false)?;
        }

        Command::Touch { path } => {
            commands::touch(state, &path, false)?;
        }

        Command::Rm { path } => {
            commands::rm(state, &path, false)?;
        }

        Command::Undo { count } => {
            commands::undo(state, count, false)?;
        }

        Command::Redo { count } => {
            commands::redo(state, count, false)?;
        }

        Command::History { count, show_proofs } => {
            commands::history(state, count, show_proofs)?;
        }

        // Transactions
        Command::Begin { name } => {
            commands::begin_transaction(state, &name)?;
        }

        Command::Commit => {
            commands::commit_transaction(state)?;
        }

        Command::Rollback => {
            commands::rollback_transaction(state)?;
        }

        // Display commands
        Command::Graph => {
            commands::show_graph(state)?;
        }

        Command::Proofs => {
            commands::show_proofs()?;
        }

        Command::Ls { path } => {
            let target = if let Some(p) = path {
                state.resolve_path(&p)
            } else {
                state.root.clone()
            };

            if target.is_dir() {
                for entry in std::fs::read_dir(&target)? {
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

        Command::Pwd => {
            println!("{}", state.root.display());
        }

        Command::Cd { path } => {
            let target = if let Some(p) = path {
                if p == "-" {
                    // cd - not implemented yet
                    anyhow::bail!("cd -: not implemented yet");
                }
                // Handle absolute vs relative paths
                if p.starts_with('/') {
                    // Absolute path - use as-is
                    PathBuf::from(p)
                } else if p.starts_with("~/") {
                    // Home-relative path
                    let home = dirs::home_dir()
                        .ok_or_else(|| anyhow::anyhow!("Could not find home directory"))?;
                    home.join(&p[2..])
                } else {
                    // Relative to current directory
                    state.root.join(&p)
                }
            } else {
                // cd with no args goes to home
                dirs::home_dir().ok_or_else(|| anyhow::anyhow!("Could not find home directory"))?
            };

            if !target.exists() {
                anyhow::bail!("cd: {}: No such file or directory", target.display());
            }

            if !target.is_dir() {
                anyhow::bail!("cd: {}: Not a directory", target.display());
            }

            // Change the shell's working directory
            std::env::set_current_dir(&target)?;
            // Update state root to track current directory
            state.root = std::fs::canonicalize(target)?;
        }

        Command::External { program, args } => {
            match external::execute_external(&program, &args) {
                Ok(exit_code) => {
                    // Store exit code for future $? support
                    state.last_exit_code = exit_code;
                }
                Err(e) => {
                    eprintln!("{}: {}", program, e);
                    state.last_exit_code = 127; // Command not found
                }
            }
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
    println!("  {}         Change directory", "cd [path]".bright_green());
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

    println!("{}", "External Commands:".bright_yellow());
    println!("  Any other command will be executed as an external program");
    println!("  Example: {} or {}", "ls -la".bright_green(), "cat file.txt".bright_green());
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
