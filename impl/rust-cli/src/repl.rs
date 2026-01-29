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
use std::sync::atomic::Ordering;

use crate::executable::{ExecutableCommand, ExecutionResult};
use crate::parser;
use crate::state::ShellState;

/// Run the interactive REPL (Read-Eval-Print Loop).
///
/// Starts an interactive shell session with:
/// - Command history
/// - Colored prompts showing transaction state
/// - Ctrl+C handling for interrupting commands
/// - EOF (Ctrl+D) to exit
///
/// # Arguments
/// * `state` - Mutable shell state for command execution
///
/// # Errors
/// Returns error if:
/// - SIGINT handler installation fails
/// - Terminal I/O fails
/// - Command execution fails fatally
///
/// # Examples
/// ```no_run
/// use vsh::repl;
/// use vsh::state::ShellState;
///
/// let mut state = ShellState::new("/tmp/workspace")?;
/// repl::run(&mut state)?;  // Starts interactive shell
/// # Ok::<(), anyhow::Error>(())
/// ```
pub fn run(state: &mut ShellState) -> Result<()> {
    // Install SIGINT handler for graceful Ctrl+C handling
    ctrlc::set_handler(move || {
        crate::INTERRUPT_REQUESTED.store(true, Ordering::Relaxed);
    })
    .expect("Error setting Ctrl-C handler");

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
        if input.is_empty() || input.starts_with('#') {
            // Skip empty lines and comments
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
    let txn_indicator = if let Some(ref txn) = state.active_transaction {
        format!(
            "{}/",
            format!("txn:{}", txn.name).bright_cyan()
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

    // Parse command using the parser
    let cmd = parser::parse_command(&input_normalized)?;

    // Execute command using trait (Seam 1↔2)
    let result = cmd.execute(state)?;

    // Handle execution result
    match result {
        ExecutionResult::Exit => Ok(true),
        ExecutionResult::ExternalCommand { exit_code } => {
            state.last_exit_code = exit_code;
            Ok(false)
        }
        ExecutionResult::Success => Ok(false),
    }
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
    println!("  {}          Return to previous directory", "cd -".bright_green());
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
