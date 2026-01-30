// SPDX-License-Identifier: PLMP-1.0-or-later
//! Friendly Error Messages (fish-style)
//!
//! Transforms technical error messages into user-friendly explanations
//! with suggestions for fixing the problem.

use colored::Colorize;
use std::io::{self, Write};
use std::path::{Path, PathBuf};

use crate::correction::suggest_correction;

/// Display a friendly error message to the user
///
/// Takes an anyhow::Error and displays it with:
/// - Clear explanation of what went wrong
/// - Suggestions for similar paths/commands
/// - Actionable steps to fix the problem
///
/// # Examples
///
/// ```
/// use vsh::friendly_errors::display_friendly_error;
/// use anyhow::anyhow;
///
/// let error = anyhow!("No such file or directory: /tmp/missing");
/// display_friendly_error(&error);
/// // Prints friendly message with suggestions
/// ```
pub fn display_friendly_error(error: &anyhow::Error) {
    let error_msg = error.to_string();

    // Try to match error patterns and display friendly messages
    if error_msg.contains("No such file or directory")
        || error_msg.contains("does not exist")
        || error_msg.contains("not found")
    {
        handle_not_found_error(&error_msg);
    } else if error_msg.contains("Permission denied") || error_msg.contains("permission") {
        handle_permission_error(&error_msg);
    } else if error_msg.contains("command not found")
        || error_msg.contains("CommandNotFound")
        || error_msg.contains("failed to execute")
    {
        handle_command_not_found(&error_msg);
    } else if error_msg.contains("File exists") || error_msg.contains("already exists") {
        handle_already_exists_error(&error_msg);
    } else if error_msg.contains("Is a directory") {
        handle_is_directory_error(&error_msg);
    } else if error_msg.contains("Not a directory") {
        handle_not_directory_error(&error_msg);
    } else {
        // Generic error - still make it friendly
        handle_generic_error(&error_msg);
    }
}

fn handle_not_found_error(error_msg: &str) {
    eprintln!("{}: The file or directory does not exist.", "vsh".bright_red().bold());
    eprintln!();

    // Try to extract path from error message
    if let Some(path) = extract_path(error_msg) {
        eprintln!("  Path: {}", path.bright_cyan());
        eprintln!();

        // Suggest similar paths
        if let Some(suggestions) = find_similar_paths(&path) {
            eprintln!("Did you mean one of these?");
            for suggestion in suggestions.iter().take(3) {
                eprintln!("  {}", suggestion.display().to_string().bright_green());
            }
            eprintln!();
        }

        // Suggest creation
        eprintln!("Or create it with:");
        if path.ends_with('/') || !path.contains('.') {
            eprintln!("  {}", format!("mkdir {}", path).bright_yellow());
        } else {
            eprintln!("  {}", format!("touch {}", path).bright_yellow());
        }
    }
}

fn handle_permission_error(error_msg: &str) {
    eprintln!("{}: Permission denied.", "vsh".bright_red().bold());
    eprintln!();
    eprintln!("You don't have permission to access this file or directory.");
    eprintln!();

    if let Some(path) = extract_path(error_msg) {
        eprintln!("  Path: {}", path.bright_cyan());
        eprintln!();
    }

    eprintln!("Try:");
    eprintln!("  {} Run as superuser", "sudo vsh".bright_yellow());
    if let Some(path) = extract_path(error_msg) {
        if error_msg.contains("read") || error_msg.contains("open") {
            eprintln!("  {} Make file readable", format!("chmod +r {}", path).bright_yellow());
        } else if error_msg.contains("write") {
            eprintln!("  {} Make file writable", format!("chmod +w {}", path).bright_yellow());
        } else if error_msg.contains("execute") {
            eprintln!("  {} Make file executable", format!("chmod +x {}", path).bright_yellow());
        }
    }
}

fn handle_command_not_found(error_msg: &str) {
    eprintln!("{}: Command not found.", "vsh".bright_red().bold());
    eprintln!();

    // Try to extract command name
    if let Some(cmd) = extract_command(error_msg) {
        eprintln!("  Command: {}", cmd.bright_cyan());
        eprintln!();

        // Suggest correction
        if let Some(suggestion) = suggest_correction(&cmd) {
            eprintln!("Did you mean:");
            eprintln!("  {}", suggestion.bright_green());
            eprintln!();
        }

        // Suggest package search
        eprintln!("Search for this command:");
        eprintln!("  {} (Fedora)", format!("dnf search {}", cmd).bright_yellow());
        eprintln!("  {} (Ubuntu/Debian)", format!("apt search {}", cmd).bright_yellow());
        eprintln!("  {} (Arch)", format!("pacman -Ss {}", cmd).bright_yellow());
    }
}

fn handle_already_exists_error(error_msg: &str) {
    eprintln!("{}: File or directory already exists.", "vsh".bright_red().bold());
    eprintln!();

    if let Some(path) = extract_path(error_msg) {
        eprintln!("  Path: {}", path.bright_cyan());
        eprintln!();

        eprintln!("To replace it:");
        eprintln!("  {} Remove first, then create", format!("rm {} && touch {}", path, path).bright_yellow());
        eprintln!();
        eprintln!("Or use a different name:");
        eprintln!("  {} Add suffix", format!("{}.new", path).bright_yellow());
    }
}

fn handle_is_directory_error(error_msg: &str) {
    eprintln!("{}: Expected a file but found a directory.", "vsh".bright_red().bold());
    eprintln!();

    if let Some(path) = extract_path(error_msg) {
        eprintln!("  Path: {}", path.bright_cyan());
        eprintln!();

        eprintln!("To remove a directory:");
        eprintln!("  {} Remove empty directory", format!("rmdir {}", path).bright_yellow());
        eprintln!("  {} Remove directory and contents", format!("rm -r {}", path).bright_yellow());
    }
}

fn handle_not_directory_error(error_msg: &str) {
    eprintln!("{}: Expected a directory but found a file.", "vsh".bright_red().bold());
    eprintln!();

    if let Some(path) = extract_path(error_msg) {
        eprintln!("  Path: {}", path.bright_cyan());
        eprintln!();

        eprintln!("To create a directory:");
        eprintln!("  {} Remove file first", format!("rm {}", path).bright_yellow());
        eprintln!("  {} Then create directory", format!("mkdir {}", path).bright_yellow());
    }
}

fn handle_generic_error(error_msg: &str) {
    eprintln!("{}: {}", "vsh".bright_red().bold(), error_msg);
    eprintln!();
    eprintln!("For help, try:");
    eprintln!("  {}", "help".bright_yellow());
    eprintln!("  {}", "help <command>".bright_yellow());
}

/// Extract path from error message
fn extract_path(error_msg: &str) -> Option<String> {
    // Common patterns:
    // "No such file or directory: /path/to/file"
    // "Permission denied: /path/to/file"
    // "/path/to/file: No such file"

    // Try colon-separated
    if let Some(idx) = error_msg.rfind(": ") {
        let after_colon = &error_msg[idx + 2..].trim();
        // Remove quotes if present
        let cleaned = after_colon.trim_matches(|c| c == '"' || c == '\'');
        if !cleaned.is_empty() && (cleaned.starts_with('/') || cleaned.starts_with('.')) {
            return Some(cleaned.to_string());
        }
    }

    // Try space-separated (find first thing that looks like a path)
    for word in error_msg.split_whitespace() {
        let cleaned = word.trim_matches(|c: char| !c.is_alphanumeric() && c != '/' && c != '.' && c != '_' && c != '-');
        if cleaned.starts_with('/') || cleaned.starts_with("./") || cleaned.starts_with("../") {
            return Some(cleaned.to_string());
        }
    }

    None
}

/// Extract command name from error message
fn extract_command(error_msg: &str) -> Option<String> {
    // Patterns:
    // "command not found: cmd"
    // "CommandNotFound(\"cmd\")"
    // "failed to execute: cmd"

    // Try after "command not found"
    if let Some(idx) = error_msg.find("command not found:") {
        let after = &error_msg[idx + 18..].trim();
        return Some(after.split_whitespace().next()?.to_string());
    }

    // Try CommandNotFound(\"cmd\")
    if let Some(start) = error_msg.find("CommandNotFound(") {
        let after = &error_msg[start + 16..];
        if let Some(end) = after.find(')') {
            let cmd = &after[..end]
                .trim_matches(|c| c == '"' || c == '\'' || c == '(' || c == ')');
            return Some(cmd.to_string());
        }
    }

    // Try "failed to execute"
    if let Some(idx) = error_msg.find("failed to execute:") {
        let after = &error_msg[idx + 18..].trim();
        return Some(after.split_whitespace().next()?.to_string());
    }

    None
}

/// Find similar paths in the parent directory
fn find_similar_paths(path: &str) -> Option<Vec<PathBuf>> {
    let path_buf = PathBuf::from(path);

    // Get parent directory
    let parent = path_buf.parent()?;
    if !parent.exists() {
        return None;
    }

    // Get filename
    let filename = path_buf.file_name()?.to_str()?;

    // Read parent directory
    let entries = std::fs::read_dir(parent).ok()?;

    let mut similar = Vec::new();
    for entry in entries.flatten() {
        if let Some(entry_name) = entry.file_name().to_str() {
            // Calculate similarity (simple: starts with same char or contains substring)
            if entry_name.starts_with(&filename[..1.min(filename.len())])
                || entry_name.contains(filename)
                || filename.contains(entry_name)
            {
                similar.push(entry.path());
            }
        }
    }

    if similar.is_empty() {
        None
    } else {
        Some(similar)
    }
}

/// Ask user for confirmation (used in command correction)
pub fn ask_correction_confirmation(suggestion: &str) -> std::io::Result<bool> {
    eprint!("Did you mean '{}'? [y/n] ", suggestion.bright_green());
    io::stderr().flush()?;

    let mut response = String::new();
    io::stdin().read_line(&mut response)?;

    Ok(response.trim().to_lowercase() == "y" || response.trim().to_lowercase() == "yes")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_extract_path() {
        assert_eq!(
            extract_path("No such file or directory: /tmp/test"),
            Some("/tmp/test".to_string())
        );

        assert_eq!(
            extract_path("Permission denied: ./file.txt"),
            Some("./file.txt".to_string())
        );

        assert_eq!(
            extract_path("/tmp/missing: No such file"),
            Some("/tmp/missing".to_string())
        );
    }

    #[test]
    fn test_extract_command() {
        assert_eq!(
            extract_command("command not found: sl"),
            Some("sl".to_string())
        );

        assert_eq!(
            extract_command("CommandNotFound(\"gti\")"),
            Some("gti".to_string())
        );

        assert_eq!(
            extract_command("failed to execute: nonexistent"),
            Some("nonexistent".to_string())
        );
    }
}
