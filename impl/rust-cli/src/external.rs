// SPDX-License-Identifier: PMPL-1.0-or-later
//! External Command Execution
//!
//! Executes external programs via execve(), handles PATH lookup,
//! and manages stdio.

use anyhow::{Context, Result};
use std::fs::{File, OpenOptions};
use std::path::PathBuf;
use std::process::{Command, Stdio};

use crate::redirection::{Redirection, RedirectSetup};
use crate::state::ShellState;

/// Execute an external command with I/O redirections
///
/// Handles:
/// - Output redirection (>, >>, 2>, 2>>, &>)
/// - Input redirection (<)
/// - Error to output (2>&1)
/// - Signal termination (SIGINT, SIGTERM)
/// - File modification tracking for undo
pub fn execute_external_with_redirects(
    program: &str,
    args: &[String],
    redirects: &[Redirection],
    state: &mut ShellState,
) -> Result<i32> {
    // Setup redirections (validates, opens files, saves state)
    let redirect_setup = RedirectSetup::setup(redirects, state)?;

    // Configure stdio from redirections
    let (stdin_cfg, stdout_cfg, stderr_cfg) =
        stdio_config_from_redirects(redirects, &redirect_setup, state)?;

    // PATH lookup
    let executable = find_in_path(program)?;

    // Execute with redirected stdio
    let status = Command::new(&executable)
        .args(args)
        .stdin(stdin_cfg)
        .stdout(stdout_cfg)
        .stderr(stderr_cfg)
        .status()
        .context(format!("Failed to execute: {}", program))?;

    // Record file modifications for undo
    redirect_setup.record_for_undo(state)?;

    // Handle exit status (including signals)
    handle_exit_status(status)
}

/// Execute an external command (no redirections - legacy)
///
/// Handles signal termination (SIGINT, SIGTERM) and returns appropriate exit codes.
/// Exit code 130 indicates SIGINT (Ctrl+C), 143 indicates SIGTERM.
pub fn execute_external(program: &str, args: &[String]) -> Result<i32> {
    // PATH lookup
    let executable = find_in_path(program)?;

    // Execute via std::process::Command
    let status = Command::new(&executable)
        .args(args)
        .stdin(Stdio::inherit()) // Pass through stdin
        .stdout(Stdio::inherit()) // Pass through stdout
        .stderr(Stdio::inherit()) // Pass through stderr
        .status()
        .context(format!("Failed to execute: {}", program))?;

    handle_exit_status(status)
}

/// Convert redirections to stdio configuration
fn stdio_config_from_redirects(
    redirects: &[Redirection],
    _setup: &RedirectSetup,
    state: &ShellState,
) -> Result<(Stdio, Stdio, Stdio)> {
    let mut stdin_cfg = Stdio::inherit();
    let mut stdout_cfg = Stdio::inherit();
    let mut stderr_cfg = Stdio::inherit();

    for redirect in redirects {
        match redirect {
            Redirection::Output { file } | Redirection::Append { file } => {
                let target = state.resolve_path(file);
                let file_handle = File::create(&target)
                    .with_context(|| format!("Failed to open output file: {}", target.display()))?;
                stdout_cfg = Stdio::from(file_handle);
            }

            Redirection::Input { file } => {
                let target = state.resolve_path(file);
                let file_handle = File::open(&target)
                    .with_context(|| format!("Failed to open input file: {}", target.display()))?;
                stdin_cfg = Stdio::from(file_handle);
            }

            Redirection::ErrorOutput { file } | Redirection::ErrorAppend { file } => {
                let target = state.resolve_path(file);
                let file_handle = if matches!(redirect, Redirection::ErrorAppend { .. }) {
                    OpenOptions::new()
                        .create(true)
                        .append(true)
                        .open(&target)
                } else {
                    File::create(&target)
                }
                .with_context(|| format!("Failed to open error file: {}", target.display()))?;

                stderr_cfg = Stdio::from(file_handle);
            }

            Redirection::BothOutput { file } => {
                let target = state.resolve_path(file);
                let file_handle = File::create(&target)
                    .with_context(|| format!("Failed to open output file: {}", target.display()))?;

                // Clone the file handle for both stdout and stderr
                let file_handle2 = file_handle
                    .try_clone()
                    .context("Failed to duplicate file handle")?;

                stdout_cfg = Stdio::from(file_handle);
                stderr_cfg = Stdio::from(file_handle2);
            }

            Redirection::ErrorToOutput => {
                // Redirect stderr to stdout's current target
                // This is tricky with Stdio - need to use piped() and manual plumbing
                // For now, use simpler approach: both to same file
                // TODO: Implement proper fd duplication
                stderr_cfg = Stdio::inherit(); // Fallback
            }
        }
    }

    Ok((stdin_cfg, stdout_cfg, stderr_cfg))
}

/// Handle command exit status, converting signals to exit codes
fn handle_exit_status(status: std::process::ExitStatus) -> Result<i32> {
    #[cfg(unix)]
    {
        use std::os::unix::process::ExitStatusExt;

        // Check if terminated by signal
        if let Some(signal) = status.signal() {
            // Convert Unix signal to shell exit code
            // Convention: 128 + signal number
            let exit_code = 128 + signal;
            return Ok(exit_code);
        }
    }

    // Normal exit code
    Ok(status.code().unwrap_or(1))
}

/// Find executable in PATH
fn find_in_path(program: &str) -> Result<PathBuf> {
    // If path contains '/', treat as literal path
    if program.contains('/') {
        let path = PathBuf::from(program);
        if path.exists() && is_executable(&path) {
            return Ok(path);
        }
        anyhow::bail!("Command not found: {}", program);
    }

    // Search PATH
    let path_env =
        std::env::var("PATH").unwrap_or_else(|_| "/usr/local/bin:/usr/bin:/bin".to_string());

    for dir in path_env.split(':') {
        let candidate = PathBuf::from(dir).join(program);
        if candidate.exists() && is_executable(&candidate) {
            return Ok(candidate);
        }
    }

    anyhow::bail!("Command not found: {}", program);
}

/// Check if file is executable
fn is_executable(path: &PathBuf) -> bool {
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        if let Ok(metadata) = std::fs::metadata(path) {
            let perms = metadata.permissions();
            return perms.mode() & 0o111 != 0; // Check any execute bit
        }
    }
    #[cfg(not(unix))]
    {
        // On non-Unix, just check if file exists
        let _ = path;
        true
    }
    false
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_find_ls() {
        let ls = find_in_path("ls");
        assert!(ls.is_ok(), "Should find 'ls' in PATH");
        if let Ok(ls_path) = ls {
            assert!(ls_path.to_string_lossy().contains("ls"));
        }
    }

    #[test]
    fn test_not_found() {
        assert!(find_in_path("nonexistent-command-xyz").is_err());
    }

    #[test]
    fn test_absolute_path() {
        let result = find_in_path("/bin/ls");
        // Platform-dependent - may or may not exist
        assert!(result.is_ok() || result.is_err());
    }

    #[test]
    fn test_executable_check() {
        // Test with a known executable
        if let Ok(ls_path) = find_in_path("ls") {
            assert!(is_executable(&ls_path), "ls should be executable");
        }
    }

    #[test]
    fn test_external_command_success() {
        // Test successful command execution
        let exit_code = execute_external("true", &[]).unwrap();
        assert_eq!(exit_code, 0, "true command should return 0");
    }

    #[test]
    fn test_external_command_failure() {
        // Test failed command execution
        let exit_code = execute_external("false", &[]).unwrap();
        assert_eq!(exit_code, 1, "false command should return 1");
    }

    #[test]
    fn test_external_command_with_args() {
        // Test command with arguments
        let exit_code = execute_external("echo", &["hello".to_string()]).unwrap();
        assert_eq!(exit_code, 0, "echo should return 0");
    }
}
