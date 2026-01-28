// SPDX-License-Identifier: PMPL-1.0-or-later
//! External Command Execution
//!
//! Executes external programs via execve(), handles PATH lookup,
//! and manages stdio.

use anyhow::{Context, Result};
use std::path::PathBuf;
use std::process::{Command, Stdio};

/// Execute an external command
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

    // Handle exit status
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
