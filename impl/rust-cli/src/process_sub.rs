// SPDX-License-Identifier: PLMP-1.0-or-later
//! Process Substitution Implementation
//!
//! Implements POSIX-style process substitution for treating command output as files.
//!
//! # Examples
//!
//! ```bash
//! # Input process substitution
//! diff <(ls dir1) <(ls dir2)
//!
//! # Output process substitution
//! tee >(wc -l) >(grep pattern)
//! ```

use anyhow::{anyhow, Result};
use std::os::unix::fs::PermissionsExt;
use std::path::PathBuf;
use std::process::{Child, Command as ProcessCommand, Stdio};

use crate::parser::{parse_command, Command, ProcessSubType};
use crate::state::ShellState;

/// Process substitution instance
pub struct ProcessSubstitution {
    /// Path to the FIFO
    pub fifo_path: PathBuf,
    /// Command being executed
    pub command: String,
    /// Type (input or output)
    pub sub_type: ProcessSubType,
    /// Background process handle
    pub child_process: Option<Child>,
}

impl ProcessSubstitution {
    /// Create new process substitution with FIFO
    pub fn create(
        sub_type: ProcessSubType,
        cmd: String,
        state: &mut ShellState,
    ) -> Result<Self> {
        // Generate unique FIFO path: /tmp/vsh-fifo-<pid>-<counter>
        let pid = std::process::id();
        let fifo_id = state.next_fifo_id();
        let fifo_path = PathBuf::from(format!("/tmp/vsh-fifo-{}-{}", pid, fifo_id));

        // Create FIFO using mkfifo(2) syscall
        #[cfg(unix)]
        {
            use std::ffi::CString;
            let path_cstr = CString::new(fifo_path.to_str().unwrap())?;
            let result = unsafe { libc::mkfifo(path_cstr.as_ptr(), 0o600) };
            if result != 0 {
                let err = std::io::Error::last_os_error();
                // If FIFO already exists, try to remove and recreate
                if err.kind() == std::io::ErrorKind::AlreadyExists {
                    if fifo_path.exists() {
                        std::fs::remove_file(&fifo_path)?;
                        let result = unsafe { libc::mkfifo(path_cstr.as_ptr(), 0o600) };
                        if result != 0 {
                            let err = std::io::Error::last_os_error();
                            return Err(anyhow!("Failed to create FIFO {}: {}", fifo_path.display(), err));
                        }
                    }
                } else {
                    return Err(anyhow!("Failed to create FIFO {}: {}", fifo_path.display(), err));
                }
            }
        }

        #[cfg(not(unix))]
        {
            return Err(anyhow!("Process substitution requires Unix (FIFOs not supported on Windows)"));
        }

        Ok(Self {
            fifo_path,
            command: cmd,
            sub_type,
            child_process: None,
        })
    }

    /// Start background process
    pub fn start(&mut self, state: &mut ShellState) -> Result<()> {
        // Parse command
        let parsed_cmd = parse_command(&self.command)?;

        // Start background process with appropriate redirection
        let child = match self.sub_type {
            ProcessSubType::Input => {
                // <(cmd): Command writes to FIFO (stdout → FIFO)
                start_command_with_output_redirect(&parsed_cmd, state, &self.fifo_path)?
            }
            ProcessSubType::Output => {
                // >(cmd): Command reads from FIFO (FIFO → stdin)
                start_command_with_input_redirect(&parsed_cmd, state, &self.fifo_path)?
            }
        };

        self.child_process = Some(child);
        Ok(())
    }

    /// Wait for background process and cleanup
    pub fn cleanup(mut self) -> Result<()> {
        // Wait for background process to finish
        if let Some(mut child) = self.child_process.take() {
            let status = child.wait()?;
            if !status.success() {
                eprintln!(
                    "Process substitution command failed: {} (exit code: {})",
                    self.command,
                    status.code().unwrap_or(-1)
                );
            }
        }

        // Remove FIFO
        if self.fifo_path.exists() {
            std::fs::remove_file(&self.fifo_path)?;
        }

        Ok(())
    }
}

/// Start command with stdout redirected to file (for <(cmd))
fn start_command_with_output_redirect(
    cmd: &Command,
    state: &mut ShellState,
    output_path: &PathBuf,
) -> Result<Child> {
    // For FIFOs, we use shell redirection (sh -c "cmd > fifo") to avoid blocking
    // The shell handles the FIFO opening in the background properly

    let cmd_string = match cmd {
        Command::External { program, args, .. } => {
            let expanded_program = crate::parser::expand_with_command_sub(program, state)?;
            let expanded_args: Result<Vec<String>> = args
                .iter()
                .map(|arg| crate::parser::expand_with_command_sub(arg, state))
                .collect();
            let expanded_args = expanded_args?;

            // Build command string: prog arg1 arg2 > fifo
            let mut cmd = expanded_program;
            for arg in expanded_args {
                cmd.push(' ');
                // Simple shell escaping (single quotes)
                cmd.push_str(&format!("'{}'", arg.replace('\'', "'\\''")));
            }
            cmd
        }
        Command::Pwd { .. } => "pwd".to_string(),
        Command::Ls { path, .. } => {
            let mut cmd = "ls".to_string();
            if let Some(p) = path {
                let expanded = crate::parser::expand_with_command_sub(p, state)?;
                cmd.push_str(&format!(" '{}'", expanded.replace('\'', "'\\''")));
            }
            cmd
        }
        _ => return Err(anyhow!("Command type not supported in process substitution")),
    };

    // Use sh -c to run: cmd > fifo_path
    let shell_cmd = format!("{} > {}", cmd_string, output_path.display());

    let child = ProcessCommand::new("sh")
        .arg("-c")
        .arg(&shell_cmd)
        .spawn()?;

    Ok(child)
}

/// Start command with stdin redirected from file (for >(cmd))
fn start_command_with_input_redirect(
    cmd: &Command,
    state: &mut ShellState,
    input_path: &PathBuf,
) -> Result<Child> {
    // For FIFOs, use shell redirection: sh -c "cmd < fifo"

    let cmd_string = match cmd {
        Command::External { program, args, .. } => {
            let expanded_program = crate::parser::expand_with_command_sub(program, state)?;
            let expanded_args: Result<Vec<String>> = args
                .iter()
                .map(|arg| crate::parser::expand_with_command_sub(arg, state))
                .collect();
            let expanded_args = expanded_args?;

            // Build command string
            let mut cmd = expanded_program;
            for arg in expanded_args {
                cmd.push(' ');
                cmd.push_str(&format!("'{}'", arg.replace('\'', "'\\''")));
            }
            cmd
        }
        _ => return Err(anyhow!("Command type not supported for output process substitution")),
    };

    // Use sh -c to run: cmd < fifo_path
    let shell_cmd = format!("{} < {}", cmd_string, input_path.display());

    let child = ProcessCommand::new("sh")
        .arg("-c")
        .arg(&shell_cmd)
        .spawn()?;

    Ok(child)
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::TempDir;

    #[test]
    fn test_fifo_creation() {
        let temp_dir = TempDir::new().unwrap();
        let mut state = ShellState::new(temp_dir.path().to_str().unwrap()).unwrap();

        let proc_sub = ProcessSubstitution::create(
            ProcessSubType::Input,
            "echo test".to_string(),
            &mut state,
        ).unwrap();

        // FIFO should exist
        assert!(proc_sub.fifo_path.exists());

        // Should be a FIFO
        #[cfg(unix)]
        {
            let metadata = std::fs::metadata(&proc_sub.fifo_path).unwrap();
            use std::os::unix::fs::FileTypeExt;
            assert!(metadata.file_type().is_fifo());
        }

        // Cleanup should remove FIFO
        let fifo_path = proc_sub.fifo_path.clone();
        proc_sub.cleanup().unwrap();
        assert!(!fifo_path.exists());
    }

    #[test]
    fn test_fifo_path_unique() {
        let temp_dir = TempDir::new().unwrap();
        let mut state = ShellState::new(temp_dir.path().to_str().unwrap()).unwrap();

        let proc_sub1 = ProcessSubstitution::create(
            ProcessSubType::Input,
            "echo a".to_string(),
            &mut state,
        ).unwrap();

        let proc_sub2 = ProcessSubstitution::create(
            ProcessSubType::Input,
            "echo b".to_string(),
            &mut state,
        ).unwrap();

        // FIFOs should have different paths
        assert_ne!(proc_sub1.fifo_path, proc_sub2.fifo_path);

        // Cleanup
        proc_sub1.cleanup().unwrap();
        proc_sub2.cleanup().unwrap();
    }
}
