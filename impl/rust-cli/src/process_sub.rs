// SPDX-License-Identifier: MPL-2.0
// Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
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
use std::ffi::OsString;
use std::path::{Path, PathBuf};
use std::process::{Child, Command as ProcessCommand};

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
    pub fn create(sub_type: ProcessSubType, cmd: String, state: &mut ShellState) -> Result<Self> {
        // Generate globally-unique FIFO path:
        //   /tmp/vsh-fifo-<pid>-<counter>-<uuidv4>
        // The pid + counter make collisions improbable in single-process use;
        // the UUID v4 suffix prevents collisions when two ShellState
        // instances share a pid (e.g., parallel cargo tests where each test
        // creates a fresh state with counter starting at 0).
        let pid = std::process::id();
        let fifo_id = state.next_fifo_id();
        let unique = uuid::Uuid::new_v4().simple();
        let fifo_path = PathBuf::from(format!("/tmp/vsh-fifo-{}-{}-{}", pid, fifo_id, unique));

        // Create FIFO using mkfifo(2) syscall
        #[cfg(unix)]
        {
            use nix::sys::stat::Mode;
            // `nix::unistd::mkfifo` takes the path directly, so no C string
            // or raw pointer is built here.
            let mode = Mode::S_IRUSR | Mode::S_IWUSR; // 0o600
            if let Err(err) = nix::unistd::mkfifo(&fifo_path, mode) {
                // If FIFO already exists, try to remove and recreate
                if err == nix::errno::Errno::EEXIST {
                    std::fs::remove_file(&fifo_path)?;
                    nix::unistd::mkfifo(&fifo_path, mode).map_err(|err| {
                        anyhow!("Failed to create FIFO {}: {}", fifo_path.display(), err)
                    })?;
                } else {
                    return Err(anyhow!(
                        "Failed to create FIFO {}: {}",
                        fifo_path.display(),
                        err
                    ));
                }
            }
        }

        #[cfg(not(unix))]
        {
            return Err(anyhow!(
                "Process substitution requires Unix (FIFOs not supported on Windows)"
            ));
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

    /// Wait for background process and cleanup.
    ///
    /// Callers run this after the last command that could open the FIFO has
    /// finished. A child that no command opened is still blocked in its
    /// `open(2)` of the FIFO, waiting for a partner, so a plain `wait` would
    /// never return (`echo <(pwd)` prints the path and opens nothing). While
    /// the child runs, the shell therefore opens the end that the child waits
    /// for, without blocking, and closes it at once: a `<(cmd)` writer sees
    /// its reader leave, and a `>(cmd)` reader sees end of file. A connected
    /// child is not cut short: the shell keeps waiting until it exits, so a
    /// `>(cmd)` reader still finishes the work it was given.
    pub fn cleanup(mut self) -> Result<()> {
        // Wait for background process to finish
        if let Some(mut child) = self.child_process.take() {
            let status = loop {
                if let Some(status) = child.try_wait()? {
                    break status;
                }
                self.release_waiting_child();
                std::thread::sleep(std::time::Duration::from_millis(10));
            };
            // A `<(cmd)` writer whose reader has gone ends on SIGPIPE. That is
            // the normal end of an unread substitution, not a failure.
            if !status.success() && !ended_by_sigpipe(&status) {
                eprintln!(
                    "Process substitution command failed: {} (exit code: {})",
                    self.command,
                    status.code().unwrap_or(-1)
                );
            }
        }

        // Remove FIFO (ignore NotFound — another process may have already cleaned it up)
        match std::fs::remove_file(&self.fifo_path) {
            Ok(()) => {}
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => {}
            Err(e) => return Err(e.into()),
        }

        Ok(())
    }
}

impl ProcessSubstitution {
    /// Open the end of the FIFO that the child waits for, without blocking,
    /// and close it again at once. An error only means that the child has not
    /// reached its own `open` yet (no reader for a `>(cmd)` FIFO); the caller
    /// tries again on its next turn.
    #[cfg(unix)]
    fn release_waiting_child(&self) {
        use std::os::unix::fs::OpenOptionsExt;
        let mut options = std::fs::OpenOptions::new();
        match self.sub_type {
            // The child writes, so the shell opens the read end.
            ProcessSubType::Input => options.read(true),
            // The child reads, so the shell opens the write end.
            ProcessSubType::Output => options.write(true),
        };
        let _ = options.custom_flags(libc::O_NONBLOCK).open(&self.fifo_path);
    }

    #[cfg(not(unix))]
    fn release_waiting_child(&self) {}
}

/// True when the process ended on SIGPIPE.
#[cfg(unix)]
fn ended_by_sigpipe(status: &std::process::ExitStatus) -> bool {
    use std::os::unix::process::ExitStatusExt;
    status.signal() == Some(libc::SIGPIPE)
}

#[cfg(not(unix))]
fn ended_by_sigpipe(_status: &std::process::ExitStatus) -> bool {
    false
}

/// Safety net: remove FIFO on drop if cleanup() was never called
impl Drop for ProcessSubstitution {
    fn drop(&mut self) {
        // Kill lingering child process
        if let Some(ref mut child) = self.child_process {
            let _ = child.kill();
            let _ = child.wait();
        }
        // Remove leaked FIFO (unconditional — ignore NotFound to avoid TOCTOU)
        let _ = std::fs::remove_file(&self.fifo_path);
    }
}

/// Start command with stdout redirected to file (for <(cmd))
fn start_command_with_output_redirect(
    cmd: &Command,
    state: &mut ShellState,
    output_path: &Path,
) -> Result<Child> {
    // For FIFOs, we use shell redirection (sh -c "cmd > fifo") to avoid blocking
    // The shell handles the FIFO opening in the background properly

    // The arguments stay OsString values and reach the shell as positional
    // parameters, forwarded with "$@". Quoting them into the script text would
    // need UTF-8 and would lose the bytes of a name that is not UTF-8.
    let (cmd_string, args): (String, Vec<OsString>) = match cmd {
        Command::External { program, args, .. } => {
            let expanded_program = crate::parser::expand_with_command_sub(program, state)?;
            let expansion =
                crate::word::expand_words(args, state, crate::word::ProcessSubs::Refuse)?;
            (format!("{expanded_program} \"$@\""), expansion.fields)
        }
        Command::Pwd { .. } => ("pwd".to_string(), Vec::new()),
        Command::Ls { path, .. } => {
            let mut cmd = "ls".to_string();
            if let Some(p) = path {
                let expanded = crate::parser::expand_with_command_sub(p, state)?;
                cmd.push_str(&format!(" '{}'", expanded.replace('\'', "'\\''")));
            }
            (cmd, Vec::new())
        }
        _ => {
            return Err(anyhow!(
                "Command type not supported in process substitution"
            ))
        }
    };

    // Use sh -c to run: cmd > fifo_path
    let shell_cmd = format!("{} > {}", cmd_string, output_path.display());
    spawn_sh(&shell_cmd, &args)
}

/// Start command with stdin redirected from file (for >(cmd))
fn start_command_with_input_redirect(
    cmd: &Command,
    state: &mut ShellState,
    input_path: &Path,
) -> Result<Child> {
    // For FIFOs, use shell redirection: sh -c "cmd < fifo"

    // As above: OsString positional parameters forwarded with "$@".
    let (cmd_string, args): (String, Vec<OsString>) = match cmd {
        Command::External { program, args, .. } => {
            let expanded_program = crate::parser::expand_with_command_sub(program, state)?;
            let expansion =
                crate::word::expand_words(args, state, crate::word::ProcessSubs::Refuse)?;
            (format!("{expanded_program} \"$@\""), expansion.fields)
        }
        _ => {
            return Err(anyhow!(
                "Command type not supported for output process substitution"
            ))
        }
    };

    // Use sh -c to run: cmd < fifo_path
    let shell_cmd = format!("{} < {}", cmd_string, input_path.display());
    spawn_sh(&shell_cmd, &args)
}

/// Run `sh -c script sh args...`. The arguments become `$1`, `$2`, ... and are
/// passed as raw OS strings, so their bytes and their boundaries survive.
fn spawn_sh(script: &str, args: &[OsString]) -> Result<Child> {
    Ok(ProcessCommand::new("sh")
        .arg("-c")
        .arg(script)
        .arg("sh")
        .args(args)
        .spawn()?)
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::TempDir;

    #[test]
    fn test_fifo_creation() {
        let temp_dir = TempDir::new().unwrap();
        let mut state = ShellState::new(temp_dir.path().to_str().unwrap()).unwrap();

        let proc_sub =
            ProcessSubstitution::create(ProcessSubType::Input, "echo test".to_string(), &mut state)
                .unwrap();

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

        let proc_sub1 =
            ProcessSubstitution::create(ProcessSubType::Input, "echo a".to_string(), &mut state)
                .unwrap();

        let proc_sub2 =
            ProcessSubstitution::create(ProcessSubType::Input, "echo b".to_string(), &mut state)
                .unwrap();

        // FIFOs should have different paths
        assert_ne!(proc_sub1.fifo_path, proc_sub2.fifo_path);

        // Cleanup
        proc_sub1.cleanup().unwrap();
        proc_sub2.cleanup().unwrap();
    }

    /// A file named `bad\xff.bin` (not UTF-8) and a pattern that matches it.
    #[cfg(unix)]
    fn non_utf8_fixture(dir: &Path) -> String {
        use std::ffi::OsStr;
        use std::os::unix::ffi::OsStrExt;
        let name = OsStr::from_bytes(b"bad\xff.bin");
        std::fs::write(dir.join(name), "12345").unwrap();
        format!("{}/bad*.bin", crate::glob::escape(&dir.to_string_lossy()))
    }

    #[cfg(unix)]
    #[test]
    fn output_redirect_keeps_non_utf8_filename_bytes() {
        let temp_dir = TempDir::new().unwrap();
        let mut state = ShellState::new(temp_dir.path().to_str().unwrap()).unwrap();
        let pattern = non_utf8_fixture(temp_dir.path());
        let cmd = parse_command(&format!("cat {pattern}")).unwrap();
        let out = temp_dir.path().join("out.txt");

        let mut child = start_command_with_output_redirect(&cmd, &mut state, &out).unwrap();
        assert!(child.wait().unwrap().success());
        assert_eq!(std::fs::read_to_string(&out).unwrap(), "12345");
    }

    #[cfg(unix)]
    #[test]
    fn input_redirect_keeps_non_utf8_filename_bytes() {
        let temp_dir = TempDir::new().unwrap();
        let mut state = ShellState::new(temp_dir.path().to_str().unwrap()).unwrap();
        let pattern = non_utf8_fixture(temp_dir.path());
        let copy = temp_dir.path().join("copy.txt");
        let cmd = parse_command(&format!("sort -o {} {pattern}", copy.display())).unwrap();
        let input = temp_dir.path().join("in.txt");
        std::fs::write(&input, "").unwrap();

        let mut child = start_command_with_input_redirect(&cmd, &mut state, &input).unwrap();
        assert!(child.wait().unwrap().success());
        assert_eq!(std::fs::read_to_string(&copy).unwrap(), "12345\n");
    }

    /// Run `f` on another thread. True when it finishes within `secs`.
    /// A cleanup that waits forever fails the test instead of hanging the suite.
    fn finishes_within(secs: u64, f: impl FnOnce() + Send + 'static) -> bool {
        let (tx, rx) = std::sync::mpsc::channel();
        std::thread::spawn(move || {
            f();
            let _ = tx.send(());
        });
        rx.recv_timeout(std::time::Duration::from_secs(secs))
            .is_ok()
    }

    fn started(sub_type: ProcessSubType, cmd: &str) -> (TempDir, ProcessSubstitution) {
        let temp_dir = TempDir::new().unwrap();
        let mut state = ShellState::new(temp_dir.path().to_str().unwrap()).unwrap();
        let mut sub = ProcessSubstitution::create(sub_type, cmd.to_string(), &mut state).unwrap();
        sub.start(&mut state).unwrap();
        (temp_dir, sub)
    }

    #[test]
    fn cleanup_releases_an_input_substitution_that_no_command_opened() {
        // `echo <(pwd)` prints the path and never opens it.
        let (_dir, sub) = started(ProcessSubType::Input, "pwd");
        let path = sub.fifo_path.clone();
        assert!(
            finishes_within(10, move || sub.cleanup().unwrap()),
            "cleanup waited forever for an unopened <(pwd)"
        );
        assert!(!path.exists());
    }

    #[test]
    fn cleanup_releases_an_output_substitution_that_no_command_opened() {
        // `echo >(cat)` prints the path and never writes to it.
        let (_dir, sub) = started(ProcessSubType::Output, "cat");
        let path = sub.fifo_path.clone();
        assert!(
            finishes_within(10, move || sub.cleanup().unwrap()),
            "cleanup waited forever for an unopened >(cat)"
        );
        assert!(!path.exists());
    }

    #[test]
    fn a_connected_input_substitution_still_delivers_its_output() {
        // `cat <(cat FILE)`: the reader gets everything, then cleanup returns.
        // (`echo` is a builtin, which a substitution does not run.)
        let src = TempDir::new().unwrap();
        let file = src.path().join("in.txt");
        std::fs::write(&file, "hi\n").unwrap();
        let (_dir, sub) = started(ProcessSubType::Input, &format!("cat {}", file.display()));
        let text = std::fs::read_to_string(&sub.fifo_path).unwrap();
        assert_eq!(text, "hi\n");
        assert!(finishes_within(10, move || sub.cleanup().unwrap()));
    }

    #[test]
    fn a_connected_output_substitution_finishes_its_work_before_cleanup_returns() {
        // `echo data > >(tee FILE)`: cleanup waits until tee has written FILE.
        let dir = TempDir::new().unwrap();
        let out = dir.path().join("out.txt");
        let mut state = ShellState::new(dir.path().to_str().unwrap()).unwrap();
        let mut sub = ProcessSubstitution::create(
            ProcessSubType::Output,
            format!("tee {}", out.display()),
            &mut state,
        )
        .unwrap();
        sub.start(&mut state).unwrap();
        std::fs::write(&sub.fifo_path, "data\n").unwrap();
        assert!(finishes_within(10, move || sub.cleanup().unwrap()));
        assert_eq!(std::fs::read_to_string(&out).unwrap(), "data\n");
    }
}
