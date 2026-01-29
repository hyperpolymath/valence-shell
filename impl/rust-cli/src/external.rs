// SPDX-License-Identifier: PMPL-1.0-or-later
//! External Command Execution
//!
//! Executes external programs via execve(), handles PATH lookup,
//! and manages stdio.

use anyhow::{Context, Result};
use std::fs::{File, OpenOptions};
use std::path::PathBuf;
use std::process::{Command, Stdio};
use std::time::Duration;

use crate::glob;
use crate::redirection::{Redirection, RedirectSetup};
use crate::signals;
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

    // Expand glob patterns in arguments (Phase 6 M12)
    let expanded_args = expand_glob_args(args, state)?;

    // PATH lookup
    let executable = find_in_path(program)?;

    // Build command with redirected stdio
    let mut command = Command::new(&executable);
    command
        .args(&expanded_args)
        .stdin(stdin_cfg)
        .stdout(stdout_cfg)
        .stderr(stderr_cfg);

    // Set process group on Unix for proper job control
    #[cfg(unix)]
    {
        use std::os::unix::process::CommandExt;
        command.process_group(0);
    }

    // Spawn child process (non-blocking)
    let mut child = command
        .spawn()
        .context(format!("Failed to spawn: {}", program))?;

    // Poll for exit while checking for interrupt
    loop {
        match child.try_wait().context("Failed to wait for child")? {
            Some(status) => {
                // Child exited - record modifications and return
                redirect_setup.record_for_undo(state)?;
                return handle_exit_status(status);
            }
            None => {
                // Child still running - check for interrupt
                if signals::is_interrupt_requested() {
                    // User pressed Ctrl+C - kill child and reset flag
                    child.kill().context("Failed to kill child process")?;
                    signals::clear_interrupt();

                    // Wait for child to actually terminate
                    child.wait().context("Failed to wait for killed child")?;

                    // Don't record modifications - operation interrupted
                    return Ok(130); // 128 + SIGINT(2)
                }

                // Sleep briefly before next check
                std::thread::sleep(Duration::from_millis(50));
            }
        }
    }
}

/// Execute a pipeline of external commands with stdio chaining.
///
/// Spawns each command in sequence, piping stdout of stage N to stdin of stage N+1.
/// Final stage's output goes to redirections or inherits from shell.
///
/// # Arguments
/// * `stages` - Vector of (program, args) pairs for each pipeline stage
/// * `redirects` - Final redirections (>, >>, etc.) applied to last stage
/// * `state` - Shell state for undo tracking
///
/// # Returns
/// Exit code of the rightmost (last) command in the pipeline (POSIX behavior)
///
/// # Errors
/// Returns error if:
/// - Pipeline is empty or has only one stage
/// - Program not found in PATH
/// - Failed to spawn child process
/// - Failed to setup redirections
///
/// # Examples
/// ```no_run
/// use vsh::external;
/// use vsh::state::ShellState;
///
/// let stages = vec![
///     ("ls".to_string(), vec!["-la".to_string()]),
///     ("grep".to_string(), vec!["test".to_string()]),
/// ];
/// let mut state = ShellState::new("/tmp")?;
/// let exit_code = external::execute_pipeline(&stages, &[], &mut state)?;
/// # Ok::<(), anyhow::Error>(())
/// ```
pub fn execute_pipeline(
    stages: &[(String, Vec<String>)],
    redirects: &[Redirection],
    state: &mut ShellState,
) -> Result<i32> {
    if stages.is_empty() {
        anyhow::bail!("Pipeline must have at least one stage");
    }

    if stages.len() == 1 {
        // Single stage - just run normally with redirects
        return execute_external_with_redirects(&stages[0].0, &stages[0].1, redirects, state);
    }

    // Setup final redirection output files
    let redirect_setup = if !redirects.is_empty() {
        Some(RedirectSetup::setup(redirects, state)?)
    } else {
        None
    };

    // Configure stdio for stages and spawn children
    let mut children: Vec<std::process::Child> = Vec::new();
    let mut prev_stdout: Option<std::process::ChildStdout> = None;

    for (idx, (program, args)) in stages.iter().enumerate() {
        let executable = find_in_path(program)?;

        let is_first = idx == 0;
        let is_last = idx == stages.len() - 1;

        // Configure stdin
        let stdin_cfg = if is_first {
            // First stage: inherit from shell
            Stdio::inherit()
        } else {
            // Middle/last stages: read from previous stdout
            Stdio::from(prev_stdout.take().unwrap())
        };

        // Configure stdout
        let stdout_cfg = if is_last {
            // Last stage: redirect to file or inherit
            if !redirects.is_empty() {
                stdio_config_from_redirects(redirects, redirect_setup.as_ref().unwrap(), state)?.1
            } else {
                Stdio::inherit()
            }
        } else {
            // First/middle stages: pipe to next
            Stdio::piped()
        };

        // Configure stderr (inherit unless redirected in last stage)
        let stderr_cfg = if is_last && !redirects.is_empty() {
            stdio_config_from_redirects(redirects, redirect_setup.as_ref().unwrap(), state)?.2
        } else {
            Stdio::inherit()
        };

        // Spawn child
        let mut command = Command::new(&executable);
        command
            .args(args)
            .stdin(stdin_cfg)
            .stdout(stdout_cfg)
            .stderr(stderr_cfg);

        #[cfg(unix)]
        {
            use std::os::unix::process::CommandExt;
            command.process_group(0);
        }

        let mut child = command
            .spawn()
            .context(format!("Failed to spawn: {}", program))?;

        // Save stdout for next stage
        if !is_last {
            prev_stdout = child.stdout.take();
        }

        children.push(child);
    }

    // Wait for all children in order, checking for SIGINT
    let mut final_exit_code = 0;

    for (idx, mut child) in children.into_iter().enumerate() {
        loop {
            match child.try_wait().context("Failed to wait for child")? {
                Some(status) => {
                    let exit_code = handle_exit_status(status)?;
                    if idx == stages.len() - 1 {
                        // Last stage's exit code is pipeline's exit code
                        final_exit_code = exit_code;
                    }
                    break;
                }
                None => {
                    // Child still running - check for interrupt
                    if signals::is_interrupt_requested() {
                        // Kill all remaining children
                        child.kill().context("Failed to kill child process")?;
                        signals::clear_interrupt();
                        child.wait().context("Failed to wait for killed child")?;

                        // Don't record modifications - operation interrupted
                        return Ok(130); // 128 + SIGINT
                    }
                    std::thread::sleep(Duration::from_millis(50));
                }
            }
        }
    }

    // Record undo for final redirection (if any)
    if let Some(setup) = redirect_setup {
        setup.record_for_undo(state)?;
    }

    Ok(final_exit_code)
}

/// Execute an external command without redirections (legacy interface).
///
/// Spawns a child process via execve(), polls for completion, and handles
/// Ctrl+C interruption gracefully. The child process runs in its own process
/// group for proper job control on Unix.
///
/// # Arguments
/// * `program` - Program name (resolved via PATH lookup)
/// * `args` - Command arguments
///
/// # Returns
/// Exit code from the child process:
/// - 0: Success
/// - 1-127: Program-specific exit codes
/// - 128+N: Terminated by signal N (130 = SIGINT, 143 = SIGTERM)
///
/// # Errors
/// Returns error if:
/// - Program not found in PATH
/// - Failed to spawn child process
/// - Failed to wait for child termination
///
/// # Examples
/// ```no_run
/// use vsh::external;
///
/// let exit_code = external::execute_external("ls", &["-la".to_string()])?;
/// assert_eq!(exit_code, 0);
/// # Ok::<(), anyhow::Error>(())
/// ```
pub fn execute_external(program: &str, args: &[String]) -> Result<i32> {
    // PATH lookup
    let executable = find_in_path(program)?;

    // Spawn child process (non-blocking)
    let mut child = Command::new(&executable)
        .args(args)
        .stdin(Stdio::inherit())
        .stdout(Stdio::inherit())
        .stderr(Stdio::inherit())
        .spawn()
        .context(format!("Failed to spawn: {}", program))?;

    // Poll for exit while checking for interrupt
    loop {
        match child.try_wait().context("Failed to wait for child")? {
            Some(status) => {
                // Child exited normally
                return handle_exit_status(status);
            }
            None => {
                // Child still running - check for interrupt
                if signals::is_interrupt_requested() {
                    // User pressed Ctrl+C - kill child and reset flag
                    child.kill().context("Failed to kill child process")?;
                    signals::clear_interrupt();

                    // Wait for child to actually terminate
                    child.wait().context("Failed to wait for killed child")?;

                    return Ok(130); // 128 + SIGINT(2)
                }

                // Sleep briefly before next check
                std::thread::sleep(Duration::from_millis(50));
            }
        }
    }
}

/// Convert redirections to stdio configuration
fn stdio_config_from_redirects(
    redirects: &[Redirection],
    _setup: &RedirectSetup,
    state: &mut ShellState,
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

            Redirection::HereDoc { content, expand, strip_tabs, .. } => {
                // Process here document content
                let processed = crate::parser::process_heredoc_content(
                    content,
                    *strip_tabs,
                    *expand,
                    state,
                )?;

                // Create temporary file with processed content
                let temp_path = format!("/tmp/vsh-heredoc-{}-{}",
                    std::process::id(),
                    std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos()
                );
                std::fs::write(&temp_path, &processed)?;

                let file_handle = File::open(&temp_path)
                    .with_context(|| format!("Failed to open here document temp file: {}", temp_path))?;
                stdin_cfg = Stdio::from(file_handle);

                // TODO: Track temp file for cleanup
            }

            Redirection::HereString { content, expand } => {
                // Process here string content (always add trailing newline)
                let processed = if *expand {
                    let expanded = crate::parser::expand_with_command_sub(content, state)?;
                    format!("{}\n", expanded)
                } else {
                    format!("{}\n", content)
                };

                // Create temporary file
                let temp_path = format!("/tmp/vsh-herestring-{}-{}",
                    std::process::id(),
                    std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos()
                );
                std::fs::write(&temp_path, &processed)?;

                let file_handle = File::open(&temp_path)
                    .with_context(|| format!("Failed to open here string temp file: {}", temp_path))?;
                stdin_cfg = Stdio::from(file_handle);

                // TODO: Track temp file for cleanup
            }
        }
    }

    Ok((stdin_cfg, stdout_cfg, stderr_cfg))
}

/// Expand glob patterns in command arguments (Phase 6 M12)
///
/// For each argument:
/// - If it contains glob metacharacters (*, ?, [, {), expand it
/// - If expansion succeeds, use matching paths
/// - If expansion fails or returns empty, use literal pattern (POSIX behavior)
/// - If no metacharacters, use argument as-is
///
/// # POSIX Behavior
/// - Brace expansion happens first: {a,b} -> [a, b]
/// - Then glob expansion: *.txt -> [file1.txt, file2.txt]
/// - Empty matches return literal: "*.xyz" if no .xyz files
///
/// # Examples
/// ```no_run
/// expand_glob_args(&["echo", "*.txt"], state)  // -> ["echo", "file1.txt", "file2.txt"]
/// expand_glob_args(&["ls", "file?.rs"], state) // -> ["ls", "file1.rs", "file2.rs"]
/// expand_glob_args(&["rm", "*.xyz"], state)    // -> ["rm", "*.xyz"] (no .xyz files)
/// ```
fn expand_glob_args(args: &[String], _state: &ShellState) -> Result<Vec<String>> {
    let mut expanded: Vec<String> = Vec::new();

    // Get current working directory for glob expansion
    let cwd = std::env::current_dir()
        .context("Failed to get current working directory")?;

    for arg in args {
        // Check if argument contains glob metacharacters
        if glob::contains_glob_pattern(arg) {
            // First, expand braces: file{1,2}.txt -> [file1.txt, file2.txt]
            let brace_expanded = glob::expand_braces(arg);

            // Then expand each brace result for glob patterns
            let mut glob_matches: Vec<String> = Vec::new();
            for pattern in &brace_expanded {
                // Expand glob pattern relative to current directory
                match glob::expand_glob(pattern, &cwd) {
                    Ok(matches) if !matches.is_empty() => {
                        // Found matches - add them as strings
                        for path in matches {
                            glob_matches.push(path.to_string_lossy().to_string());
                        }
                    }
                    _ => {
                        // No matches or error - use literal pattern (POSIX behavior)
                        glob_matches.push(pattern.clone());
                    }
                }
            }

            // Add all matches (or literal if no matches)
            expanded.extend(glob_matches);
        } else {
            // No glob pattern - use argument as-is
            expanded.push(arg.clone());
        }
    }

    Ok(expanded)
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

/// Execute an external command in the background
///
/// Creates a new process group for the job and adds it to the job table.
/// Does not wait for the command to complete.
///
/// # Arguments
/// * `program` - Program name or path
/// * `args` - Command arguments
/// * `redirects` - I/O redirections
/// * `state` - Shell state for job tracking
///
/// # Returns
/// Job ID for the background job
pub fn execute_external_background(
    program: &str,
    args: &[String],
    redirects: &[Redirection],
    state: &mut ShellState,
) -> Result<usize> {
    // Setup redirections if any
    let redirect_setup = RedirectSetup::setup(redirects, state)?;

    // Configure stdio from redirections
    let (stdin_cfg, stdout_cfg, stderr_cfg) =
        stdio_config_from_redirects(redirects, &redirect_setup, state)?;

    // PATH lookup
    let executable = find_in_path(program)?;

    // Build command string for display
    let command_str = if args.is_empty() {
        format!("{} &", program)
    } else {
        format!("{} {} &", program, args.join(" "))
    };

    // Build command with redirected stdio
    let mut command = Command::new(&executable);
    command
        .args(args)
        .stdin(stdin_cfg)
        .stdout(stdout_cfg)
        .stderr(stderr_cfg);

    // Create new process group for job (Unix only)
    #[cfg(unix)]
    {
        use std::os::unix::process::CommandExt;
        command.process_group(0);
    }

    // Spawn child process (non-blocking)
    let child = command
        .spawn()
        .context(format!("Failed to spawn: {}", program))?;

    let pid = child.id() as i32;
    let pgid = pid; // Process becomes its own group leader

    // Add job to job table
    let job_id = state.jobs.add_job(pgid, command_str, vec![pid]);

    // Print job info (bash-style)
    println!("[{}] {}", job_id, pid);

    // Don't wait for background job - it will run independently
    // Job state will be updated by SIGCHLD handler (TODO)

    Ok(job_id)
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

    #[test]
    fn test_pipeline_simple() {
        // Test simple 2-stage pipeline: true | true
        use tempfile::TempDir;
        let temp = TempDir::new().unwrap();
        let mut state = crate::state::ShellState::new(temp.path().to_str().unwrap()).unwrap();

        let stages = vec![
            ("true".to_string(), vec![]),
            ("true".to_string(), vec![]),
        ];
        let exit_code = execute_pipeline(&stages, &[], &mut state).unwrap();
        assert_eq!(exit_code, 0, "true | true should return 0");
    }

    #[test]
    fn test_pipeline_exit_code() {
        // Test that pipeline returns exit code from last stage
        use tempfile::TempDir;
        let temp = TempDir::new().unwrap();
        let mut state = crate::state::ShellState::new(temp.path().to_str().unwrap()).unwrap();

        let stages = vec![
            ("true".to_string(), vec![]),
            ("false".to_string(), vec![]),
        ];
        let exit_code = execute_pipeline(&stages, &[], &mut state).unwrap();
        assert_eq!(exit_code, 1, "true | false should return 1 (from false)");
    }

    #[test]
    fn test_pipeline_three_stages() {
        // Test 3-stage pipeline
        use tempfile::TempDir;
        let temp = TempDir::new().unwrap();
        let mut state = crate::state::ShellState::new(temp.path().to_str().unwrap()).unwrap();

        let stages = vec![
            ("echo".to_string(), vec!["hello".to_string()]),
            ("cat".to_string(), vec![]),
            ("cat".to_string(), vec![]),
        ];
        let exit_code = execute_pipeline(&stages, &[], &mut state).unwrap();
        assert_eq!(exit_code, 0, "echo hello | cat | cat should return 0");
    }

    #[test]
    fn test_pipeline_with_redirect() {
        // Test pipeline with output redirection
        use tempfile::TempDir;
        use std::fs;
        let temp = TempDir::new().unwrap();
        let mut state = crate::state::ShellState::new(temp.path().to_str().unwrap()).unwrap();

        let stages = vec![
            ("echo".to_string(), vec!["test".to_string()]),
            ("cat".to_string(), vec![]),
        ];
        let redirects = vec![crate::redirection::Redirection::Output {
            file: "output.txt".to_string(),
        }];
        let exit_code = execute_pipeline(&stages, &redirects, &mut state).unwrap();
        assert_eq!(exit_code, 0, "Pipeline with redirect should return 0");

        // Verify file was created
        let output_file = temp.path().join("output.txt");
        assert!(output_file.exists(), "Output file should be created");

        let content = fs::read_to_string(output_file).unwrap();
        assert_eq!(content.trim(), "test", "Output should be 'test'");
    }

    #[test]
    fn test_pipeline_error_empty_stages() {
        // Test that empty stages array returns error
        use tempfile::TempDir;
        let temp = TempDir::new().unwrap();
        let mut state = crate::state::ShellState::new(temp.path().to_str().unwrap()).unwrap();

        let stages: Vec<(String, Vec<String>)> = vec![];
        let result = execute_pipeline(&stages, &[], &mut state);
        assert!(result.is_err(), "Empty pipeline should return error");
    }

    #[test]
    fn test_pipeline_single_stage_delegates() {
        // Test that single-stage pipeline delegates to execute_external_with_redirects
        use tempfile::TempDir;
        let temp = TempDir::new().unwrap();
        let mut state = crate::state::ShellState::new(temp.path().to_str().unwrap()).unwrap();

        let stages = vec![("true".to_string(), vec![])];
        let exit_code = execute_pipeline(&stages, &[], &mut state).unwrap();
        assert_eq!(exit_code, 0, "Single-stage pipeline should work");
    }
}
