// SPDX-License-Identifier: PMPL-1.0-or-later
//! I/O Redirection Support
//!
//! Implements POSIX-compliant redirections for both built-in and external commands.
//! All file modifications are reversible via the undo system.

use anyhow::{Context, Result};
use std::collections::HashSet;
use std::fs::{self, File, OpenOptions};
use std::io::{Read, Write};
use std::path::{Path, PathBuf};

use crate::state::ShellState;

/// Captures stdout and applies redirections
///
/// Used for built-in commands that print to stdout.
/// Executes the provided closure, captures its stdout output,
/// and writes to redirection targets if specified.
///
/// The closure receives mutable access to ShellState for command execution.
pub fn capture_and_redirect<F>(
    redirects: &[Redirection],
    state: &mut ShellState,
    mut f: F,
) -> Result<()>
where
    F: FnMut(&mut ShellState) -> Result<()>,
{
    if redirects.is_empty() {
        // No redirections - execute normally
        return f(state);
    }

    // Resolve redirect file paths before capturing stdout
    // (state.resolve_path needs immutable access)
    // IMPORTANT: Expand variables in file paths first (fixes M11 edge case)
    let resolved_redirects: Vec<(Redirection, PathBuf)> = redirects
        .iter()
        .filter_map(|r| match r {
            Redirection::Output { file } => {
                let expanded = crate::parser::expand_variables(file, state);
                Some((r.clone(), state.resolve_path(&expanded)))
            }
            Redirection::Append { file } => {
                let expanded = crate::parser::expand_variables(file, state);
                Some((r.clone(), state.resolve_path(&expanded)))
            }
            Redirection::BothOutput { file } => {
                let expanded = crate::parser::expand_variables(file, state);
                Some((r.clone(), state.resolve_path(&expanded)))
            }
            _ => None,
        })
        .collect();

    // Setup redirections (validates, opens files, records original state)
    let redirect_setup = RedirectSetup::setup(redirects, state)?;

    // Capture stdout
    let mut buffer = gag::BufferRedirect::stdout()?;

    // Execute command with mutable state
    f(state)?;

    // Get captured output
    let mut output = String::new();
    buffer.read_to_string(&mut output)?;
    drop(buffer); // Release stdout

    // Write to redirect targets
    for (redirect, path) in resolved_redirects {
        match redirect {
            Redirection::Output { .. } | Redirection::BothOutput { .. } => {
                fs::write(&path, &output)
                    .with_context(|| format!("Failed to write to: {}", path.display()))?;
            }

            Redirection::Append { .. } => {
                let mut f = OpenOptions::new()
                    .create(true)
                    .append(true)
                    .open(&path)
                    .with_context(|| format!("Failed to open for append: {}", path.display()))?;
                f.write_all(output.as_bytes())?;
            }

            _ => {} // Filtered out above
        }
    }

    // Record modifications for undo
    redirect_setup.record_for_undo(state)?;

    Ok(())
}

/// I/O redirection operator for commands.
///
/// Supports POSIX-standard redirections and bash extensions. All file
/// modifications are tracked for undo support.
///
/// # Examples
/// ```
/// use vsh::redirection::Redirection;
///
/// let redirect = Redirection::Output { file: "output.txt".to_string() };
/// // Used with commands: ls > output.txt
/// ```
#[derive(Debug, Clone, PartialEq)]
pub enum Redirection {
    /// Redirect stdout to file (truncate): `> file`
    Output { file: String },

    /// Append stdout to file: `>> file`
    Append { file: String },

    /// Redirect stdin from file: `< file`
    Input { file: String },

    /// Redirect stderr to file (truncate): `2> file`
    ErrorOutput { file: String },

    /// Append stderr to file: `2>> file`
    ErrorAppend { file: String },

    /// Redirect stderr to stdout's target: `2>&1`
    ErrorToOutput,

    /// Redirect both stdout and stderr to file (bash extension): `&> file`
    BothOutput { file: String },

    /// Here document: `<< DELIMITER`
    HereDoc {
        delimiter: String,
        content: String,
        expand: bool,
        strip_tabs: bool,
    },

    /// Here string: `<<< string`
    HereString {
        content: String,
        expand: bool,
    },
}

/// Type of file modification for undo tracking.
///
/// Records how a file was changed by a redirection so the change can be
/// reversed. Each variant stores the data needed for reversal.
///
/// # Examples
/// ```no_run
/// use vsh::redirection::FileModification;
/// use std::path::PathBuf;
///
/// let mod_op = FileModification::Created { path: PathBuf::from("new.txt") };
/// mod_op.reverse()?;  // Deletes the created file
/// # Ok::<(), anyhow::Error>(())
/// ```
#[derive(Debug, Clone)]
pub enum FileModification {
    /// File was created (didn't exist before)
    Created { path: PathBuf },

    /// File was truncated (existed before)
    Truncated {
        path: PathBuf,
        original_content: Vec<u8>,
    },

    /// File was appended to
    Appended {
        path: PathBuf,
        original_size: u64,
    },
}

impl FileModification {
    /// Get the path affected by this modification
    pub fn path(&self) -> &Path {
        match self {
            FileModification::Created { path } => path,
            FileModification::Truncated { path, .. } => path,
            FileModification::Appended { path, .. } => path,
        }
    }

    /// Reverse this file modification (for undo)
    pub fn reverse(&self) -> Result<()> {
        match self {
            FileModification::Created { path } => {
                fs::remove_file(path)
                    .with_context(|| format!("Failed to remove created file: {}", path.display()))?;
            }

            FileModification::Truncated {
                path,
                original_content,
            } => {
                fs::write(path, original_content)
                    .with_context(|| format!("Failed to restore truncated file: {}", path.display()))?;
            }

            FileModification::Appended {
                path,
                original_size,
            } => {
                let file = OpenOptions::new()
                    .write(true)
                    .open(path)
                    .with_context(|| format!("Failed to open appended file: {}", path.display()))?;

                file.set_len(*original_size)
                    .with_context(|| {
                        format!("Failed to truncate appended file: {}", path.display())
                    })?;
            }
        }
        Ok(())
    }
}

/// Redirection setup and cleanup handler.
///
/// Manages file handles opened for redirections and tracks modifications
/// for undo support. Ensures files are properly closed via Drop.
///
/// # Examples
/// ```no_run
/// use vsh::redirection::{Redirection, RedirectSetup};
/// use vsh::state::ShellState;
///
/// let mut state = ShellState::new("/tmp/test")?;
/// let redirects = vec![Redirection::Output { file: "out.txt".to_string() }];
/// let setup = RedirectSetup::setup(&redirects, &mut state)?;
/// # Ok::<(), anyhow::Error>(())
/// ```
pub struct RedirectSetup {
    /// Files opened for redirection (need cleanup)
    pub opened_files: Vec<File>,

    /// File modifications made (for undo)
    pub modifications: Vec<FileModification>,
}

impl RedirectSetup {
    /// Create a new empty redirection setup
    pub fn new() -> Self {
        Self {
            opened_files: Vec::new(),
            modifications: Vec::new(),
        }
    }

    /// Prepare file redirections before command execution
    ///
    /// Validates all redirections, opens files, and records original state for undo.
    /// Fails atomically if any redirection is invalid.
    pub fn setup(redirects: &[Redirection], state: &ShellState) -> Result<Self> {
        // Validate all redirections first (fail fast)
        validate_redirections(redirects, state)?;

        let mut setup = Self::new();

        for redirect in redirects {
            match redirect {
                Redirection::Output { file } => {
                    setup.setup_output_redirect(file, state, false)?;
                }

                Redirection::Append { file } => {
                    setup.setup_output_redirect(file, state, true)?;
                }

                Redirection::ErrorOutput { file } => {
                    setup.setup_output_redirect(file, state, false)?;
                }

                Redirection::ErrorAppend { file } => {
                    setup.setup_output_redirect(file, state, true)?;
                }

                Redirection::BothOutput { file } => {
                    setup.setup_output_redirect(file, state, false)?;
                }

                Redirection::Input { file } => {
                    setup.setup_input_redirect(file, state)?;
                }

                Redirection::ErrorToOutput => {
                    // Handled at execution time (fd duplication)
                }

                Redirection::HereDoc { .. } | Redirection::HereString { .. } => {
                    // Handled by external command execution (creates temp file)
                }
            }
        }

        Ok(setup)
    }

    /// Setup output redirection (> or >>)
    fn setup_output_redirect(
        &mut self,
        file: &str,
        state: &ShellState,
        append: bool,
    ) -> Result<()> {
        // Expand variables in file path first (M11 edge case fix)
        let expanded = crate::parser::expand_variables(file, state);
        let path = state.resolve_path(&expanded);

        // Record original state for undo
        if path.exists() {
            if append {
                let metadata = fs::metadata(&path)
                    .with_context(|| format!("Failed to stat file: {}", path.display()))?;

                self.modifications
                    .push(FileModification::Appended {
                        path: path.clone(),
                        original_size: metadata.len(),
                    });
            } else {
                // Truncate - save original content
                let original_content = fs::read(&path)
                    .with_context(|| format!("Failed to read file for backup: {}", path.display()))?;

                // Warn if file is large
                if original_content.len() > 10 * 1024 * 1024 {
                    eprintln!(
                        "Warning: Saving {:.1}MB file for undo. This may use significant memory.",
                        original_content.len() as f64 / (1024.0 * 1024.0)
                    );
                }

                self.modifications
                    .push(FileModification::Truncated {
                        path: path.clone(),
                        original_content,
                    });
            }
        } else {
            // File doesn't exist - will be created
            self.modifications.push(FileModification::Created {
                path: path.clone(),
            });
        }

        // Open file for writing
        let file = if append {
            OpenOptions::new()
                .create(true)
                .append(true)
                .open(&path)
                .with_context(|| format!("Failed to open file for append: {}", path.display()))?
        } else {
            File::create(&path)
                .with_context(|| format!("Failed to create file: {}", path.display()))?
        };

        self.opened_files.push(file);

        Ok(())
    }

    /// Setup input redirection (<)
    fn setup_input_redirect(&mut self, file: &str, state: &ShellState) -> Result<()> {
        // Expand variables in file path first (M11 edge case fix)
        let expanded = crate::parser::expand_variables(file, state);
        let path = state.resolve_path(&expanded);

        // Validate file exists and is readable
        if !path.exists() {
            anyhow::bail!("Input file does not exist: {}", path.display());
        }

        if !path.is_file() {
            anyhow::bail!("Input redirection target is not a file: {}", path.display());
        }

        // Open for reading
        let file = File::open(&path)
            .with_context(|| format!("Failed to open input file: {}", path.display()))?;

        self.opened_files.push(file);

        Ok(())
    }

    /// Get file at index (for manual fd setup)
    pub fn get_file(&mut self, index: usize) -> Option<&mut File> {
        self.opened_files.get_mut(index)
    }

    /// Record all modifications as undoable operations
    pub fn record_for_undo(self, state: &mut ShellState) -> Result<()> {
        use crate::state::{Operation, OperationType};

        // Clone modifications to avoid moving out of Drop type
        for modification in self.modifications.clone() {
            let (op_type, path, undo_data) = match modification {
                FileModification::Created { path } => {
                    // File was created by redirection
                    let path_str = path.to_string_lossy().to_string();
                    (OperationType::CreateFile, path_str, None)
                }

                FileModification::Truncated {
                    path,
                    original_content,
                } => {
                    // File was truncated by > redirection
                    let path_str = path.to_string_lossy().to_string();
                    (
                        OperationType::FileTruncated,
                        path_str,
                        Some(original_content),
                    )
                }

                FileModification::Appended {
                    path,
                    original_size,
                } => {
                    // File was appended to by >> redirection
                    let path_str = path.to_string_lossy().to_string();
                    // Encode size as bytes
                    let size_bytes = original_size.to_le_bytes().to_vec();
                    (OperationType::FileAppended, path_str, Some(size_bytes))
                }
            };

            let mut op = Operation::new(op_type, path, state.active_transaction.as_ref().map(|t| t.id));
            if let Some(data) = undo_data {
                op = op.with_undo_data(data);
            }

            state.record_operation(op);
        }

        Ok(())
    }
}

impl Drop for RedirectSetup {
    fn drop(&mut self) {
        // Files are automatically closed when dropped
        // This ensures cleanup even on panic
    }
}

/// Validate all redirections before execution
///
/// Checks for:
/// - Conflicting redirections (e.g., `> file1 > file2`)
/// - Input/output to same file
/// - Missing redirect targets
/// - Permission issues
/// - Parent directory existence
fn validate_redirections(redirects: &[Redirection], state: &ShellState) -> Result<()> {
    if redirects.is_empty() {
        return Ok(());
    }

    // Check for conflicting stdout redirections
    let stdout_redirects: Vec<_> = redirects
        .iter()
        .filter(|r| {
            matches!(
                r,
                Redirection::Output { .. }
                    | Redirection::Append { .. }
                    | Redirection::BothOutput { .. }
            )
        })
        .collect();

    if stdout_redirects.len() > 1 {
        anyhow::bail!("Cannot redirect stdout multiple times");
    }

    // Check for conflicting stderr redirections
    let stderr_redirects: Vec<_> = redirects
        .iter()
        .filter(|r| {
            matches!(
                r,
                Redirection::ErrorOutput { .. }
                    | Redirection::ErrorAppend { .. }
                    | Redirection::ErrorToOutput
                    | Redirection::BothOutput { .. }
            )
        })
        .collect();

    if stderr_redirects.len() > 1 {
        anyhow::bail!("Cannot redirect stderr multiple times");
    }

    // Check for input/output to same file (data race)
    validate_no_input_output_conflict(redirects, state)?;

    // Validate each redirection's target
    for redirect in redirects {
        match redirect {
            Redirection::Input { file } => {
                validate_input_file(file, state)?;
            }

            Redirection::Output { file }
            | Redirection::Append { file }
            | Redirection::ErrorOutput { file }
            | Redirection::ErrorAppend { file }
            | Redirection::BothOutput { file } => {
                validate_output_file(file, state)?;
            }

            Redirection::ErrorToOutput => {
                // No file validation needed
            }

            Redirection::HereDoc { .. } | Redirection::HereString { .. } => {
                // No file validation needed (uses temp files)
            }
        }
    }

    Ok(())
}

/// Check for input/output conflict (same file)
fn validate_no_input_output_conflict(
    redirects: &[Redirection],
    state: &ShellState,
) -> Result<()> {
    let input_files: HashSet<PathBuf> = redirects
        .iter()
        .filter_map(|r| match r {
            Redirection::Input { file } => {
                let expanded = crate::parser::expand_variables(file, state);
                Some(state.resolve_path(&expanded))
            }
            _ => None,
        })
        .collect();

    let output_files: HashSet<PathBuf> = redirects
        .iter()
        .filter_map(|r| match r {
            Redirection::Output { file }
            | Redirection::Append { file }
            | Redirection::ErrorOutput { file }
            | Redirection::ErrorAppend { file }
            | Redirection::BothOutput { file } => {
                let expanded = crate::parser::expand_variables(file, state);
                Some(state.resolve_path(&expanded))
            }
            _ => None,
        })
        .collect();

    // Find intersection
    let conflicts: Vec<_> = input_files.intersection(&output_files).collect();

    if !conflicts.is_empty() {
        anyhow::bail!(
            "Cannot redirect input and output to the same file: {}",
            conflicts[0].display()
        );
    }

    Ok(())
}

/// Validate input redirection target
fn validate_input_file(file: &str, state: &ShellState) -> Result<()> {
    // Expand variables in file path first (M11 edge case fix)
    let expanded = crate::parser::expand_variables(file, state);
    let path = state.resolve_path(&expanded);

    if !path.exists() {
        anyhow::bail!("Input file does not exist: {}", path.display());
    }

    if !path.is_file() {
        anyhow::bail!("Input redirection target is not a file: {}", path.display());
    }

    // Check readable (Unix only)
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        let metadata = fs::metadata(&path)
            .with_context(|| format!("Failed to stat input file: {}", path.display()))?;

        let mode = metadata.permissions().mode();
        if mode & 0o400 == 0 {
            anyhow::bail!("Input file is not readable: {}", path.display());
        }
    }

    Ok(())
}

/// Validate output redirection target
fn validate_output_file(file: &str, state: &ShellState) -> Result<()> {
    // Expand variables in file path first (M11 edge case fix)
    let expanded = crate::parser::expand_variables(file, state);
    let path = state.resolve_path(&expanded);

    // Check parent directory exists
    if let Some(parent) = path.parent() {
        if !parent.exists() {
            anyhow::bail!("Parent directory does not exist: {}", parent.display());
        }

        if !parent.is_dir() {
            anyhow::bail!("Parent is not a directory: {}", parent.display());
        }

        // Check parent is writable (Unix only)
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            let metadata = fs::metadata(parent)
                .with_context(|| format!("Failed to stat parent directory: {}", parent.display()))?;

            let mode = metadata.permissions().mode();
            if mode & 0o200 == 0 {
                anyhow::bail!("Parent directory is not writable: {}", parent.display());
            }
        }
    }

    // If file exists, check it's writable
    if path.exists() {
        if !path.is_file() {
            anyhow::bail!("Output redirection target is not a file: {}", path.display());
        }

        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            let metadata = fs::metadata(&path)
                .with_context(|| format!("Failed to stat output file: {}", path.display()))?;

            let mode = metadata.permissions().mode();
            if mode & 0o200 == 0 {
                anyhow::bail!("Output file is not writable: {}", path.display());
            }
        }
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::state::ShellState;
    use std::fs;
    use tempfile::TempDir;

    fn test_state(root: &Path) -> ShellState {
        ShellState::new(root.to_str().unwrap()).unwrap()
    }

    #[test]
    fn test_redirection_equality() {
        let r1 = Redirection::Output {
            file: "test.txt".to_string(),
        };
        let r2 = Redirection::Output {
            file: "test.txt".to_string(),
        };
        assert_eq!(r1, r2);
    }

    #[test]
    fn test_validate_output_file_nonexistent_parent() {
        let temp = TempDir::new().unwrap();
        let state = test_state(temp.path());

        let result = validate_output_file("nonexistent/file.txt", &state);
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("Parent directory does not exist"));
    }

    #[test]
    fn test_validate_input_file_not_exists() {
        let temp = TempDir::new().unwrap();
        let state = test_state(temp.path());

        let result = validate_input_file("nonexistent.txt", &state);
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("Input file does not exist"));
    }

    #[test]
    fn test_validate_input_output_conflict() {
        let temp = TempDir::new().unwrap();
        let state = test_state(temp.path());

        let redirects = vec![
            Redirection::Input {
                file: "file.txt".to_string(),
            },
            Redirection::Output {
                file: "file.txt".to_string(),
            },
        ];

        let result = validate_no_input_output_conflict(&redirects, &state);
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("Cannot redirect input and output to the same file"));
    }

    #[test]
    fn test_validate_multiple_stdout_redirects() {
        let temp = TempDir::new().unwrap();
        let state = test_state(temp.path());

        let redirects = vec![
            Redirection::Output {
                file: "file1.txt".to_string(),
            },
            Redirection::Output {
                file: "file2.txt".to_string(),
            },
        ];

        let result = validate_redirections(&redirects, &state);
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("Cannot redirect stdout multiple times"));
    }

    #[test]
    fn test_file_modification_path() {
        let path = PathBuf::from("/tmp/test.txt");
        let modification = FileModification::Created { path: path.clone() };

        assert_eq!(modification.path(), path.as_path());
    }

    #[test]
    fn test_redirect_setup_new() {
        let setup = RedirectSetup::new();
        assert_eq!(setup.opened_files.len(), 0);
        assert_eq!(setup.modifications.len(), 0);
    }

    #[test]
    fn test_setup_output_redirect_creates_file() {
        let temp = TempDir::new().unwrap();
        let state = test_state(temp.path());
        let mut setup = RedirectSetup::new();

        setup
            .setup_output_redirect("newfile.txt", &state, false)
            .unwrap();

        assert_eq!(setup.modifications.len(), 1);
        assert!(matches!(
            &setup.modifications[0],
            FileModification::Created { .. }
        ));
        assert_eq!(setup.opened_files.len(), 1);
    }

    #[test]
    fn test_setup_output_redirect_truncates_existing() {
        let temp = TempDir::new().unwrap();
        let state = test_state(temp.path());

        // Create existing file
        let file_path = temp.path().join("existing.txt");
        fs::write(&file_path, b"original content").unwrap();

        let mut setup = RedirectSetup::new();
        setup
            .setup_output_redirect("existing.txt", &state, false)
            .unwrap();

        assert_eq!(setup.modifications.len(), 1);
        assert!(matches!(
            &setup.modifications[0],
            FileModification::Truncated { .. }
        ));

        if let FileModification::Truncated { original_content, .. } = &setup.modifications[0] {
            assert_eq!(original_content, b"original content");
        }
    }

    #[test]
    fn test_setup_append_redirect() {
        let temp = TempDir::new().unwrap();
        let state = test_state(temp.path());

        // Create existing file
        let file_path = temp.path().join("existing.txt");
        fs::write(&file_path, b"original").unwrap();

        let mut setup = RedirectSetup::new();
        setup
            .setup_output_redirect("existing.txt", &state, true)
            .unwrap();

        assert_eq!(setup.modifications.len(), 1);
        assert!(matches!(
            &setup.modifications[0],
            FileModification::Appended { .. }
        ));

        if let FileModification::Appended { original_size, .. } = &setup.modifications[0] {
            assert_eq!(*original_size, 8); // "original" = 8 bytes
        }
    }

    #[test]
    fn test_file_modification_reverse_created() {
        let temp = TempDir::new().unwrap();
        let file_path = temp.path().join("created.txt");

        // Create file
        fs::write(&file_path, b"test").unwrap();
        assert!(file_path.exists());

        // Reverse (delete)
        let modification = FileModification::Created {
            path: file_path.clone(),
        };
        modification.reverse().unwrap();

        assert!(!file_path.exists());
    }

    #[test]
    fn test_file_modification_reverse_truncated() {
        let temp = TempDir::new().unwrap();
        let file_path = temp.path().join("truncated.txt");

        // Create with original content
        fs::write(&file_path, b"original").unwrap();

        // Simulate truncation
        fs::write(&file_path, b"new").unwrap();

        // Reverse (restore original)
        let modification = FileModification::Truncated {
            path: file_path.clone(),
            original_content: b"original".to_vec(),
        };
        modification.reverse().unwrap();

        let restored = fs::read(&file_path).unwrap();
        assert_eq!(restored, b"original");
    }

    #[test]
    fn test_file_modification_reverse_appended() {
        let temp = TempDir::new().unwrap();
        let file_path = temp.path().join("appended.txt");

        // Create original file
        fs::write(&file_path, b"original").unwrap();
        let original_size = 8;

        // Simulate append
        let mut file = OpenOptions::new().append(true).open(&file_path).unwrap();
        file.write_all(b" appended").unwrap();
        drop(file);

        // Verify appended
        let content = fs::read_to_string(&file_path).unwrap();
        assert_eq!(content, "original appended");

        // Reverse (truncate to original size)
        let modification = FileModification::Appended {
            path: file_path.clone(),
            original_size,
        };
        modification.reverse().unwrap();

        let restored = fs::read_to_string(&file_path).unwrap();
        assert_eq!(restored, "original");
    }
}
