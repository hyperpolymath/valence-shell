// SPDX-License-Identifier: MPL-2.0
// Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//! I/O Redirection Support
//!
//! Implements POSIX-compliant redirections for both built-in and external commands.
//! All file modifications are reversible via the undo system.

use anyhow::{Context, Result};
use std::collections::HashSet;
use std::fs::{self, File, OpenOptions};
use std::io::{Read, Seek, Write};
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
    let resolved_redirects: Vec<(usize, PathBuf)> = redirects
        .iter()
        .enumerate()
        .filter_map(|(index, r)| match r {
            Redirection::Output { file }
            | Redirection::Append { file }
            | Redirection::BothOutput { file } => {
                let expanded = crate::parser::expand_variables(file, state);
                Some((index, state.resolve_path(&expanded)))
            }
            _ => None,
        })
        .collect();

    // Set the redirections up (validate, open the files, save their
    // original state), run the command, and record what the set-up
    // changed, whatever becomes of the command.
    RedirectSetup::run(redirects, state, |redirect_setup, state| {
        // Capture stdout
        let mut buffer = gag::BufferRedirect::stdout()?;

        // Execute command with mutable state
        f(state)?;

        // Get captured output
        let mut output = String::new();
        buffer.read_to_string(&mut output)?;
        drop(buffer); // Release stdout

        // Write to the redirect targets, through the files the set-up
        // opened and checked. Opening the names a second time here went
        // round that check: a name given to another file in between (a
        // hard link to a file outside the root, say) was opened and
        // overwritten.
        for (index, path) in resolved_redirects {
            redirect_setup
                .handle(index)?
                .write_all(output.as_bytes())
                .with_context(|| format!("Failed to write to: {}", path.display()))?;
        }

        Ok(())
    })
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
    HereString { content: String, expand: bool },
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
    Appended { path: PathBuf, original_size: u64 },
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
                fs::remove_file(path).with_context(|| {
                    format!("Failed to remove created file: {}", path.display())
                })?;
            }

            FileModification::Truncated {
                path,
                original_content,
            } => {
                fs::write(path, original_content).with_context(|| {
                    format!("Failed to restore truncated file: {}", path.display())
                })?;
            }

            FileModification::Appended {
                path,
                original_size,
            } => {
                let file = OpenOptions::new()
                    .write(true)
                    .open(path)
                    .with_context(|| format!("Failed to open appended file: {}", path.display()))?;

                file.set_len(*original_size).with_context(|| {
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

    /// For each redirection given to [`Self::setup`], in order, the place
    /// in `opened_files` of the file opened for it, if it names a file.
    targets: Vec<Option<usize>>,

    /// The `>` targets that are opened and saved but not emptied yet: the
    /// place of each in `opened_files` and of its record in
    /// `modifications`. See [`Self::truncate_pending`].
    pending_truncations: Vec<(usize, usize)>,
}

/// `path`, an absolute path inside the session root, as the root-relative
/// form the history stores. Recording the absolute path made undo resolve
/// it under the root a second time and fail.
fn rooted_path(state: &ShellState, path: &Path) -> String {
    match state.contained_abs(path) {
        Ok(relative) => relative.to_string_lossy().into_owned(),
        Err(_) => path.to_string_lossy().into_owned(),
    }
}

/// The file a redirection writes to, opened beneath the session root
/// without truncating it, and whether this call created it.
///
/// An existing file is opened first. Only if there is none is one created,
/// and then exclusively, so a file that another program makes in between
/// is never taken for a new one (its content would be lost, and `undo`
/// would delete it).
fn open_redirect_target(
    root: &cap_std::fs::Dir,
    contained: &Path,
    append: bool,
) -> std::io::Result<(cap_std::fs::File, bool)> {
    use std::io::ErrorKind;

    match open_existing_target(root, contained, append) {
        Ok(file) => Ok((file, false)),
        Err(e) if e.kind() == ErrorKind::NotFound => {
            let mut options = cap_std::fs::OpenOptions::new();
            if append {
                options.append(true);
            } else {
                options.write(true);
            }
            options.create_new(true);
            match root.open_with(contained, &options) {
                Ok(file) => Ok((file, true)),
                Err(e) if e.kind() == ErrorKind::AlreadyExists => Err(std::io::Error::new(
                    ErrorKind::AlreadyExists,
                    "the name is a symbolic link to a file that does not exist, or another \
                     program created the file at the same moment; nothing was written",
                )),
                Err(e) => Err(e),
            }
        }
        Err(e) => Err(e),
    }
}

/// An existing redirect target, opened without truncating it.
///
/// For `>` it is opened for reading too, so that the bytes saved for undo
/// are read from the very file that is then truncated, and, where the
/// system has it, with `O_NOATIME`, so that saving them does not change the
/// file's access time (see [`crate::fs_pure`]).
fn open_existing_target(
    root: &cap_std::fs::Dir,
    contained: &Path,
    append: bool,
) -> std::io::Result<cap_std::fs::File> {
    let mut options = cap_std::fs::OpenOptions::new();
    if append {
        options.append(true);
        return root.open_with(contained, &options);
    }
    options.read(true).write(true);
    #[cfg(target_os = "linux")]
    {
        use cap_std::fs::OpenOptionsExt;
        let mut pure = options.clone();
        pure.custom_flags(libc::O_NOATIME);
        match root.open_with(contained, &pure) {
            // Not the owner: the kernel refuses the flag. Open without it.
            Err(e) if e.raw_os_error() == Some(libc::EPERM) => {}
            other => return other,
        }
    }
    root.open_with(contained, &options)
}

/// Refuse an open redirect target that must not be written to. `shown` is
/// its path, for the message.
fn check_writable_target(meta: &cap_std::fs::Metadata, shown: &Path) -> Result<()> {
    if !meta.is_file() {
        anyhow::bail!(
            "Output redirection target is not a file: {}",
            shown.display()
        );
    }
    // A file with more than one hard link has other names, which may lie
    // outside the session root. Writing to it would change what those
    // names hold, so it is refused.
    let links = cap_fs_ext::MetadataExt::nlink(meta);
    if links > 1 {
        anyhow::bail!(
            "Cannot redirect to {}: the file has {} hard links, and writing to it \
             would change the data under its other names too",
            shown.display(),
            links
        )
    }
    Ok(())
}

/// The existing file at `contained` (beneath the session root `root`),
/// opened for reading and writing without truncating it, and checked while
/// open as a redirection's target is: it must be a regular file with no
/// other name. `shown` is its path, for the messages.
pub(crate) fn open_checked_target(
    root: &cap_std::fs::Dir,
    contained: &Path,
    shown: &Path,
) -> Result<cap_std::fs::File> {
    let target = open_existing_target(root, contained, false)
        .with_context(|| format!("Failed to open file for writing: {}", shown.display()))?;
    let meta = target
        .metadata()
        .with_context(|| format!("Failed to stat file: {}", shown.display()))?;
    check_writable_target(&meta, shown)?;
    Ok(target)
}

/// Empty the file at `contained` (beneath the session root `root`) and
/// return what it held, for redoing a `>` redirection. `shown` is its path,
/// for the messages.
///
/// As for the redirection itself, the file is opened once, checked, read
/// and then truncated through that one handle, so the bytes returned are
/// those of the file that was emptied.
pub(crate) fn truncate_keeping(
    root: &cap_std::fs::Dir,
    contained: &Path,
    shown: &Path,
) -> Result<Vec<u8>> {
    let mut target = open_checked_target(root, contained, shown)?;
    let mut original_content = Vec::new();
    target
        .read_to_end(&mut original_content)
        .with_context(|| format!("Failed to read file for backup: {}", shown.display()))?;
    target
        .set_len(0)
        .with_context(|| format!("Failed to truncate: {}", shown.display()))?;
    Ok(original_content)
}

/// The absolute path of the file that `contained` names once the links in
/// it are followed, checked to be the file that was opened (`opened` is the
/// open file's metadata).
///
/// # Errors
///
/// Fails if the name leads to another file than the one opened (it was
/// changed in between), or if the real path is not valid UTF-8, which the
/// history cannot store.
fn changed_file(
    state: &ShellState,
    contained: &Path,
    opened: &cap_std::fs::Metadata,
) -> Result<PathBuf> {
    use cap_fs_ext::MetadataExt;

    let root = state.root_dir();
    let real = root
        .canonicalize(contained)
        .context("Failed to resolve the path of the opened file")?;
    let named = root
        .symlink_metadata(&real)
        .context("Failed to stat the opened file by its path")?;
    if named.dev() != opened.dev() || named.ino() != opened.ino() {
        anyhow::bail!("the name was given to another file while it was being opened");
    }
    if real.to_str().is_none() {
        anyhow::bail!(
            "its real path ({}) is not valid UTF-8, so it could not be recorded for undo; \
             nothing was written",
            real.display()
        );
    }
    Ok(state.session_root().join(real))
}

impl Default for RedirectSetup {
    fn default() -> Self {
        Self::new()
    }
}

impl RedirectSetup {
    /// Create a new empty redirection setup
    pub fn new() -> Self {
        Self {
            opened_files: Vec::new(),
            modifications: Vec::new(),
            targets: Vec::new(),
            pending_truncations: Vec::new(),
        }
    }

    /// Set up `redirects`, run `body` with them, and record what the
    /// set-up changed, whatever becomes of `body`.
    ///
    /// A `>` target is emptied when it is set up. That used to be recorded
    /// only when the command went well: a built-in that failed, a command
    /// that could not be found or was interrupted, and every background
    /// command left the file emptied with nothing for `undo` to restore.
    /// Going through this function, a caller cannot leave the record out.
    ///
    /// # Errors
    ///
    /// Fails if the set-up fails (then nothing was changed and `body` does
    /// not run), if `body` fails, or if the record cannot be made.
    pub fn run<T>(
        redirects: &[Redirection],
        state: &mut ShellState,
        body: impl FnOnce(&Self, &mut ShellState) -> Result<T>,
    ) -> Result<T> {
        let setup = Self::setup(redirects, state)?;
        let outcome = body(&setup, state);
        let recorded = setup.record_for_undo(state);
        let value = outcome?;
        recorded?;
        Ok(value)
    }

    /// A second handle on the file opened for the redirection at `index`
    /// of the list given to [`Self::setup`].
    ///
    /// Whatever writes or reads the redirected stream uses this handle. The
    /// file was opened once, beneath the session root, and checked while
    /// open. Opening its name again would go round both: the name can be
    /// given to another file in between.
    ///
    /// # Errors
    ///
    /// Fails if that redirection does not name a file, or the handle cannot
    /// be duplicated.
    pub fn handle(&self, index: usize) -> Result<File> {
        let file = self
            .targets
            .get(index)
            .copied()
            .flatten()
            .and_then(|place| self.opened_files.get(place))
            .context("No file was opened for this redirection")?;
        file.try_clone()
            .context("Failed to duplicate the handle of a redirection target")
    }

    /// Prepare file redirections before command execution
    ///
    /// Validates all redirections, opens files, and records original state for undo.
    ///
    /// No file is emptied until every redirection has been set up. If one
    /// of them is refused, the targets of the others still hold what they
    /// held. A file that an earlier redirection created stays, empty, as
    /// it does in bash.
    ///
    /// Prefer [`Self::run`], which also makes the record for undo on every
    /// path.
    pub fn setup(redirects: &[Redirection], state: &ShellState) -> Result<Self> {
        // Validate all redirections first (fail fast)
        validate_redirections(redirects, state)?;

        let mut setup = Self::new();

        for redirect in redirects {
            let opened_before = setup.opened_files.len();
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
            let opened = setup.opened_files.len() > opened_before;
            setup.targets.push(opened.then_some(opened_before));
        }

        setup.truncate_pending()?;

        Ok(setup)
    }

    /// Empty the files that `>` redirections opened, once every
    /// redirection of the command has been set up.
    ///
    /// Emptying each file as it was set up lost its content when a later
    /// redirection was then refused: `echo hi > out 2> dangling` emptied
    /// `out`, failed on `dangling`, and dropped the record that held what
    /// `out` had contained.
    ///
    /// If a file cannot be emptied, those emptied before it get their
    /// content back, so the targets are either all emptied or all as they
    /// were.
    fn truncate_pending(&mut self) -> Result<()> {
        self.truncate_pending_with(|file| file.set_len(0))
    }

    /// [`Self::truncate_pending`], with the step that empties a file passed
    /// in as `empty`, so that a test can make that step fail.
    fn truncate_pending_with(
        &mut self,
        empty: impl Fn(&File) -> std::io::Result<()>,
    ) -> Result<()> {
        let pending = std::mem::take(&mut self.pending_truncations);
        for (done, &(place, record)) in pending.iter().enumerate() {
            let mut file = &self.opened_files[place];
            if let Err(e) = empty(file).and_then(|()| file.rewind()) {
                let not_restored = self.write_back(&pending[..done]);
                let path = self.modifications[record].path().display().to_string();
                let failed = anyhow::Error::new(e).context(format!("Failed to truncate: {path}"));
                if not_restored.is_empty() {
                    return Err(failed);
                }
                return Err(failed.context(format!(
                    "The earlier content could not be written back to: {}",
                    not_restored.join(", ")
                )));
            }
        }
        Ok(())
    }

    /// Write the saved content back to the files of `emptied` (places in
    /// `opened_files` and `modifications`). Returns the paths of those
    /// that could not be written.
    fn write_back(&self, emptied: &[(usize, usize)]) -> Vec<String> {
        let mut not_restored = Vec::new();
        for &(place, record) in emptied {
            let FileModification::Truncated {
                path,
                original_content,
            } = &self.modifications[record]
            else {
                continue;
            };
            let mut file = &self.opened_files[place];
            let written = file
                .rewind()
                .and_then(|()| file.write_all(original_content))
                .and_then(|()| file.rewind());
            if written.is_err() {
                not_restored.push(path.display().to_string());
            }
        }
        not_restored
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

        // The target is opened beneath the session root, once, and without
        // truncating it. Everything else is decided from the open file. A
        // check made on the name before the open can be overtaken: between
        // the two, the name can be given to another file (a hard link to a
        // file outside the root, say), and the open would then truncate
        // that one. A path that leaves the root through a symlink is
        // refused by the open itself.
        let contained = state.contained_abs(&path)?;
        let (mut target, created) = open_redirect_target(state.root_dir(), &contained, append)
            .with_context(|| format!("Failed to open file for writing: {}", path.display()))?;
        let meta = target
            .metadata()
            .with_context(|| format!("Failed to stat file: {}", path.display()))?;
        check_writable_target(&meta, &path)?;

        // The record names the file that is changed. Through a link
        // (`echo x > alias`) that is the link's target: the bytes saved for
        // undo are the target's, and an `obliterate` of the target must be
        // able to find them.
        let changed = changed_file(state, &contained, &meta)
            .with_context(|| format!("Cannot redirect to: {}", path.display()))?;

        // Record original state for undo
        if created {
            // File did not exist - it was created by the open
            self.modifications
                .push(FileModification::Created { path: changed });
        } else if append {
            // The file is emptied by a preceding `>` of the same command
            // before anything is appended (`> f 2>> f`), so what the
            // append starts from is nothing, not what the file holds now.
            let emptied_first = self
                .pending_truncations
                .iter()
                .any(|&(_, record)| self.modifications[record].path() == changed.as_path());
            let original_size = if emptied_first { 0 } else { meta.len() };
            self.modifications.push(FileModification::Appended {
                path: changed,
                original_size,
            });
        } else {
            // Save the original content, read from the file that will be
            // truncated. It is not truncated here: see `truncate_pending`.
            let mut original_content = Vec::new();
            target
                .read_to_end(&mut original_content)
                .with_context(|| format!("Failed to read file for backup: {}", path.display()))?;

            // Warn if file is large
            if original_content.len() > 10 * 1024 * 1024 {
                eprintln!(
                    "Warning: Saving {:.1}MB file for undo. This may use significant memory.",
                    original_content.len() as f64 / (1024.0 * 1024.0)
                );
            }

            self.pending_truncations
                .push((self.opened_files.len(), self.modifications.len()));
            self.modifications.push(FileModification::Truncated {
                path: changed,
                original_content,
            });
        }

        self.opened_files.push(target.into_std());

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

        // Open for reading via the noatime-aware helper so input
        // redirections (`<` operator) do not mutate atime when permitted.
        let file = crate::fs_pure::open_pure(&path)
            .with_context(|| format!("Failed to open input file: {}", path.display()))?;

        self.opened_files.push(file);

        Ok(())
    }

    /// Record all modifications as undoable operations
    pub fn record_for_undo(self, state: &mut ShellState) -> Result<()> {
        use crate::state::{Operation, OperationType};

        // Clone modifications to avoid moving out of Drop type
        for modification in self.modifications.clone() {
            let (op_type, path, undo_data) = match modification {
                FileModification::Created { path } => {
                    // File was created by redirection
                    let path_str = rooted_path(state, &path);
                    (OperationType::CreateFile, path_str, None)
                }

                FileModification::Truncated {
                    path,
                    original_content,
                } => {
                    // File was truncated by > redirection
                    let path_str = rooted_path(state, &path);
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
                    let path_str = rooted_path(state, &path);
                    // Encode size as bytes
                    let size_bytes = original_size.to_le_bytes().to_vec();
                    (OperationType::FileAppended, path_str, Some(size_bytes))
                }
            };

            let mut op = Operation::new(
                op_type,
                path,
                state.active_transaction.as_ref().map(|t| t.id),
            );
            if let Some(data) = undo_data {
                op = op.with_undo_data(data);
            }

            // `path` is relative to the session root already (see
            // `rooted_path`), so it must not be read against the working
            // directory a second time.
            state.record_rooted_operation(op);
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
fn validate_no_input_output_conflict(redirects: &[Redirection], state: &ShellState) -> Result<()> {
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
            let metadata = fs::metadata(parent).with_context(|| {
                format!("Failed to stat parent directory: {}", parent.display())
            })?;

            let mode = metadata.permissions().mode();
            if mode & 0o200 == 0 {
                anyhow::bail!("Parent directory is not writable: {}", parent.display());
            }
        }
    }

    // If file exists, check it's writable
    if path.exists() {
        if !path.is_file() {
            anyhow::bail!(
                "Output redirection target is not a file: {}",
                path.display()
            );
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

        if let FileModification::Truncated {
            original_content, ..
        } = &setup.modifications[0]
        {
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

    /// The file a test's redirection was opened on: its device and inode.
    #[cfg(unix)]
    fn identity(file: &File) -> (u64, u64) {
        use std::os::unix::fs::MetadataExt;
        let meta = file.metadata().unwrap();
        (meta.dev(), meta.ino())
    }

    /// Each redirection is handed the file that was opened for it, and a
    /// redirection that names no file has none.
    #[cfg(unix)]
    #[test]
    fn test_each_redirection_gets_the_handle_of_its_own_file() {
        let temp = TempDir::new().unwrap();
        let state = test_state(temp.path());
        fs::write(temp.path().join("in"), "input").unwrap();
        let redirects = vec![
            Redirection::Input {
                file: "in".to_string(),
            },
            Redirection::HereString {
                content: "text".to_string(),
                expand: false,
            },
            Redirection::Output {
                file: "out".to_string(),
            },
            Redirection::ErrorAppend {
                file: "err".to_string(),
            },
        ];

        let setup = RedirectSetup::setup(&redirects, &state).unwrap();

        for (index, name) in [(0, "in"), (2, "out"), (3, "err")] {
            let by_name = File::open(temp.path().join(name)).unwrap();
            assert_eq!(
                identity(&setup.handle(index).unwrap()),
                identity(&by_name),
                "{name}"
            );
        }
        assert!(setup.handle(1).is_err(), "a here-string names no file");
        assert!(setup.handle(4).is_err(), "there is no fifth redirection");
    }

    /// A write through a link is recorded under the file it changed, not
    /// under the link: the bytes saved for undo are that file's.
    #[cfg(unix)]
    #[test]
    fn test_a_write_through_a_link_is_recorded_under_the_file_it_changed() {
        let temp = TempDir::new().unwrap();
        let root = fs::canonicalize(temp.path()).unwrap();
        let state = test_state(&root);
        fs::create_dir(root.join("dir")).unwrap();
        fs::write(root.join("dir/real"), "ORIGINAL").unwrap();
        std::os::unix::fs::symlink("dir/real", root.join("alias")).unwrap();
        std::os::unix::fs::symlink("dir", root.join("way")).unwrap();

        for (name, append) in [("alias", false), ("way/real", true)] {
            let mut setup = RedirectSetup::new();
            setup.setup_output_redirect(name, &state, append).unwrap();
            setup.truncate_pending().unwrap();
            assert_eq!(
                setup.modifications[0].path(),
                root.join("dir/real"),
                "{name}"
            );
        }
        // The first one truncated the file, and kept what it held.
        assert_eq!(fs::read(root.join("dir/real")).unwrap(), b"");
    }

    /// No target is emptied until every redirection of the command is set
    /// up. `echo hi > out 2> dangling` emptied `out`, was then refused on
    /// `dangling`, and dropped the record of what `out` had held.
    #[cfg(unix)]
    #[test]
    fn test_no_target_is_emptied_when_a_later_redirection_is_refused() {
        let temp = TempDir::new().unwrap();
        let root = fs::canonicalize(temp.path()).unwrap();
        let state = test_state(&root);
        fs::write(root.join("out"), "ORIGINAL").unwrap();
        std::os::unix::fs::symlink("nowhere", root.join("dangling")).unwrap();
        let redirects = vec![
            Redirection::Output {
                file: "out".to_string(),
            },
            Redirection::ErrorOutput {
                file: "dangling".to_string(),
            },
        ];

        assert!(RedirectSetup::setup(&redirects, &state).is_err());

        assert_eq!(fs::read(root.join("out")).unwrap(), b"ORIGINAL");
    }

    /// If a target cannot be emptied, those emptied before it get their
    /// content back.
    #[test]
    fn test_targets_get_their_content_back_when_one_cannot_be_emptied() {
        let temp = TempDir::new().unwrap();
        let root = fs::canonicalize(temp.path()).unwrap();
        let state = test_state(&root);
        fs::write(root.join("one"), "FIRST").unwrap();
        fs::write(root.join("two"), "SECOND").unwrap();
        let mut setup = RedirectSetup::new();
        setup.setup_output_redirect("one", &state, false).unwrap();
        setup.setup_output_redirect("two", &state, false).unwrap();

        let emptied = std::cell::Cell::new(0);
        let refused = setup.truncate_pending_with(|file| {
            emptied.set(emptied.get() + 1);
            if emptied.get() == 2 {
                return Err(std::io::Error::other("the second file cannot be emptied"));
            }
            file.set_len(0)
        });

        assert!(refused.is_err());
        assert_eq!(fs::read(root.join("one")).unwrap(), b"FIRST");
        assert_eq!(fs::read(root.join("two")).unwrap(), b"SECOND");
    }

    /// What the set-up changed is recorded whatever becomes of the command.
    /// A command that failed after its `>` target was emptied left nothing
    /// for undo to restore.
    #[test]
    fn test_run_records_the_set_up_when_the_command_fails() {
        let temp = TempDir::new().unwrap();
        let root = fs::canonicalize(temp.path()).unwrap();
        let mut state = test_state(&root);
        fs::write(root.join("f"), "ORIGINAL").unwrap();
        let redirects = vec![Redirection::Output {
            file: "f".to_string(),
        }];

        let outcome: Result<()> = RedirectSetup::run(&redirects, &mut state, |_, _| {
            anyhow::bail!("the command failed")
        });

        assert!(outcome.is_err());
        assert_eq!(fs::read(root.join("f")).unwrap(), b"");
        crate::commands::undo(&mut state, 1, false).unwrap();
        assert_eq!(fs::read(root.join("f")).unwrap(), b"ORIGINAL");
    }

    /// A truncation that is redone empties the file a second time, and its
    /// record must hold the content again. It held none, so `echo x > f;
    /// undo; redo; undo` left `f` empty.
    #[cfg(unix)]
    #[test]
    fn test_a_redone_truncation_can_be_undone_again() {
        let temp = TempDir::new().unwrap();
        let root = fs::canonicalize(temp.path()).unwrap();
        let mut state = test_state(&root);
        fs::write(root.join("f"), "ORIGINAL").unwrap();

        let redirects = vec![Redirection::Output {
            file: "f".to_string(),
        }];
        RedirectSetup::run(&redirects, &mut state, |_, _| Ok(())).unwrap();
        assert_eq!(fs::read(root.join("f")).unwrap(), b"");

        crate::commands::undo(&mut state, 1, false).unwrap();
        assert_eq!(fs::read(root.join("f")).unwrap(), b"ORIGINAL");
        crate::commands::redo(&mut state, 1, false).unwrap();
        assert_eq!(fs::read(root.join("f")).unwrap(), b"");
        crate::commands::undo(&mut state, 1, false).unwrap();
        assert_eq!(fs::read(root.join("f")).unwrap(), b"ORIGINAL");
    }

    /// Redoing a truncation makes the checks the redirection made: a file
    /// that has gained another name since is not emptied.
    #[cfg(unix)]
    #[test]
    fn test_a_truncation_is_not_redone_on_a_file_with_another_name() {
        let temp = TempDir::new().unwrap();
        let root = fs::canonicalize(temp.path()).unwrap();
        let mut state = test_state(&root);
        fs::write(root.join("f"), "ORIGINAL").unwrap();

        let redirects = vec![Redirection::Output {
            file: "f".to_string(),
        }];
        RedirectSetup::run(&redirects, &mut state, |_, _| Ok(())).unwrap();
        crate::commands::undo(&mut state, 1, false).unwrap();
        fs::hard_link(root.join("f"), root.join("other-name")).unwrap();

        let refused = crate::commands::redo(&mut state, 1, false).unwrap_err();

        assert!(format!("{refused:#}").contains("hard links"), "{refused:#}");
        assert_eq!(fs::read(root.join("other-name")).unwrap(), b"ORIGINAL");
    }

    /// A link whose target does not exist is refused, and nothing is made.
    /// The file would have to be created through the link, and a file that
    /// another program makes at that moment cannot be told from it.
    #[cfg(unix)]
    #[test]
    fn test_a_redirect_to_a_link_with_no_target_is_refused_and_makes_nothing() {
        let temp = TempDir::new().unwrap();
        let state = test_state(temp.path());
        std::os::unix::fs::symlink("nowhere", temp.path().join("dangling")).unwrap();

        let mut setup = RedirectSetup::new();
        let refused = setup
            .setup_output_redirect("dangling", &state, false)
            .unwrap_err();

        assert!(
            format!("{refused:#}").contains("symbolic link"),
            "{refused:#}"
        );
        assert!(!temp.path().join("nowhere").exists());
        assert!(setup.modifications.is_empty());
        assert!(setup.opened_files.is_empty());
    }

    /// Saving the old content for undo is a read, and it must not change
    /// the file's access time (see `fs_pure`). The file is read through
    /// the handle that then truncates it.
    #[cfg(target_os = "linux")]
    #[test]
    fn test_saving_the_old_content_does_not_change_the_access_time() {
        use std::time::{Duration, UNIX_EPOCH};

        let temp = TempDir::new().unwrap();
        let state = test_state(temp.path());
        let path = temp.path().join("f");
        fs::write(&path, "OLD CONTENT").unwrap();
        // An access time older than the modification time: the one case in
        // which a read moves it under `relatime`.
        let accessed = UNIX_EPOCH + Duration::from_secs(1_000_000_000);
        let modified = UNIX_EPOCH + Duration::from_secs(1_100_000_000);
        let times = fs::FileTimes::new()
            .set_accessed(accessed)
            .set_modified(modified);
        File::options()
            .write(true)
            .open(&path)
            .unwrap()
            .set_times(times)
            .unwrap();

        let mut setup = RedirectSetup::new();
        setup.setup_output_redirect("f", &state, false).unwrap();

        assert!(matches!(
            &setup.modifications[0],
            FileModification::Truncated { original_content, .. } if original_content == b"OLD CONTENT"
        ));
        assert_eq!(fs::metadata(&path).unwrap().accessed().unwrap(), accessed);
    }
}
