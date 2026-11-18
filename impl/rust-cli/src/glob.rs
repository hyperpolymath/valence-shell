// SPDX-License-Identifier: MPL-2.0
// Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//! Glob pattern expansion (filename wildcards)
//!
//! Expands `*`, `?`, `[...]` and the recursive `**` against the file system,
//! with fixed limits on how much work and memory one expansion may use.
//! Brace expansion (`{a,b}`) is a separate, purely textual step: see
//! [`expand_braces`].
//!
//! # Matching rules
//!
//! The rules follow bash 5.2 with `shopt -s globstar`, `dotglob` off and
//! `globskipdots` on (the default):
//!
//! - `*`, `?` and `[...]` match within one path component. Single components
//!   are matched by the `glob` crate's [`glob::Pattern`].
//! - A name that starts with `.` is matched only by a component that itself
//!   starts with a literal `.`. So `*` skips hidden files, `.*` and `.h*` find
//!   them, and `.` and `..` are never produced by a wildcard.
//! - A component that is exactly `**` matches zero or more directories. It
//!   lists a symbolic link to a directory but does not descend into it, and it
//!   does not enter hidden directories. Other components do go through
//!   symbolic links, so `link/*` lists the target directory.
//!   One measured difference: when `**` is *not* the first component (an
//!   absolute pattern, `./**/*`, `d/**/*`), bash 5.2 enters a symbolic link to
//!   a directory found by `**` for one more component, and vsh does not. On
//!   one machine `/usr/**/*` gave bash 2,956 more paths than vsh, every one of
//!   them below a link such as `/usr/bin/X11 -> .`.
//! - A pattern that ends in `**` lists everything below its directory, and the
//!   directory itself when it is named (`d/**` gives `d/`, `d/e`, ...).
//! - A pattern that ends in `/` matches directories only, and each result ends
//!   in `/`.
//! - Results are sorted and each path appears once. (bash lists a path again
//!   for every way the pattern matches it, so `**/*/**/*` can repeat a path
//!   many times.)
//! - A pattern that matches nothing gives an empty list; the caller decides
//!   whether to keep the word literally.
//!
//! # Limits
//!
//! One expansion is metered on three axes ([`GlobLimits`]):
//!
//! | Axis | Kind | Default |
//! |------|------|---------|
//! | file-system reads (directories opened, entries listed, names looked up) | cost: adds up | 10,000,000 |
//! | matches held | occupancy: high-water mark | 100,000 |
//! | bytes of matches held (path length + 1 for each match) | occupancy | 6 MiB |
//!
//! The meters are charged *while* the walk runs, so an expansion stops at the
//! first unit over a limit instead of collecting everything first. Stopping
//! returns a [`GlobLimitExceeded`] error that names the limit and carries the
//! usage so far and the directory being read; no partial result is returned.
//! Because entries are visited in sorted order, the same pattern over the same
//! tree always stops at the same place with the same report.
//!
//! The default byte limit is 6 MiB because Linux refuses any `execve` whose
//! argument strings take more than that, whatever the stack limit (measured on
//! Linux 6.18: 6,279,840 bytes accepted at both a 64 MiB and an unlimited
//! stack), so a larger expansion could never reach an external command.
//!
//! bash has no such limits: it expanded `/**/*` on a test machine to 643,683
//! paths. The limits here are deliberate departures, made so that a single
//! word cannot exhaust the shell's memory.
//!
//! # Work bound
//!
//! Each pair (directory, pattern component) is processed at most once, so the
//! walk reads each directory at most once per component of the pattern. That
//! is the `O(|pattern| x |entries|)` shape stated as frontier item A-6 in
//! `docs/PROOF-OPEN-FRONTIER.adoc`; here it is tested, not proved.
//!
//! # Examples
//! ```no_run
//! use vsh::glob::expand_glob;
//! use std::path::Path;
//!
//! let matches = expand_glob("*.txt", Path::new("/tmp")).unwrap();
//! // Returns: ["file1.txt", "file2.txt", ...]
//! ```

use crate::grade::{Cost, Exceeded, Meter, Occupancy};
use anyhow::{Context, Result};
use std::collections::{BTreeSet, HashSet};
use std::ffi::OsString;
use std::fmt;
use std::fs;
use std::path::{Path, PathBuf};

/// Default limit on file-system reads in one expansion.
pub const MAX_GLOB_READS: u64 = 10_000_000;

/// Default limit on the number of matches one expansion may hold.
pub const MAX_GLOB_RESULTS: u64 = 100_000;

/// Default limit on the bytes of matches one expansion may hold: 6 MiB, the
/// most Linux `execve` accepts for argument strings.
pub const MAX_GLOB_MATCH_BYTES: u64 = 6 * 1024 * 1024;

/// The limits one glob expansion runs under.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct GlobLimits {
    /// Most file-system reads: directories opened, entries listed, names looked up.
    pub max_reads: u64,
    /// Most matches held at once.
    pub max_matches: u64,
    /// Most bytes of matches held at once (path length + 1 per match).
    pub max_match_bytes: u64,
}

impl GlobLimits {
    /// The limits [`expand_glob`] uses.
    pub const DEFAULT: GlobLimits = GlobLimits {
        max_reads: MAX_GLOB_READS,
        max_matches: MAX_GLOB_RESULTS,
        max_match_bytes: MAX_GLOB_MATCH_BYTES,
    };
}

impl Default for GlobLimits {
    fn default() -> Self {
        GlobLimits::DEFAULT
    }
}

/// What one expansion used, on each metered axis.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct GlobUsage {
    /// File-system reads: directories opened, entries listed, names looked up.
    pub reads: Cost,
    /// Matches held.
    pub matches: Occupancy,
    /// Bytes of matches held (path length + 1 per match).
    pub match_bytes: Occupancy,
}

impl fmt::Display for GlobUsage {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} file-system reads, {} matches, {} bytes of matches",
            self.reads.total(),
            self.matches.peak(),
            self.match_bytes.peak()
        )
    }
}

/// A successful expansion: the matches and what finding them cost.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Expansion {
    /// Matching paths, sorted, each once.
    pub paths: Vec<PathBuf>,
    /// The resources the expansion used.
    pub usage: GlobUsage,
}

/// The error returned when an expansion reaches one of its [`GlobLimits`].
///
/// It is a record of where the walk stopped, not a partial result: it says
/// that more exists and where the walk was, without listing what was found.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GlobLimitExceeded {
    /// The pattern as given.
    pub pattern: String,
    /// The limit that was reached: which axis, its value, and the level the
    /// refused step would have reached.
    pub exceeded: Exceeded,
    /// What had been used when the walk stopped.
    pub usage: GlobUsage,
    /// The directory being read when the walk stopped, written the way the
    /// matches would be (relative to the base directory unless the pattern is
    /// absolute).
    pub at: PathBuf,
}

impl fmt::Display for GlobLimitExceeded {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "glob pattern '{}' was not expanded: {} (stopped while reading '{}' after {})",
            self.pattern,
            self.exceeded,
            self.at.display(),
            self.usage
        )
    }
}

impl std::error::Error for GlobLimitExceeded {}

/// Check if a string contains glob metacharacters
///
/// Returns true if the string contains any of: * ? [ { (unescaped)
///
/// # Examples
/// ```
/// use vsh::glob::contains_glob_pattern;
/// assert!(contains_glob_pattern("*.txt"));
/// assert!(contains_glob_pattern("file?.rs"));
/// assert!(contains_glob_pattern("[a-z]*.log"));
/// assert!(!contains_glob_pattern("file.txt"));
/// assert!(!contains_glob_pattern("\\*.txt")); // Escaped
/// ```
pub fn contains_glob_pattern(s: &str) -> bool {
    let chars = s.chars().peekable();
    let mut escaped = false;

    for ch in chars {
        if escaped {
            escaped = false;
            continue;
        }

        if ch == '\\' {
            escaped = true;
            continue;
        }

        // Glob metacharacters
        if matches!(ch, '*' | '?' | '[' | '{') {
            return true;
        }
    }

    false
}

/// Expand a glob pattern to matching file paths, under [`GlobLimits::DEFAULT`].
///
/// Relative patterns are matched below `base_dir` and give paths relative to
/// it; patterns that start with `/` give absolute paths. See the
/// [module documentation](self) for the matching rules and the limits.
///
/// # Examples
/// ```no_run
/// use vsh::glob::expand_glob;
/// use std::path::Path;
///
/// // Basic wildcard
/// let matches = expand_glob("*.txt", Path::new("/tmp")).unwrap();
///
/// // Character class
/// let matches = expand_glob("file[0-9].log", Path::new("/var/log")).unwrap();
///
/// // Recursive glob
/// let matches = expand_glob("**/*.rs", Path::new("src")).unwrap();
/// ```
///
/// # Errors
/// Returns an error if the pattern is invalid, or a [`GlobLimitExceeded`]
/// (reachable with `anyhow::Error::downcast_ref`) if the expansion reaches a
/// limit. Directories that cannot be read are skipped, as bash does.
pub fn expand_glob(pattern: &str, base_dir: &Path) -> Result<Vec<PathBuf>> {
    expand_glob_with_limits(pattern, base_dir, &GlobLimits::DEFAULT).map(|e| e.paths)
}

/// Expand a glob pattern under the given limits, reporting what it used.
///
/// # Examples
/// ```
/// use vsh::glob::{expand_glob_with_limits, GlobLimitExceeded, GlobLimits};
///
/// let dir = tempfile::tempdir().unwrap();
/// for name in ["a.txt", "b.txt", "c.txt"] {
///     std::fs::write(dir.path().join(name), b"").unwrap();
/// }
///
/// let limits = GlobLimits { max_matches: 2, ..GlobLimits::DEFAULT };
/// let err = expand_glob_with_limits("*.txt", dir.path(), &limits).unwrap_err();
/// let stopped = err.downcast_ref::<GlobLimitExceeded>().unwrap();
/// assert_eq!(stopped.exceeded.axis, "matches held");
/// assert_eq!((stopped.exceeded.limit, stopped.exceeded.level), (2, 3));
/// ```
///
/// # Errors
/// As for [`expand_glob`].
pub fn expand_glob_with_limits(
    pattern: &str,
    base_dir: &Path,
    limits: &GlobLimits,
) -> Result<Expansion> {
    let compiled =
        Compiled::new(pattern).with_context(|| format!("Invalid glob pattern: {}", pattern))?;
    let mut walker = Walker::new(pattern, base_dir, &compiled, limits);
    walker.run().map_err(anyhow::Error::new)?;
    Ok(Expansion {
        usage: walker.usage(),
        paths: walker.found.into_iter().collect(),
    })
}

/// One path component of a compiled pattern.
#[derive(Debug)]
enum Component {
    /// No metacharacters: looked up by name, without listing the directory.
    Literal(String),
    /// Matched against each name in the directory.
    Wild(glob::Pattern),
    /// `**`: zero or more directories.
    Recursive,
}

#[derive(Debug)]
struct Compiled {
    components: Vec<Component>,
    absolute: bool,
    dirs_only: bool,
}

impl Compiled {
    fn new(pattern: &str) -> std::result::Result<Self, glob::PatternError> {
        let mut components: Vec<Component> = Vec::new();
        for part in pattern.split('/').filter(|part| !part.is_empty()) {
            let component = if part == "**" {
                // `**/**` matches exactly what `**` matches.
                if matches!(components.last(), Some(Component::Recursive)) {
                    continue;
                }
                Component::Recursive
            } else if part.contains(['*', '?', '[']) {
                Component::Wild(glob::Pattern::new(part)?)
            } else {
                Component::Literal(part.to_string())
            };
            components.push(component);
        }
        Ok(Compiled {
            components,
            absolute: pattern.starts_with('/'),
            dirs_only: pattern.len() > 1 && pattern.ends_with('/'),
        })
    }
}

const MATCH_OPTIONS: glob::MatchOptions = glob::MatchOptions {
    case_sensitive: true,
    require_literal_separator: true,
    require_literal_leading_dot: true,
};

/// The walk: a depth-first search over states (directory, component index),
/// each processed at most once.
struct Walker<'a> {
    pattern: &'a str,
    base: &'a Path,
    compiled: &'a Compiled,
    reads: Meter<Cost>,
    matches: Meter<Occupancy>,
    match_bytes: Meter<Occupancy>,
    found: BTreeSet<PathBuf>,
}

impl<'a> Walker<'a> {
    fn new(pattern: &'a str, base: &'a Path, compiled: &'a Compiled, limits: &GlobLimits) -> Self {
        Walker {
            pattern,
            base,
            compiled,
            reads: Meter::new("file-system reads", limits.max_reads),
            matches: Meter::new("matches held", limits.max_matches),
            match_bytes: Meter::new("bytes of matches held", limits.max_match_bytes),
            found: BTreeSet::new(),
        }
    }

    fn usage(&self) -> GlobUsage {
        GlobUsage {
            reads: self.reads.grade(),
            matches: self.matches.grade(),
            match_bytes: self.match_bytes.grade(),
        }
    }

    /// Where `path` (as it would be reported) is on the file system.
    fn real(&self, path: &Path) -> PathBuf {
        if self.compiled.absolute {
            path.to_path_buf()
        } else if path.as_os_str().is_empty() {
            self.base.to_path_buf()
        } else {
            self.base.join(path)
        }
    }

    fn stopped(&self, exceeded: Exceeded, at: &Path) -> GlobLimitExceeded {
        GlobLimitExceeded {
            pattern: self.pattern.to_string(),
            exceeded,
            usage: self.usage(),
            at: if at.as_os_str().is_empty() {
                PathBuf::from(".")
            } else {
                at.to_path_buf()
            },
        }
    }

    fn charge_read(&mut self, at: &Path) -> std::result::Result<(), GlobLimitExceeded> {
        self.reads.charge(1).map_err(|e| self.stopped(e, at))
    }

    /// Record a match, once.
    fn emit(&mut self, path: PathBuf, at: &Path) -> std::result::Result<(), GlobLimitExceeded> {
        let path = if self.compiled.dirs_only {
            path.join("")
        } else {
            path
        };
        if self.found.contains(&path) {
            return Ok(());
        }
        let bytes = path.as_os_str().len() as u64 + 1;
        self.matches.charge(1).map_err(|e| self.stopped(e, at))?;
        if let Err(e) = self.match_bytes.charge(bytes) {
            self.matches.release(1);
            return Err(self.stopped(e, at));
        }
        self.found.insert(path);
        Ok(())
    }

    /// List a directory in name order, charging the open and every entry.
    /// An unreadable directory gives no entries.
    fn list(
        &mut self,
        dir: &Path,
    ) -> std::result::Result<Vec<(OsString, fs::FileType)>, GlobLimitExceeded> {
        self.charge_read(dir)?;
        let mut entries = Vec::new();
        if let Ok(read) = fs::read_dir(self.real(dir)) {
            for entry in read {
                self.charge_read(dir)?;
                if let Ok(entry) = entry {
                    if let Ok(kind) = entry.file_type() {
                        entries.push((entry.file_name(), kind));
                    }
                }
            }
        }
        entries.sort_by(|a, b| a.0.cmp(&b.0));
        Ok(entries)
    }

    /// Whether `path` is a directory, going through a symbolic link.
    fn is_dir(&self, path: &Path, kind: Option<fs::FileType>) -> bool {
        match kind {
            Some(kind) if kind.is_dir() => true,
            Some(kind) if !kind.is_symlink() => false,
            _ => fs::metadata(self.real(path)).is_ok_and(|m| m.is_dir()),
        }
    }

    fn run(&mut self) -> std::result::Result<(), GlobLimitExceeded> {
        let count = self.compiled.components.len();
        if count == 0 {
            return Ok(());
        }
        let start = if self.compiled.absolute {
            PathBuf::from("/")
        } else {
            PathBuf::new()
        };
        let mut stack: Vec<(PathBuf, usize)> = vec![(start, 0)];
        let mut seen: HashSet<(PathBuf, usize)> = HashSet::new();

        while let Some((dir, index)) = stack.pop() {
            if !seen.insert((dir.clone(), index)) {
                continue;
            }
            let last = index + 1 == count;
            let compiled = self.compiled;
            // Successor states, pushed in reverse so they are visited in name order.
            let mut next: Vec<(PathBuf, usize)> = Vec::new();

            match &compiled.components[index] {
                Component::Literal(name) => {
                    self.charge_read(&dir)?;
                    let child = dir.join(name);
                    if last {
                        let exists = fs::symlink_metadata(self.real(&child)).is_ok();
                        if exists && (!compiled.dirs_only || self.is_dir(&child, None)) {
                            self.emit(child, &dir)?;
                        }
                    } else if self.is_dir(&child, None) {
                        next.push((child, index + 1));
                    }
                }
                Component::Wild(pattern) => {
                    for (name, kind) in self.list(&dir)? {
                        if !pattern.matches_with(&name.to_string_lossy(), MATCH_OPTIONS) {
                            continue;
                        }
                        let child = dir.join(&name);
                        if last {
                            if !compiled.dirs_only || self.is_dir(&child, Some(kind)) {
                                self.emit(child, &dir)?;
                            }
                        } else if self.is_dir(&child, Some(kind)) {
                            next.push((child, index + 1));
                        }
                    }
                }
                Component::Recursive => {
                    // Zero directories: the pattern continues here.
                    if !last {
                        next.push((dir.clone(), index + 1));
                    } else if !dir.as_os_str().is_empty() {
                        self.emit(dir.join(""), &dir)?;
                    }
                    // One more directory: descend into real, visible directories.
                    for (name, kind) in self.list(&dir)? {
                        if name.as_encoded_bytes().starts_with(b".") {
                            continue;
                        }
                        let child = dir.join(&name);
                        if last && (!compiled.dirs_only || self.is_dir(&child, Some(kind))) {
                            self.emit(child.clone(), &dir)?;
                        }
                        if kind.is_dir() {
                            next.push((child, index));
                        }
                    }
                }
            }
            stack.extend(next.into_iter().rev());
        }
        Ok(())
    }
}

#[cfg(test)]
mod walk_tests {
    use super::*;
    use proptest::prelude::*;
    use tempfile::TempDir;

    fn expand(pattern: &str, base: &Path) -> Vec<String> {
        expand_glob(pattern, base)
            .unwrap()
            .into_iter()
            .map(|p| p.to_string_lossy().into_owned())
            .collect()
    }

    #[test]
    fn literal_and_wild_components() {
        let t = TempDir::new().unwrap();
        fs::create_dir_all(t.path().join("src/sub")).unwrap();
        for f in ["src/a.rs", "src/b.txt", "src/sub/c.rs", "top.rs"] {
            fs::write(t.path().join(f), b"").unwrap();
        }
        assert_eq!(expand("src/*.rs", t.path()), ["src/a.rs"]);
        assert_eq!(expand("*/*/*.rs", t.path()), ["src/sub/c.rs"]);
        assert_eq!(expand("./*.rs", t.path()), ["./top.rs"]);
        assert_eq!(
            expand("**/*.rs", t.path()),
            ["src/a.rs", "src/sub/c.rs", "top.rs"]
        );
        assert_eq!(expand("src/**/c.rs", t.path()), ["src/sub/c.rs"]);
        assert!(expand("*.none", t.path()).is_empty());
    }

    #[test]
    fn absolute_patterns_give_absolute_paths() {
        let t = TempDir::new().unwrap();
        fs::write(t.path().join("x.txt"), b"").unwrap();
        let pattern = format!("{}/*.txt", t.path().display());
        assert_eq!(
            expand_glob(&pattern, Path::new("/nonexistent")).unwrap(),
            [t.path().join("x.txt")]
        );
    }

    #[test]
    fn invalid_patterns_are_errors_not_limits() {
        let t = TempDir::new().unwrap();
        for bad in ["a**", "***", "[z-"] {
            let err = expand_glob(bad, t.path()).unwrap_err();
            assert!(err.downcast_ref::<GlobLimitExceeded>().is_none(), "{bad}");
        }
    }

    #[test]
    fn a_base_directory_with_metacharacters_is_taken_literally() {
        let t = TempDir::new().unwrap();
        let base = t.path().join("we[ir]d*");
        fs::create_dir(&base).unwrap();
        fs::write(base.join("f.txt"), b"").unwrap();
        assert_eq!(expand("*.txt", &base), ["f.txt"]);
    }

    #[test]
    fn empty_pattern_matches_nothing() {
        let t = TempDir::new().unwrap();
        assert!(expand("", t.path()).is_empty());
    }

    // ------------------------------------------------------------------
    // Differential check against the `glob` crate, which this walker
    // replaces. On trees without symbolic links and for patterns that do not
    // end in `**` and have no component starting with `.`, the two must find
    // the same set of paths (the crate can list a path twice; this walker
    // lists it once). Those exclusions are exactly where the rules changed.
    // ------------------------------------------------------------------

    fn crate_glob(pattern: &str, base: &Path) -> BTreeSet<PathBuf> {
        let options = glob::MatchOptions {
            require_literal_leading_dot: true,
            case_sensitive: true,
            require_literal_separator: false,
        };
        glob::glob_with(&base.join(pattern).to_string_lossy(), options)
            .unwrap()
            .filter_map(|p| p.ok())
            .map(|p| p.strip_prefix(base).unwrap().to_path_buf())
            .collect()
    }

    fn tree() -> impl Strategy<Value = Vec<(Vec<&'static str>, bool)>> {
        let name = prop::sample::select(vec!["a", "b", "ab", "ba", ".h"]);
        prop::collection::vec((prop::collection::vec(name, 1..4), any::<bool>()), 0..25)
    }

    fn pattern() -> impl Strategy<Value = String> {
        let component = prop::sample::select(vec![
            "*", "?", "a*", "*b", "[ab]", "[!a]*", "a", "b", "ab", "**",
        ]);
        (prop::collection::vec(component, 1..5), any::<bool>()).prop_filter_map(
            "pattern ends in **",
            |(parts, slash)| {
                if parts.last() == Some(&"**") {
                    return None;
                }
                let mut p = parts.join("/");
                if slash {
                    p.push('/');
                }
                Some(p)
            },
        )
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(96))]
        #[test]
        fn agrees_with_the_glob_crate(entries in tree(), pattern in pattern()) {
            let t = TempDir::new().unwrap();
            for (parts, is_dir) in &entries {
                let path = parts.iter().collect::<PathBuf>();
                let full = t.path().join(&path);
                if let Some(parent) = full.parent() {
                    if fs::create_dir_all(parent).is_err() {
                        continue;
                    }
                }
                let _ = if *is_dir { fs::create_dir_all(&full) } else { fs::write(&full, b"") };
            }
            let ours: BTreeSet<PathBuf> = expand_glob(&pattern, t.path()).unwrap().into_iter().collect();
            prop_assert_eq!(ours, crate_glob(&pattern, t.path()), "pattern {}", pattern);
        }
    }
}

/// Expand brace patterns: a{b,c}d -> [abd, acd]
///
/// Performs brace expansion before glob expansion.
/// This is a pure string operation (no filesystem access).
///
/// # Examples
/// ```
/// use vsh::glob::expand_braces;
///
/// assert_eq!(
///     expand_braces("file{1,2,3}.txt"),
///     vec!["file1.txt", "file2.txt", "file3.txt"]
/// );
///
/// assert_eq!(
///     expand_braces("src/{main,lib}.rs"),
///     vec!["src/main.rs", "src/lib.rs"]
/// );
/// ```
/// Maximum number of results from brace expansion (prevents exponential blowup from
/// patterns like `{a,b}{a,b}{a,b}...` which grow as 2^N).
const MAX_BRACE_RESULTS: usize = 10_000;

pub fn expand_braces(pattern: &str) -> Vec<String> {
    expand_braces_limited(pattern, MAX_BRACE_RESULTS)
}

fn expand_braces_limited(pattern: &str, remaining: usize) -> Vec<String> {
    if remaining == 0 {
        return vec![pattern.to_string()];
    }

    // Find first unescaped {
    let chars = pattern.chars().enumerate().peekable();
    let mut brace_start = None;
    let mut brace_depth = 0;
    let mut escaped = false;

    for (i, ch) in chars {
        if escaped {
            escaped = false;
            continue;
        }

        if ch == '\\' {
            escaped = true;
            continue;
        }

        if ch == '{' {
            if brace_depth == 0 {
                brace_start = Some(i);
            }
            brace_depth += 1;
        } else if ch == '}' && brace_depth > 0 {
            brace_depth -= 1;
            if brace_depth == 0 {
                // Found matching close brace.
                // brace_start is Some whenever brace_depth >= 1: the only site
                // that increments brace_depth (the `ch == '{'` arm above) sets
                // brace_start = Some(i) when brace_depth was zero, and only the
                // matched '}' decrements it back. If that ever broke, the
                // pattern is returned unexpanded instead of panicking.
                let Some(start) = brace_start else {
                    return vec![pattern.to_string()];
                };
                let prefix = &pattern[..start];
                let suffix = &pattern[i + 1..];
                let content = &pattern[start + 1..i];

                // Split by comma (respecting nesting and escaping)
                let alternatives = split_brace_content(content);

                // If only one alternative, it's not a valid brace expansion
                if alternatives.len() <= 1 {
                    // Not a brace expansion, return as-is
                    return vec![pattern.to_string()];
                }

                // Expand each alternative with remaining budget
                let mut results = Vec::new();
                let mut budget = remaining;
                for alt in alternatives {
                    if budget == 0 {
                        break;
                    }
                    let expanded = format!("{}{}{}", prefix, alt, suffix);
                    let sub = expand_braces_limited(&expanded, budget);
                    budget = budget.saturating_sub(sub.len());
                    results.extend(sub);
                }

                return results;
            }
        }
    }

    // No brace expansion found, return original
    vec![pattern.to_string()]
}

/// Split brace content by commas (respecting nesting and escaping)
fn split_brace_content(content: &str) -> Vec<String> {
    let mut parts = Vec::new();
    let mut current = String::new();
    let mut depth = 0;
    let mut escaped = false;

    for ch in content.chars() {
        if escaped {
            current.push(ch);
            escaped = false;
            continue;
        }

        if ch == '\\' {
            escaped = true;
            current.push(ch);
            continue;
        }

        if ch == '{' {
            depth += 1;
            current.push(ch);
        } else if ch == '}' {
            depth -= 1;
            current.push(ch);
        } else if ch == ',' && depth == 0 {
            // Top-level comma: split here
            parts.push(current.clone());
            current.clear();
        } else {
            current.push(ch);
        }
    }

    // Push final part
    if !current.is_empty() || !parts.is_empty() {
        parts.push(current);
    }

    parts
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_contains_glob_pattern() {
        assert!(contains_glob_pattern("*.txt"));
        assert!(contains_glob_pattern("file?.rs"));
        assert!(contains_glob_pattern("[a-z]*.log"));
        assert!(contains_glob_pattern("file{1,2}.txt"));
        assert!(!contains_glob_pattern("file.txt"));
        assert!(!contains_glob_pattern("plain_filename"));
    }

    #[test]
    fn test_contains_glob_pattern_escaped() {
        // Escaped metacharacters are not glob patterns
        assert!(!contains_glob_pattern("\\*.txt"));
        assert!(!contains_glob_pattern("file\\?.rs"));
        assert!(!contains_glob_pattern("\\[test\\]"));
    }

    #[test]
    fn test_expand_braces_simple() {
        assert_eq!(
            expand_braces("file{1,2,3}.txt"),
            vec!["file1.txt", "file2.txt", "file3.txt"]
        );
    }

    #[test]
    fn test_expand_braces_path() {
        assert_eq!(
            expand_braces("src/{main,lib}.rs"),
            vec!["src/main.rs", "src/lib.rs"]
        );
    }

    #[test]
    fn test_expand_braces_no_expansion() {
        // Single element - no expansion
        assert_eq!(expand_braces("file{1}.txt"), vec!["file{1}.txt"]);

        // No braces
        assert_eq!(expand_braces("file.txt"), vec!["file.txt"]);
    }

    #[test]
    fn test_expand_braces_nested() {
        let result = expand_braces("{a,{b,c}}");
        assert_eq!(result.len(), 3);
        assert!(result.contains(&"a".to_string()));
        assert!(result.contains(&"b".to_string()));
        assert!(result.contains(&"c".to_string()));
    }

    #[test]
    fn test_expand_braces_multiple() {
        let result = expand_braces("{a,b}{1,2}");
        assert_eq!(result.len(), 4);
        assert!(result.contains(&"a1".to_string()));
        assert!(result.contains(&"a2".to_string()));
        assert!(result.contains(&"b1".to_string()));
        assert!(result.contains(&"b2".to_string()));
    }

    #[test]
    fn test_split_brace_content() {
        assert_eq!(split_brace_content("a,b,c"), vec!["a", "b", "c"]);

        assert_eq!(split_brace_content("main,lib"), vec!["main", "lib"]);

        // Nested braces
        assert_eq!(split_brace_content("a,{b,c}"), vec!["a", "{b,c}"]);
    }
}
