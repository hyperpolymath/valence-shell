// SPDX-License-Identifier: MPL-2.0
// Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//! Fuzz Target: Glob Expansion
//!
//! Expands arbitrary patterns over one small, fixed directory tree, so the
//! target exercises the shell's own walker and limits rather than the size of
//! the machine it runs on. (Until 2026-11-17 an absolute input such as `/**/*`
//! walked the runner's whole file system, following symbolic-link loops under
//! /proc and /sys, and hit libFuzzer's 2560 MB limit.)
//!
//! - Absolute patterns are re-rooted under the fixture.
//! - Patterns with a `..` component are skipped: they would leave the fixture.
//! - Expansion runs under small limits so that inputs reach them, and every
//!   result is checked against the limits and against the file system.
//!
//! The fixture holds the cases that matter for termination and matching:
//! two symbolic-link loops, a dangling link, a hidden directory and a name
//! that is not valid UTF-8.

#![no_main]

use libfuzzer_sys::fuzz_target;
use std::fs;
use std::os::unix::ffi::OsStrExt;
use std::os::unix::fs::symlink;
use std::path::{Path, PathBuf};
use std::sync::OnceLock;
use tempfile::TempDir;
use vsh::glob::{expand_glob_with_limits, GlobLimitExceeded, GlobLimits};

const LIMITS: GlobLimits = GlobLimits {
    max_reads: 20_000,
    max_matches: 2_000,
    max_match_bytes: 256 * 1024,
};

/// Build the fixture tree.
fn build_fixture() -> std::io::Result<TempDir> {
    let t = TempDir::new()?;
    let root = t.path();
    for dir in ["d/sub", ".hd/x", "e"] {
        fs::create_dir_all(root.join(dir))?;
    }
    for file in [
        "a.txt",
        "b.txt",
        "c.log",
        ".hidden",
        "d/f.rs",
        "d/sub/g.rs",
        ".hd/x/y",
        "e/z",
    ] {
        fs::write(root.join(file), b"")?;
    }
    // Some file systems refuse names that are not UTF-8; the rest still works.
    let _ = fs::write(root.join(std::ffi::OsStr::from_bytes(b"bad\xff.txt")), b"");
    symlink("..", root.join("d/up"))?; // loop back to the root
    symlink(".", root.join("self"))?; // loop to itself
    symlink("d", root.join("link"))?;
    symlink("missing", root.join("dangling"))?;
    Ok(t)
}

/// The fixture, built once. A fixture that cannot be built stops the run
/// with a clear message: skipping every input would report a green run that
/// tested nothing.
fn fixture() -> &'static Path {
    static FIXTURE: OnceLock<TempDir> = OnceLock::new();
    FIXTURE
        .get_or_init(|| match build_fixture() {
            Ok(fixture) => fixture,
            Err(e) => {
                // Exit rather than panic: libFuzzer reports an exiting target
                // as an error ("fuzz target exited"), so the run still fails.
                eprintln!("fuzz_glob_expansion: cannot build the fixture tree: {e}");
                std::process::exit(1);
            }
        })
        .path()
}

fuzz_target!(|data: &[u8]| {
    let Ok(input) = std::str::from_utf8(data) else {
        return;
    };
    if input.len() > 200 || input.split('/').any(|part| part == "..") {
        return;
    }

    let base = fixture();
    let pattern = if input.starts_with('/') {
        format!("{}{}", base.display(), input)
    } else {
        input.to_string()
    };

    match expand_glob_with_limits(&pattern, base, &LIMITS) {
        Ok(expansion) => {
            let usage = expansion.usage;
            assert!(usage.reads.total() <= LIMITS.max_reads);
            assert!(usage.matches.peak() <= LIMITS.max_matches);
            assert!(usage.match_bytes.peak() <= LIMITS.max_match_bytes);
            assert_eq!(expansion.paths.len() as u64, usage.matches.held());

            let bytes: u64 = expansion
                .paths
                .iter()
                .map(|p| p.as_os_str().len() as u64 + 1)
                .sum();
            assert_eq!(bytes, usage.match_bytes.held());

            // Sorted, each path once, and every path exists.
            assert!(expansion.paths.windows(2).all(|w| w[0] < w[1]));
            for path in &expansion.paths {
                let real: PathBuf = if path.is_absolute() {
                    path.clone()
                } else {
                    base.join(path)
                };
                assert!(
                    fs::symlink_metadata(&real).is_ok(),
                    "{} does not exist",
                    real.display()
                );
            }
        }
        Err(err) => {
            if let Some(stopped) = err.downcast_ref::<GlobLimitExceeded>() {
                assert!(stopped.exceeded.level > stopped.exceeded.limit);
                assert!(stopped.usage.reads.total() <= LIMITS.max_reads);
                assert!(stopped.usage.matches.peak() <= LIMITS.max_matches);
                assert!(stopped.usage.match_bytes.peak() <= LIMITS.max_match_bytes);
            }
        }
    }
});
