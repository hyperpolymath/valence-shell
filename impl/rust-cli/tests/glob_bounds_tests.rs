// SPDX-License-Identifier: MPL-2.0
// Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//! Glob expansion: termination, limits and resource accounting (issue #191).
//!
//! The first two tests reproduce the out-of-memory failure that
//! ClusterFuzzLite found on 2026-11-17 (`fuzz_glob_expansion`, input `/**/*`):
//! the previous expansion followed symbolic links under `**`, so a single link
//! back to a parent directory made `**/*` grow without end. Each runs the
//! expansion on a worker thread and fails if it has not finished in time,
//! instead of hanging the test run.
//!
//! The other tests use small injected limits so they are exact and fast, and
//! check the reported usage against counts computed here directly from the
//! fixture.
//!
//! Run with: `cargo test --test glob_bounds_tests`

#![cfg(unix)]

use std::collections::BTreeSet;
use std::fs;
use std::os::unix::fs::symlink;
use std::path::{Path, PathBuf};
use std::sync::mpsc;
use std::time::{Duration, Instant};
use tempfile::TempDir;
use vsh::glob::{expand_glob, expand_glob_with_limits, Expansion, GlobLimitExceeded, GlobLimits};

const TIME_ALLOWED: Duration = Duration::from_secs(20);

/// Run `expand_glob` on a worker thread; panic if it does not finish in time.
fn expand_within_time(pattern: &'static str, base: PathBuf) -> Vec<String> {
    let (send, receive) = mpsc::channel();
    std::thread::spawn(move || {
        let _ = send.send(expand_glob(pattern, &base).map_err(|e| e.to_string()));
    });
    match receive.recv_timeout(TIME_ALLOWED) {
        Ok(result) => result
            .expect("expansion failed")
            .into_iter()
            .map(|p| p.to_string_lossy().into_owned())
            .collect(),
        Err(_) => panic!("expand_glob({pattern:?}) did not finish within {TIME_ALLOWED:?}"),
    }
}

fn strings(paths: &[PathBuf]) -> Vec<String> {
    paths
        .iter()
        .map(|p| p.to_string_lossy().into_owned())
        .collect()
}

fn stopped(result: anyhow::Result<Expansion>) -> GlobLimitExceeded {
    let err = result.expect_err("the expansion must stop at a limit");
    err.downcast_ref::<GlobLimitExceeded>()
        .unwrap_or_else(|| panic!("expected a limit error, got: {err}"))
        .clone()
}

/// The 7-entry tree with two symbolic-link loops used in the reproduction:
/// `d/{f1,f2}`, `d/up -> ..`, `self -> .`, `top`.
fn looped_tree() -> TempDir {
    let t = TempDir::new().unwrap();
    fs::create_dir(t.path().join("d")).unwrap();
    for f in ["d/f1", "d/f2", "top"] {
        fs::write(t.path().join(f), b"").unwrap();
    }
    symlink("..", t.path().join("d/up")).unwrap();
    symlink(".", t.path().join("self")).unwrap();
    t
}

/// `dirs` directories with `files` files each, plus `files` files at the top.
fn broad_tree(dirs: usize, files: usize) -> TempDir {
    let t = TempDir::new().unwrap();
    for d in 0..dirs {
        let dir = t.path().join(format!("d{d:03}"));
        fs::create_dir(&dir).unwrap();
        for f in 0..files {
            fs::write(dir.join(format!("f{f:03}")), b"").unwrap();
        }
    }
    for f in 0..files {
        fs::write(t.path().join(format!("f{f:03}")), b"").unwrap();
    }
    t
}

// ---------------------------------------------------------------------------
// Termination over symbolic-link loops (fails on the previous implementation)
// ---------------------------------------------------------------------------

#[test]
fn recursive_glob_over_symlink_loops_terminates_with_the_bash_result() {
    let t = looped_tree();
    // bash 5.2 with globstar gives exactly these six paths on this tree.
    assert_eq!(
        expand_within_time("**/*", t.path().to_path_buf()),
        ["d", "d/f1", "d/f2", "d/up", "self", "top"]
    );
}

#[test]
fn recursive_glob_with_no_match_over_symlink_loops_terminates() {
    let t = looped_tree();
    assert!(expand_within_time("**/no-such-name", t.path().to_path_buf()).is_empty());
}

#[test]
fn non_recursive_components_still_go_through_symlinks() {
    let t = looped_tree();
    assert_eq!(
        expand_within_time("d/up/*", t.path().to_path_buf()),
        ["d/up/d", "d/up/self", "d/up/top"]
    );
    assert_eq!(
        expand_within_time("self/self/top", t.path().to_path_buf()),
        ["self/self/top"]
    );
}

// ---------------------------------------------------------------------------
// Each limit stops the walk, names itself, and returns nothing partial
// ---------------------------------------------------------------------------

#[test]
fn the_match_limit_stops_the_walk_and_names_itself() {
    let t = broad_tree(30, 40); // 1,230 entries
    let limits = GlobLimits {
        max_matches: 1_000,
        ..GlobLimits::DEFAULT
    };
    let started = Instant::now();
    let s = stopped(expand_glob_with_limits("**/*", t.path(), &limits));
    assert!(started.elapsed() < Duration::from_secs(5));

    assert_eq!(s.exceeded.axis, "matches held");
    assert_eq!((s.exceeded.limit, s.exceeded.level), (1_000, 1_001));
    assert_eq!(s.usage.matches.peak(), 1_000);
    assert_eq!(s.pattern, "**/*");
    let message = s.to_string();
    assert!(message.contains("matches held would reach 1001, over the limit of 1000"));
    assert!(message.contains("was not expanded"), "{message}");
}

#[test]
fn the_read_limit_stops_a_pattern_that_matches_nothing() {
    // A cap on matches alone cannot stop this one: nothing ever matches.
    let t = broad_tree(30, 40);
    let limits = GlobLimits {
        max_reads: 500,
        ..GlobLimits::DEFAULT
    };
    let s = stopped(expand_glob_with_limits(
        "**/no-such-name",
        t.path(),
        &limits,
    ));
    assert_eq!(s.exceeded.axis, "file-system reads");
    assert_eq!((s.exceeded.limit, s.exceeded.level), (500, 501));
    assert_eq!(s.usage.matches.peak(), 0);
}

#[test]
fn the_byte_limit_counts_path_length_plus_one() {
    let t = TempDir::new().unwrap();
    for name in ["aaaa", "bbbb", "cccc"] {
        fs::write(t.path().join(name), b"").unwrap();
    }
    // Each match costs 4 + 1 = 5 bytes: two fit in 10, the third does not.
    let limits = GlobLimits {
        max_match_bytes: 10,
        ..GlobLimits::DEFAULT
    };
    let s = stopped(expand_glob_with_limits("*", t.path(), &limits));
    assert_eq!(s.exceeded.axis, "bytes of matches held");
    assert_eq!((s.exceeded.limit, s.exceeded.level), (10, 15));
    assert_eq!(
        s.usage.matches.held(),
        2,
        "the refused match is not counted"
    );
    assert_eq!(s.usage.matches.peak(), 2, "nor does it raise the peak");
    assert_eq!(s.usage.match_bytes.peak(), 10);

    let limits = GlobLimits {
        max_match_bytes: 15,
        ..GlobLimits::DEFAULT
    };
    let ok = expand_glob_with_limits("*", t.path(), &limits).unwrap();
    assert_eq!(ok.usage.match_bytes.peak(), 15);
}

#[test]
fn the_report_is_the_same_on_every_run() {
    let t = broad_tree(30, 40);
    let limits = GlobLimits {
        max_matches: 777,
        ..GlobLimits::DEFAULT
    };
    let first = stopped(expand_glob_with_limits("**/*", t.path(), &limits));
    for _ in 0..3 {
        assert_eq!(
            stopped(expand_glob_with_limits("**/*", t.path(), &limits)),
            first
        );
    }
    // Entries are visited in name order. The top level gives 30 directories
    // and 40 files (70 matches), then d000..d016 give 40 each (750), so the
    // 778th match, the first one refused, is the 28th file of d017.
    assert_eq!(first.at, PathBuf::from("d017"));
    assert_eq!(first.usage.matches.peak(), 777);
}

#[test]
fn default_limits_are_the_documented_values() {
    assert_eq!(
        GlobLimits::default(),
        GlobLimits {
            max_reads: 10_000_000,
            max_matches: 100_000,
            max_match_bytes: 6 * 1024 * 1024,
        }
    );
}

// ---------------------------------------------------------------------------
// Accounting: the reported usage equals a count made directly from the tree
// ---------------------------------------------------------------------------

/// Visible, real (not symbolic-link) directories at or below `dir`, with the
/// number of entries in each.
fn visible_dirs(dir: &Path, out: &mut Vec<u64>) {
    let entries: Vec<_> = fs::read_dir(dir).unwrap().map(|e| e.unwrap()).collect();
    out.push(entries.len() as u64);
    for e in entries {
        let hidden = e.file_name().to_string_lossy().starts_with('.');
        if e.file_type().unwrap().is_dir() && !hidden {
            visible_dirs(&e.path(), out);
        }
    }
}

#[test]
fn reads_for_a_two_level_wildcard_match_a_direct_count() {
    let t = broad_tree(7, 5);
    let e = expand_glob_with_limits("*/*", t.path(), &GlobLimits::DEFAULT).unwrap();
    // Open the top (1) and list its 7 + 5 entries, then open and list each of
    // the 7 directories (1 + 5 each).
    assert_eq!(e.usage.reads.total(), 1 + (7 + 5) + 7 * (1 + 5));
    assert_eq!(e.paths.len(), 35);
    assert_eq!(e.usage.matches.peak(), 35);
}

#[test]
fn reads_for_a_recursive_pattern_match_a_direct_count() {
    let t = broad_tree(4, 3);
    fs::create_dir_all(t.path().join("d001/deep/er")).unwrap();
    fs::create_dir(t.path().join(".hidden")).unwrap();
    fs::write(t.path().join(".hidden/x.rs"), b"").unwrap();
    symlink("d000", t.path().join("link")).unwrap();

    let e = expand_glob_with_limits("**/*.rs", t.path(), &GlobLimits::DEFAULT).unwrap();
    assert!(e.paths.is_empty());

    // `**` lists every visible real directory once, and `*.rs` lists each of
    // them once more: 2 x (open + entries) per directory.
    let mut dirs = Vec::new();
    visible_dirs(t.path(), &mut dirs);
    let expected: u64 = dirs.iter().map(|entries| 2 * (1 + entries)).sum();
    assert_eq!(e.usage.reads.total(), expected);
}

#[test]
fn repeated_recursive_components_read_each_directory_a_bounded_number_of_times() {
    // A chain of 30 nested directories. bash lists a path once per way the
    // pattern can match it (736,281 results for six `**`); each (directory,
    // component) pair is processed once here, so the work stays linear.
    let t = TempDir::new().unwrap();
    let mut p = t.path().to_path_buf();
    for _ in 0..30 {
        p.push("a");
    }
    fs::create_dir_all(&p).unwrap();
    fs::write(p.join("leaf"), b"").unwrap();

    let pattern = "**/*/**/*/**/*/**/*/**/*/**/*";
    let e = expand_glob_with_limits(pattern, t.path(), &GlobLimits::DEFAULT).unwrap();
    assert_eq!(e.paths.len(), 26); // the paths at depth 6 or more, once each
    let entries_in_tree = 31;
    let components = 12;
    assert!(
        e.usage.reads.total() <= 2 * components * entries_in_tree,
        "{} reads",
        e.usage.reads.total()
    );
}

// ---------------------------------------------------------------------------
// Matching rules shared with bash 5.2 (globstar on, dotglob off)
// ---------------------------------------------------------------------------

/// The tree on which bash 5.2 results were recorded:
/// `d/e/g d/f d/up -> .. top .hid .hd/x/y ld/z link -> d`.
fn bash_tree() -> TempDir {
    let t = TempDir::new().unwrap();
    for d in ["d/e", ".hd/x", "ld"] {
        fs::create_dir_all(t.path().join(d)).unwrap();
    }
    for f in ["d/f", "d/e/g", "top", ".hid", ".hd/x/y", "ld/z"] {
        fs::write(t.path().join(f), b"").unwrap();
    }
    symlink("d", t.path().join("link")).unwrap();
    symlink("..", t.path().join("d/up")).unwrap();
    t
}

#[test]
fn results_match_bash_on_the_recorded_tree() {
    let t = bash_tree();
    let cases: &[(&str, &[&str])] = &[
        (
            "**",
            &[
                "d", "d/e", "d/e/g", "d/f", "d/up", "ld", "ld/z", "link", "top",
            ],
        ),
        ("**/", &["d/", "d/e/", "d/up/", "ld/", "link/"]),
        ("d/**", &["d/", "d/e", "d/e/g", "d/f", "d/up"]),
        ("d/**/", &["d/", "d/e/", "d/up/"]),
        (
            "**/*",
            &[
                "d", "d/e", "d/e/g", "d/f", "d/up", "ld", "ld/z", "link", "top",
            ],
        ),
        ("**/e", &["d/e"]),
        ("*/", &["d/", "ld/", "link/"]),
        (".*", &[".hd", ".hid"]),
        (".h*", &[".hd", ".hid"]),
        ("link/*", &["link/e", "link/f", "link/up"]),
        ("**/g", &["d/e/g"]),
        ("d/**/g", &["d/e/g"]),
        (
            "**/**",
            &[
                "d", "d/e", "d/e/g", "d/f", "d/up", "ld", "ld/z", "link", "top",
            ],
        ),
        ("./*", &["./d", "./ld", "./link", "./top"]),
        (".hd/**", &[".hd/", ".hd/x", ".hd/x/y"]),
        ("nomatch*", &[]),
    ];
    for (pattern, bash) in cases {
        let ours: BTreeSet<String> = strings(&expand_glob(pattern, t.path()).unwrap())
            .into_iter()
            .collect();
        let bash: BTreeSet<String> = bash.iter().map(|s| s.to_string()).collect();
        assert_eq!(ours, bash, "pattern {pattern}");
    }
}

#[test]
fn hidden_files_need_a_leading_dot_in_the_pattern() {
    let t = TempDir::new().unwrap();
    for f in [".hid1", ".hid2", "vis"] {
        fs::write(t.path().join(f), b"").unwrap();
    }
    assert_eq!(
        strings(&expand_glob(".*", t.path()).unwrap()),
        [".hid1", ".hid2"]
    );
    assert_eq!(
        strings(&expand_glob(".hid*", t.path()).unwrap()),
        [".hid1", ".hid2"]
    );
    assert_eq!(strings(&expand_glob("*", t.path()).unwrap()), ["vis"]);
    assert_eq!(
        strings(&expand_glob("?hid1", t.path()).unwrap()),
        Vec::<String>::new()
    );
}

#[test]
fn a_name_that_is_not_utf8_is_matched_without_a_panic() {
    use std::os::unix::ffi::OsStrExt;
    let t = TempDir::new().unwrap();
    let odd = std::ffi::OsStr::from_bytes(b"bad\xff.txt");
    if fs::write(t.path().join(odd), b"").is_err() {
        return; // the file system refuses such names; nothing to test
    }
    fs::write(t.path().join("ok.txt"), b"").unwrap();
    let found = expand_glob("*.txt", t.path()).unwrap();
    assert_eq!(found.len(), 2);
    assert!(found.contains(&PathBuf::from(odd)));
}
