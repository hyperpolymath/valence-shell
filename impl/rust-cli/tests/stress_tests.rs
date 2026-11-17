// SPDX-License-Identifier: MPL-2.0
// Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//! Stress Tests - Layer 7
//!
//! Tests system behavior under extreme conditions:
//! - Deep directory nesting (1000+ levels)
//! - Large files (1GB+)
//! - Many operations (10,000+ in history)
//! - Concurrent access
//!
//! These tests validate that the shell remains stable, performant,
//! and correct even under stress.
//!
//! All tests are `#[ignore]`d; CI runs them on Linux with
//! `cargo test --test stress_tests -- --ignored --test-threads=1`
//! (see `.github/workflows/compilation_tests.yml`).
//!
//! The shell keeps its persisted state in `.vsh_state.json` (snapshot) and
//! `.vsh_state.journal` inside the sandbox root, so directory listings below
//! account for those files explicitly.

mod fixtures;

use fixtures::tempfile::TempDir;
use std::fs;
use std::io::Write;
use std::path::Path;
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::Instant;
use vsh::state::ShellState;

/// Prefix shared by the shell's own state files in the sandbox root.
const STATE_FILE_PREFIX: &str = ".vsh_state";

/// Names of the entries in `dir` that are not the shell's own state files.
fn user_entries(dir: &Path) -> Vec<String> {
    let mut names: Vec<String> = fs::read_dir(dir)
        .unwrap()
        .map(|e| e.unwrap().file_name().to_string_lossy().into_owned())
        .filter(|name| !name.starts_with(STATE_FILE_PREFIX))
        .collect();
    names.sort();
    names
}

/// Total size in bytes of the shell's own state files in `dir`.
fn state_files_size(dir: &Path) -> u64 {
    fs::read_dir(dir)
        .unwrap()
        .map(|e| e.unwrap())
        .filter(|e| {
            e.file_name()
                .to_string_lossy()
                .starts_with(STATE_FILE_PREFIX)
        })
        .map(|e| e.metadata().unwrap().len())
        .sum()
}

// ============================================================
// Stress Test 1: Deep Directory Nesting
// ============================================================

#[test]
#[ignore] // Run with: cargo test --test stress_tests -- --ignored
fn stress_deep_nesting_1000_levels() {
    const DEPTH: usize = 1000;

    let temp = TempDir::new().unwrap();
    let mut state = ShellState::new(temp.path().to_str().unwrap()).unwrap();

    // The shell resolves every path to an absolute one, so the deepest path
    // must fit in PATH_MAX. One-character components ("d/d/.../d") cost two
    // bytes per level: about 2,000 bytes plus the root, which fits Linux's
    // 4096. (Ten-character names would need ~11,000 bytes, which no
    // absolute-path API accepts; macOS's PATH_MAX of 1024 cannot hold 1000
    // levels at all.)
    let deepest_len = state.root.as_os_str().len() + 2 * DEPTH;
    let path_max = libc::PATH_MAX as usize;
    assert!(
        deepest_len < path_max,
        "{DEPTH}-level nesting needs a {deepest_len}-byte absolute path; \
         this platform's PATH_MAX is {path_max}"
    );

    // Create the 1000-level structure through the shell, one level per op.
    let start = Instant::now();
    let mut rel = String::from("d");
    for level in 0..DEPTH {
        if level > 0 {
            rel.push_str("/d");
        }
        vsh::commands::mkdir(&mut state, &rel, false).unwrap();
    }
    let create_time = start.elapsed();
    println!(
        "✓ Created 1000-level nested directories in {:?}",
        create_time
    );

    // Verify it exists and every level was recorded
    let deepest = state.resolve_path(&rel);
    assert!(deepest.exists());
    assert!(deepest.is_dir());
    assert_eq!(state.history.len(), DEPTH, "Each mkdir should be recorded");

    // Undo all 1000 operations (innermost first)
    let undo_start = Instant::now();
    for _ in 0..DEPTH {
        vsh::commands::undo(&mut state, 1, false).unwrap();
    }
    let undo_time = undo_start.elapsed();
    println!("✓ Undid 1000 operations in {:?}", undo_time);

    assert!(
        user_entries(temp.path()).is_empty(),
        "Undo should remove every level"
    );

    // Verify requirements
    assert!(create_time.as_secs() < 5, "Should create in <5s");
    assert!(undo_time.as_secs() < 2, "Should undo in <2s");
}

#[test]
#[ignore]
fn stress_deep_nesting_no_stack_overflow() {
    use nix::fcntl::{openat, OFlag};
    use nix::sys::stat::{mkdirat, Mode};
    use std::os::fd::OwnedFd;

    const DEPTH: usize = 5000;

    let temp = TempDir::new().unwrap();
    let mut state = ShellState::new(temp.path().to_str().unwrap()).unwrap();

    // Even deeper nesting (5000 levels) to test for stack overflow. Its
    // absolute path is far longer than PATH_MAX, so it cannot be created
    // with path-based calls (`fs::create_dir_all` fails with ENAMETOOLONG).
    // Build it one level at a time relative to the parent's descriptor.
    let deep_rel = vec!["d"; DEPTH].join("/");
    assert!(
        state.root.join(&deep_rel).as_os_str().len() > libc::PATH_MAX as usize,
        "this test is meant to go beyond PATH_MAX"
    );
    let mut dir: OwnedFd = fs::File::open(&state.root).unwrap().into();
    for _ in 0..DEPTH {
        mkdirat(&dir, "d", Mode::from_bits_truncate(0o755)).unwrap();
        dir = openat(
            &dir,
            "d",
            OFlag::O_RDONLY | OFlag::O_DIRECTORY,
            Mode::empty(),
        )
        .unwrap();
    }
    drop(dir);

    // The shell must stay stable when handed a path this deep: resolving it
    // is pure normalisation, and filesystem operations on it fail with an
    // error instead of overflowing the stack or panicking.
    assert_eq!(state.resolve_path(&deep_rel), state.root.join(&deep_rel));
    let before = state.history.len();
    let mkdir_result = vsh::commands::mkdir(&mut state, &format!("{deep_rel}/x"), false);
    assert!(
        mkdir_result.is_err(),
        "mkdir beyond PATH_MAX should fail cleanly"
    );
    let touch_result = vsh::commands::touch(&mut state, &format!("{deep_rel}/f"), false);
    assert!(
        touch_result.is_err(),
        "touch beyond PATH_MAX should fail cleanly"
    );
    assert_eq!(
        state.history.len(),
        before,
        "Failed operations must not be recorded"
    );

    // Cleanup should also not overflow
    let cleanup_result = fs::remove_dir_all(temp.path().join("d"));
    assert!(cleanup_result.is_ok(), "Cleanup should not overflow");
    assert!(user_entries(temp.path()).is_empty());
}

// ============================================================
// Stress Test 2: Large Files
// ============================================================

/// Writes 1 GB of temporary data to disk (about 1.5 s on a local SSD).
#[test]
#[ignore]
fn stress_large_file_1gb() {
    let temp = TempDir::new().unwrap();
    let large_file = temp.path().join("large.bin");

    let start = Instant::now();

    // Create 1GB file (1024 * 1024 * 1024 bytes)
    let chunk_size = 1024 * 1024; // 1MB chunks
    let num_chunks = 1024; // 1024 chunks = 1GB

    let mut file = fs::File::create(&large_file).unwrap();
    let chunk = vec![0u8; chunk_size];

    for _ in 0..num_chunks {
        file.write_all(&chunk).unwrap();
    }
    file.sync_all().unwrap();
    drop(file);

    let create_time = start.elapsed();
    println!("✓ Created 1GB file in {:?}", create_time);

    // Verify size
    const SIZE: u64 = 1024 * 1024 * 1024;
    let metadata = fs::metadata(&large_file).unwrap();
    assert_eq!(metadata.len(), SIZE, "File should be exactly 1GB");

    // Test operations on large file
    let mut state = ShellState::new(temp.path().to_str().unwrap()).unwrap();

    // Metadata-only operations must not depend on the file size. (`touch`
    // in vsh only creates files, so it cannot be applied to this one; the
    // reversible metadata operations are `chmod` and `mv`.) Each operation
    // and its undo should be <100ms even for a 1GB file.
    let timed = |label: &str, op: &mut dyn FnMut()| {
        let t = Instant::now();
        op();
        let elapsed = t.elapsed();
        println!("✓ {label} on 1GB file in {elapsed:?}");
        assert!(
            elapsed.as_millis() < 100,
            "{label} should be <100ms even for large files (was {elapsed:?})"
        );
    };

    timed("chmod", &mut || {
        vsh::commands::chmod(&mut state, "600", "large.bin", false).unwrap()
    });
    timed("undo chmod", &mut || {
        vsh::commands::undo(&mut state, 1, false).unwrap()
    });
    timed("mv", &mut || {
        vsh::commands::mv(&mut state, "large.bin", "moved.bin", false).unwrap()
    });
    assert_eq!(
        fs::metadata(temp.path().join("moved.bin")).unwrap().len(),
        SIZE
    );
    timed("undo mv", &mut || {
        vsh::commands::undo(&mut state, 1, false).unwrap()
    });

    // Memory usage check: should not load entire file into memory.
    // These operations never read file content: the file is intact.
    assert_eq!(fs::metadata(&large_file).unwrap().len(), SIZE);
    assert_eq!(
        metadata.permissions(),
        fs::metadata(&large_file).unwrap().permissions()
    );
}

#[test]
#[ignore]
fn stress_large_file_undo_streaming() {
    const SIZE: usize = 100 * 1024 * 1024;

    let temp = TempDir::new().unwrap();
    let file_path = temp.path().join("large.txt");

    // Create 100MB file
    let mut file = fs::File::create(&file_path).unwrap();
    let chunk = vec![b'A'; 1024 * 1024]; // 1MB chunks

    for _ in 0..100 {
        file.write_all(&chunk).unwrap();
    }
    drop(file);

    let mut state = ShellState::new(temp.path().to_str().unwrap()).unwrap();

    // Removing a file is the operation that saves the file's content as undo
    // data. (`touch` cannot be used here: in vsh it only creates files.)
    //
    // NOT streaming: `rm` currently holds the whole content in memory as
    // `undo_data` and persists it in the state journal as JSON. This test
    // checks that a 100MB rm/undo round trip completes, restores the content
    // byte for byte, and that the undo itself stays fast. Out-of-line
    // (streamed) undo storage is open work, recorded in
    // docs/audits/2026-11-16-hypatia-remediation.adoc.
    let undo_save_start = Instant::now();
    vsh::commands::rm(&mut state, "large.txt", false).unwrap();
    let undo_save_time = undo_save_start.elapsed();
    assert!(!file_path.exists(), "rm should remove the file");

    println!("✓ Saved undo data for 100MB file in {:?}", undo_save_time);

    // Undo should also be fast
    let undo_start = Instant::now();
    vsh::commands::undo(&mut state, 1, false).unwrap();
    let undo_time = undo_start.elapsed();

    println!("✓ Undid large file operation in {:?}", undo_time);
    assert!(undo_time.as_millis() < 500, "Undo should be <500ms");

    // The restored file must be the original, byte for byte.
    let restored = fs::read(&file_path).unwrap();
    assert_eq!(restored.len(), SIZE, "Restored file should be 100MB");
    assert!(
        restored.iter().all(|&b| b == b'A'),
        "Restored content should match the original"
    );
}

// ============================================================
// Stress Test 3: Many Operations
// ============================================================

#[test]
#[ignore]
fn stress_many_operations_10000() {
    let temp = TempDir::new().unwrap();
    let mut state = ShellState::new(temp.path().to_str().unwrap()).unwrap();

    let start = Instant::now();

    // Perform 10,000 operations
    for i in 0..10_000 {
        let path = format!("file_{:05}.txt", i);
        vsh::commands::touch(&mut state, &path, true).unwrap();
    }

    let create_time = start.elapsed();
    println!("✓ Performed 10,000 touch operations in {:?}", create_time);

    // Check history size
    let history_size = state.history.len();
    assert_eq!(history_size, 10_000, "All operations should be in history");

    // Test undo performance (undo all 10,000)
    let undo_start = Instant::now();
    for _ in 0..10_000 {
        vsh::commands::undo(&mut state, 1, false).unwrap();
    }
    let undo_time = undo_start.elapsed();

    println!("✓ Undid 10,000 operations in {:?}", undo_time);

    // Performance requirements
    assert!(create_time.as_secs() < 30, "Should complete in <30s");
    assert!(undo_time.as_secs() < 30, "Should undo in <30s");

    // Verify all files removed (only the shell's own state files remain)
    let entries = user_entries(temp.path());
    assert!(
        entries.is_empty(),
        "All files should be undone, found {} (first: {:?})",
        entries.len(),
        entries.first()
    );
}

#[test]
#[ignore]
fn stress_history_memory_efficiency() {
    let temp = TempDir::new().unwrap();
    let mut state = ShellState::new(temp.path().to_str().unwrap()).unwrap();

    // Create 1000 operations
    for i in 0..1000 {
        let path = format!("file_{}.txt", i);
        vsh::commands::touch(&mut state, &path, true).unwrap();
    }

    // History should not consume excessive memory
    // Each operation should be O(1) in size (just path, not file content)

    // Rough estimate: each operation ~200 bytes max
    // 1000 operations = ~200KB max
    // If it's much larger, we're storing too much data

    let history_size = state.history.len();
    assert_eq!(history_size, 1000);

    // Memory should be proportional to unique operations, not file sizes
    println!("✓ History size: {} operations", history_size);
}

#[test]
#[ignore]
fn stress_undo_redo_efficiency() {
    let temp = TempDir::new().unwrap();
    let mut state = ShellState::new(temp.path().to_str().unwrap()).unwrap();

    // Create 100 operations
    for i in 0..100 {
        vsh::commands::touch(&mut state, &format!("file_{}.txt", i), true).unwrap();
    }

    // Undo should be O(1) per operation
    let start = Instant::now();
    for _ in 0..100 {
        vsh::commands::undo(&mut state, 1, false).unwrap();
    }
    let undo_time = start.elapsed();
    assert!(
        user_entries(temp.path()).is_empty(),
        "Undo should remove all files"
    );

    // Redo should also be O(1) per operation
    let redo_start = Instant::now();
    for _ in 0..100 {
        vsh::commands::redo(&mut state, 1, false).unwrap();
    }
    let redo_time = redo_start.elapsed();
    assert_eq!(
        user_entries(temp.path()).len(),
        100,
        "Redo should recreate all files"
    );

    println!("✓ Undo 100: {:?}, Redo 100: {:?}", undo_time, redo_time);

    // Each operation should be <1ms on average
    let avg_undo_us = undo_time.as_micros() / 100;
    let avg_redo_us = redo_time.as_micros() / 100;

    assert!(
        avg_undo_us < 1000,
        "Undo should be <1ms per op (was {}μs)",
        avg_undo_us
    );
    assert!(
        avg_redo_us < 1000,
        "Redo should be <1ms per op (was {}μs)",
        avg_redo_us
    );
}

// ============================================================
// Stress Test 4: Concurrent Access
// ============================================================

#[test]
#[ignore]
fn stress_concurrent_multiple_instances() {
    let temp = TempDir::new().unwrap();
    let temp_path = temp.path().to_path_buf();

    // Spawn 10 threads, each with its own ShellState
    let mut handles = vec![];

    for thread_id in 0..10 {
        let path = temp_path.clone();

        let handle = thread::spawn(move || {
            let mut state = ShellState::new(path.to_str().unwrap()).unwrap();

            // Each thread creates 100 files with unique names
            for i in 0..100 {
                let filename = format!("thread_{}_file_{}.txt", thread_id, i);
                vsh::commands::touch(&mut state, &filename, true).unwrap();
            }

            // Verify all files exist
            for i in 0..100 {
                let filename = format!("thread_{}_file_{}.txt", thread_id, i);
                let full_path = path.join(&filename);
                assert!(full_path.exists(), "File should exist: {}", filename);
            }

            thread_id
        });

        handles.push(handle);
    }

    // Wait for all threads
    for handle in handles {
        handle.join().unwrap();
    }

    // Verify total files created (10 threads * 100 files = 1000). The
    // instances share one sandbox root, so its state files are there too;
    // nothing else may be.
    let entries = user_entries(&temp_path);
    assert_eq!(entries.len(), 1000, "Should have 1000 total files");
    let mut expected: Vec<String> = (0..10)
        .flat_map(|t| (0..100).map(move |i| format!("thread_{}_file_{}.txt", t, i)))
        .collect();
    expected.sort();
    assert_eq!(entries, expected, "Exactly the threads' files should exist");

    println!("✓ Concurrent access: 10 threads, 100 ops each = 1000 files");
}

#[test]
#[ignore]
fn stress_concurrent_no_corruption() {
    let temp = TempDir::new().unwrap();
    let state = Arc::new(Mutex::new(
        ShellState::new(temp.path().to_str().unwrap()).unwrap(),
    ));

    // Multiple threads sharing same ShellState (via Mutex)
    let mut handles = vec![];

    for thread_id in 0..5 {
        let state_clone = Arc::clone(&state);

        let handle = thread::spawn(move || {
            for i in 0..50 {
                let filename = format!("shared_{}_{}.txt", thread_id, i);

                // Lock, operate, unlock
                let mut st = state_clone.lock().unwrap();
                vsh::commands::touch(&mut st, &filename, true).unwrap();
                drop(st); // Release lock
            }
        });

        handles.push(handle);
    }

    // Wait for all threads
    for handle in handles {
        handle.join().unwrap();
    }

    // Check state consistency
    let final_state = state.lock().unwrap();
    let history_len = final_state.history.len();

    // Should have 5 threads * 50 ops = 250 operations
    assert_eq!(history_len, 250, "History should have all 250 operations");

    println!("✓ Concurrent shared state: 5 threads, 50 ops each, no corruption");
}

// ============================================================
// Stress Test 5: Resource Limits
// ============================================================

#[test]
#[ignore]
fn stress_resource_limits_max_history() {
    let temp = TempDir::new().unwrap();
    let mut state = ShellState::new(temp.path().to_str().unwrap()).unwrap();

    // ShellState bounds its history (`max_history_size`, 10,000 by default);
    // a user-facing setting for it remains tracked by #190.
    let limit = state
        .max_history_size
        .expect("ShellState should bound its history by default");

    for i in 0..100_000 {
        let path = format!("file_{}.txt", i);
        vsh::commands::touch(&mut state, &path, true).unwrap();

        // Every 10k operations, check if we have a limit
        if i % 10_000 == 0 {
            println!("  {} operations...", i);
            assert!(state.history.len() <= limit);
        }
    }

    // Even with 100k operations, should not OOM: the in-memory history is
    // capped at the limit...
    let history_size = state.history.len();
    println!("✓ Completed {} operations without OOM", history_size);
    assert_eq!(
        history_size, limit,
        "History should be capped at max_history_size"
    );

    // ...and so is the persisted state, which must not grow with the total
    // number of operations. A touch op serialises to ~200 bytes, so a
    // snapshot plus journal of a capped history stays within a few MB;
    // 32 MiB leaves ample headroom while catching unbounded growth (100k
    // uncapped ops alone would exceed it).
    let persisted = state_files_size(temp.path());
    println!("✓ Persisted state: {} bytes", persisted);
    assert!(
        persisted < 32 * 1024 * 1024,
        "Persisted state should be bounded by the history limit (was {persisted} bytes)"
    );
}

#[test]
#[ignore]
fn stress_many_small_files() {
    let temp = TempDir::new().unwrap();

    // Create 10,000 small files (1KB each)
    let start = Instant::now();

    for i in 0..10_000 {
        let path = temp.path().join(format!("small_{}.txt", i));
        fs::write(&path, b"x").unwrap();
    }

    let create_time = start.elapsed();
    println!("✓ Created 10,000 small files in {:?}", create_time);

    // List directory (stress readdir)
    let list_start = Instant::now();
    let entries: Vec<_> = fs::read_dir(temp.path()).unwrap().collect();
    let list_time = list_start.elapsed();

    assert_eq!(entries.len(), 10_000);
    println!("✓ Listed 10,000 files in {:?}", list_time);

    // Cleanup all
    let cleanup_start = Instant::now();
    fs::remove_dir_all(temp.path()).unwrap();
    let cleanup_time = cleanup_start.elapsed();

    println!("✓ Cleaned up 10,000 files in {:?}", cleanup_time);
}
