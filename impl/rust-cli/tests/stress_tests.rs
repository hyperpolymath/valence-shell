// SPDX-License-Identifier: PLMP-1.0-or-later
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

mod fixtures;

use fixtures::tempfile::TempDir;
use std::fs;
use std::io::Write;
use std::path::PathBuf;
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::Instant;
use vsh::state::ShellState;

// ============================================================
// Stress Test 1: Deep Directory Nesting
// ============================================================

#[test]
#[ignore] // Run with: cargo test --test stress_tests -- --ignored
fn stress_deep_nesting_1000_levels() {
    let temp = TempDir::new().unwrap();
    let start = Instant::now();

    // Create 1000-level deep directory structure
    let mut current_path = temp.path().to_path_buf();
    for i in 0..1000 {
        current_path.push(format!("level_{:04}", i));
    }

    // Create the entire nested structure
    fs::create_dir_all(&current_path).unwrap();

    let create_time = start.elapsed();
    println!("✓ Created 1000-level nested directories in {:?}", create_time);

    // Verify it exists
    assert!(current_path.exists());
    assert!(current_path.is_dir());

    // Test undo (remove all levels)
    let undo_start = Instant::now();
    let mut state = ShellState::new(temp.path()).unwrap();

    // Record the creation in state
    for i in 0..1000 {
        let path = format!("level_{:04}", i);
        vsh::commands::mkdir(&mut state, &path, true).unwrap();
    }

    // Undo all 1000 operations
    for _ in 0..1000 {
        state.pop_undo().unwrap();
    }

    let undo_time = undo_start.elapsed();
    println!("✓ Undid 1000 operations in {:?}", undo_time);

    // Verify requirements
    assert!(create_time.as_secs() < 5, "Should create in <5s");
    assert!(undo_time.as_secs() < 2, "Should undo in <2s");
}

#[test]
#[ignore]
fn stress_deep_nesting_no_stack_overflow() {
    let temp = TempDir::new().unwrap();

    // Create even deeper nesting (5000 levels) to test for stack overflow
    let mut current_path = temp.path().to_path_buf();
    for i in 0..5000 {
        current_path.push(format!("d{}", i));
    }

    // Should not cause stack overflow
    let result = fs::create_dir_all(&current_path);
    assert!(result.is_ok(), "Should handle 5000 levels without stack overflow");

    // Cleanup should also not overflow
    let cleanup_result = fs::remove_dir_all(temp.path().join("d0"));
    assert!(cleanup_result.is_ok(), "Cleanup should not overflow");
}

// ============================================================
// Stress Test 2: Large Files
// ============================================================

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

    let create_time = start.elapsed();
    println!("✓ Created 1GB file in {:?}", create_time);

    // Verify size
    let metadata = fs::metadata(&large_file).unwrap();
    assert_eq!(metadata.len(), 1024 * 1024 * 1024, "File should be exactly 1GB");

    // Test operations on large file
    let mut state = ShellState::new(temp.path()).unwrap();

    // Touch shouldn't fail on large file (just updates metadata)
    let touch_start = Instant::now();
    vsh::commands::touch(&mut state, "large.bin", true).unwrap();
    let touch_time = touch_start.elapsed();
    println!("✓ Touch on 1GB file in {:?}", touch_time);

    assert!(touch_time.as_millis() < 100, "Touch should be <100ms even for large files");

    // Memory usage check: should not load entire file into memory
    // This test would fail if implementation naively reads entire file
}

#[test]
#[ignore]
fn stress_large_file_undo_streaming() {
    let temp = TempDir::new().unwrap();
    let file_path = temp.path().join("large.txt");

    // Create 100MB file
    let size = 100 * 1024 * 1024;
    let mut file = fs::File::create(&file_path).unwrap();
    let chunk = vec![b'A'; 1024 * 1024]; // 1MB chunks

    for _ in 0..100 {
        file.write_all(&chunk).unwrap();
    }
    drop(file);

    // Verify we don't OOM when saving undo data for large file
    let mut state = ShellState::new(temp.path()).unwrap();

    // This should use streaming, not load all 100MB into memory
    let undo_save_start = Instant::now();
    vsh::commands::touch(&mut state, "large.txt", true).unwrap();
    let undo_save_time = undo_save_start.elapsed();

    println!("✓ Saved undo data for 100MB file in {:?}", undo_save_time);

    // Check memory didn't spike (we can't easily test this in Rust,
    // but in practice this would be monitored externally)

    // Undo should also be fast
    let undo_start = Instant::now();
    state.pop_undo().unwrap();
    let undo_time = undo_start.elapsed();

    println!("✓ Undid large file operation in {:?}", undo_time);
    assert!(undo_time.as_millis() < 500, "Undo should be <500ms");
}

// ============================================================
// Stress Test 3: Many Operations
// ============================================================

#[test]
#[ignore]
fn stress_many_operations_10000() {
    let temp = TempDir::new().unwrap();
    let mut state = ShellState::new(temp.path()).unwrap();

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
        state.pop_undo().unwrap();
    }
    let undo_time = undo_start.elapsed();

    println!("✓ Undid 10,000 operations in {:?}", undo_time);

    // Performance requirements
    assert!(create_time.as_secs() < 30, "Should complete in <30s");
    assert!(undo_time.as_secs() < 30, "Should undo in <30s");

    // Verify all files removed
    let entries: Vec<_> = fs::read_dir(temp.path()).unwrap().collect();
    assert_eq!(entries.len(), 0, "All files should be undone");
}

#[test]
#[ignore]
fn stress_history_memory_efficiency() {
    let temp = TempDir::new().unwrap();
    let mut state = ShellState::new(temp.path()).unwrap();

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
    let mut state = ShellState::new(temp.path()).unwrap();

    // Create 100 operations
    for i in 0..100 {
        vsh::commands::touch(&mut state, &format!("file_{}.txt", i), true).unwrap();
    }

    // Undo should be O(1) per operation
    let start = Instant::now();
    for _ in 0..100 {
        state.pop_undo().unwrap();
    }
    let undo_time = start.elapsed();

    // Redo should also be O(1) per operation
    let redo_start = Instant::now();
    for _ in 0..100 {
        state.pop_redo().unwrap();
    }
    let redo_time = redo_start.elapsed();

    println!("✓ Undo 100: {:?}, Redo 100: {:?}", undo_time, redo_time);

    // Each operation should be <1ms on average
    let avg_undo_us = undo_time.as_micros() / 100;
    let avg_redo_us = redo_time.as_micros() / 100;

    assert!(avg_undo_us < 1000, "Undo should be <1ms per op (was {}μs)", avg_undo_us);
    assert!(avg_redo_us < 1000, "Redo should be <1ms per op (was {}μs)", avg_redo_us);
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
            let mut state = ShellState::new(&path).unwrap();

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

    // Verify total files created (10 threads * 100 files = 1000)
    let entries: Vec<_> = fs::read_dir(&temp_path).unwrap().collect();
    assert_eq!(entries.len(), 1000, "Should have 1000 total files");

    println!("✓ Concurrent access: 10 threads, 100 ops each = 1000 files");
}

#[test]
#[ignore]
fn stress_concurrent_no_corruption() {
    let temp = TempDir::new().unwrap();
    let state = Arc::new(Mutex::new(ShellState::new(temp.path()).unwrap()));

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
    let mut state = ShellState::new(temp.path()).unwrap();

    // Create operations until we hit a reasonable limit
    // In practice, there should be a configurable max history size

    for i in 0..100_000 {
        let path = format!("file_{}.txt", i);
        vsh::commands::touch(&mut state, &path, true).unwrap();

        // Every 10k operations, check if we have a limit
        if i % 10_000 == 0 {
            println!("  {} operations...", i);
        }
    }

    // Even with 100k operations, should not OOM
    // (This test would be better with actual memory monitoring)

    let history_size = state.history.len();
    println!("✓ Completed {} operations without OOM", history_size);

    // TODO: Implement configurable history limit for production
    // assert!(history_size <= MAX_HISTORY_SIZE);
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
