// SPDX-License-Identifier: PMPL-1.0-or-later
//! Benchmarks for core filesystem operations
//!
//! Measures the performance of mkdir, rmdir, touch, rm, and operation sequences.
//!
//! Run with:
//! ```bash
//! cargo bench
//! ```

use criterion::{black_box, criterion_group, criterion_main, Criterion};
use tempfile::tempdir;
use vsh::commands::{mkdir, rmdir, rm, touch};
use vsh::state::ShellState;

/// Benchmark: mkdir operation
fn bench_mkdir(c: &mut Criterion) {
    c.bench_function("mkdir", |b| {
        b.iter(|| {
            let temp = tempdir().unwrap();
            let mut state = ShellState::new(temp.path().to_str().unwrap()).unwrap();

            // Create directory
            mkdir(&mut state, "test_dir", false).unwrap();

            black_box(&state);
        });
    });
}

/// Benchmark: mkdir + rmdir (reversibility)
fn bench_mkdir_rmdir(c: &mut Criterion) {
    c.bench_function("mkdir_rmdir_reversible", |b| {
        b.iter(|| {
            let temp = tempdir().unwrap();
            let mut state = ShellState::new(temp.path().to_str().unwrap()).unwrap();

            mkdir(&mut state, "test_dir", false).unwrap();
            rmdir(&mut state, "test_dir", false).unwrap();

            black_box(&state);
        });
    });
}

/// Benchmark: touch operation
fn bench_touch(c: &mut Criterion) {
    c.bench_function("touch", |b| {
        b.iter(|| {
            let temp = tempdir().unwrap();
            let mut state = ShellState::new(temp.path().to_str().unwrap()).unwrap();

            touch(&mut state, "test_file.txt", false).unwrap();

            black_box(&state);
        });
    });
}

/// Benchmark: touch + rm (reversibility)
fn bench_touch_rm(c: &mut Criterion) {
    c.bench_function("touch_rm_reversible", |b| {
        b.iter(|| {
            let temp = tempdir().unwrap();
            let mut state = ShellState::new(temp.path().to_str().unwrap()).unwrap();

            touch(&mut state, "test_file.txt", false).unwrap();
            rm(&mut state, "test_file.txt", false).unwrap();

            black_box(&state);
        });
    });
}

/// Benchmark: multiple operations (sequence)
fn bench_operation_sequence(c: &mut Criterion) {
    c.bench_function("operation_sequence_5", |b| {
        b.iter(|| {
            let temp = tempdir().unwrap();
            let mut state = ShellState::new(temp.path().to_str().unwrap()).unwrap();

            // Create 5 directories
            for i in 0..5 {
                mkdir(&mut state, &format!("dir{}", i), false).unwrap();
            }

            // Delete them
            for i in 0..5 {
                rmdir(&mut state, &format!("dir{}", i), false).unwrap();
            }

            black_box(&state);
        });
    });
}

criterion_group!(
    benches,
    bench_mkdir,
    bench_mkdir_rmdir,
    bench_touch,
    bench_touch_rm,
    bench_operation_sequence
);
criterion_main!(benches);
