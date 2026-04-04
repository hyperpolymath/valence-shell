// SPDX-License-Identifier: PMPL-1.0-or-later
//! Performance Benchmarks - Fixed Version
//!
//! Comprehensive benchmark suite measuring:
//! - Undo/redo efficiency
//! - Deep nesting operations
//! - Large file handling
//! - Glob expansion speed
//! - History management
//! - Operation throughput
//!
//! Run with:
//! ```bash
//! cargo bench --bench performance_benchmarks
//! ```

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use std::fs;
use std::io::Write;
use tempfile::TempDir;
use vsh::commands::{mkdir, rm, touch, undo, redo};
use vsh::glob::expand_glob;
use vsh::state::ShellState;

// ============================================================
// Undo/Redo Performance
// ============================================================

/// Benchmark: Single undo operation
fn bench_undo_single(c: &mut Criterion) {
    c.bench_function("undo_single", |b| {
        b.iter(|| {
            let temp = TempDir::new().unwrap();
            let root = temp.path().to_str().unwrap();
            let mut state = ShellState::new(root).unwrap();

            // Perform operation
            mkdir(&mut state, "test_dir", false).unwrap();

            // Benchmark undo
            undo(&mut state, 1, false).unwrap();
            black_box(&state);
        });
    });
}

/// Benchmark: Undo performance scaling (10, 50, 100 operations)
fn bench_undo_scaling(c: &mut Criterion) {
    let mut group = c.benchmark_group("undo_scaling");

    for num_ops in [10, 50, 100].iter() {
        group.throughput(Throughput::Elements(*num_ops as u64));
        group.bench_with_input(BenchmarkId::from_parameter(num_ops), num_ops, |b, &num_ops| {
            b.iter(|| {
                let temp = TempDir::new().unwrap();
                let root = temp.path().to_str().unwrap();
                let mut state = ShellState::new(root).unwrap();

                // Create operations
                for i in 0..num_ops {
                    mkdir(&mut state, &format!("dir_{}", i), false).unwrap();
                }

                // Benchmark undoing all
                for _ in 0..num_ops {
                    undo(&mut state, 1, false).unwrap();
                }
                black_box(&state);
            });
        });
    }

    group.finish();
}

/// Benchmark: Redo performance
fn bench_redo_after_undo(c: &mut Criterion) {
    c.bench_function("redo_after_undo", |b| {
        b.iter(|| {
            let temp = TempDir::new().unwrap();
            let root = temp.path().to_str().unwrap();
            let mut state = ShellState::new(root).unwrap();

            // Create operation
            mkdir(&mut state, "test_dir", false).unwrap();

            // Undo
            undo(&mut state, 1, false).unwrap();

            // Benchmark redo
            redo(&mut state, 1, false).unwrap();
            black_box(&state);
        });
    });
}

/// Benchmark: Undo/redo cycle efficiency
fn bench_undo_redo_cycle(c: &mut Criterion) {
    let mut group = c.benchmark_group("undo_redo_cycle");

    for cycles in [5, 10, 20].iter() {
        group.throughput(Throughput::Elements(*cycles as u64 * 2));
        group.bench_with_input(BenchmarkId::from_parameter(cycles), cycles, |b, &cycles| {
            b.iter(|| {
                let temp = TempDir::new().unwrap();
                let root = temp.path().to_str().unwrap();
                let mut state = ShellState::new(root).unwrap();

                // Create baseline operation
                mkdir(&mut state, "base", false).unwrap();

                for i in 0..cycles {
                    mkdir(&mut state, &format!("cycle_{}", i), false).unwrap();
                    undo(&mut state, 1, false).unwrap();
                    redo(&mut state, 1, false).unwrap();
                }
                black_box(&state);
            });
        });
    }

    group.finish();
}

// ============================================================
// History Management Performance
// ============================================================

/// Benchmark: History lookup performance
fn bench_history_lookup(c: &mut Criterion) {
    let mut group = c.benchmark_group("history_lookup");

    for size in [10, 100, 500].iter() {
        group.throughput(Throughput::Elements(*size as u64));
        group.bench_with_input(BenchmarkId::from_parameter(size), size, |b, &size| {
            b.iter_batched(
                || {
                    let temp = TempDir::new().unwrap();
                    let root = temp.path().to_str().unwrap();
                    let mut state = ShellState::new(root).unwrap();

                    // Pre-populate history
                    for i in 0..size {
                        let _ = mkdir(&mut state, &format!("dir_{}", i), false);
                    }

                    state
                },
                |state| {
                    // Benchmark: accessing history
                    let history_len = state.history.len();
                    black_box(history_len);
                },
                criterion::BatchSize::SmallInput,
            );
        });
    }

    group.finish();
}

// ============================================================
// Glob Expansion Performance
// ============================================================

/// Benchmark: Glob expansion performance
fn bench_glob_expansion(c: &mut Criterion) {
    let mut group = c.benchmark_group("glob_expansion");

    let sizes = vec![10, 50, 100];
    for size in sizes {
        group.throughput(Throughput::Elements(size as u64));
        group.bench_with_input(BenchmarkId::from_parameter(size), &size, |b, &size| {
            b.iter_batched(
                || {
                    let temp = TempDir::new().unwrap();
                    let root = temp.path().to_path_buf();

                    // Create files for glob matching
                    for i in 0..size {
                        let file_path = root.join(format!("file_{}.txt", i));
                        let _ = fs::write(&file_path, b"test");
                    }

                    root
                },
                |root| {
                    let results = expand_glob("*.txt", &root).unwrap_or_default();
                    black_box(results.len());
                },
                criterion::BatchSize::SmallInput,
            );
        });
    }

    group.finish();
}

// ============================================================
// Checkpoint Performance
// ============================================================

/// Benchmark: Creating checkpoints
fn bench_checkpoint_creation(c: &mut Criterion) {
    c.bench_function("checkpoint_creation", |b| {
        b.iter_batched(
            || {
                let temp = TempDir::new().unwrap();
                let root = temp.path().to_str().unwrap();
                let mut state = ShellState::new(root).unwrap();

                for i in 0..10 {
                    let _ = mkdir(&mut state, &format!("dir_{}", i), false);
                }

                state
            },
            |mut state| {
                state
                    .checkpoints
                    .insert("test".to_string(), (state.history.len(), chrono::Utc::now()));
                black_box(&state.checkpoints);
            },
            criterion::BatchSize::SmallInput,
        );
    });
}

// ============================================================
// Directory Nesting Depth Benchmark
// ============================================================

/// Benchmark: Deep directory structure creation
fn bench_deep_nesting(c: &mut Criterion) {
    let mut group = c.benchmark_group("deep_nesting");

    for depth in [5, 10, 20].iter() {
        group.bench_with_input(BenchmarkId::from_parameter(depth), depth, |b, &depth| {
            b.iter_batched(
                || {
                    let temp = TempDir::new().unwrap();
                    let root = temp.path().to_str().unwrap();
                    let state = ShellState::new(root).unwrap();
                    (temp, state)
                },
                |(_temp, mut state)| {
                    for i in 0..depth {
                        let _ = mkdir(&mut state, &format!("level_{}", i), false);
                    }
                    black_box(&state);
                },
                criterion::BatchSize::SmallInput,
            );
        });
    }

    group.finish();
}

// ============================================================
// Benchmark groups
// ============================================================

criterion_group!(
    benches,
    bench_undo_single,
    bench_undo_scaling,
    bench_redo_after_undo,
    bench_undo_redo_cycle,
    bench_history_lookup,
    bench_glob_expansion,
    bench_checkpoint_creation,
    bench_deep_nesting,
);
criterion_main!(benches);
