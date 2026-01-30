// SPDX-License-Identifier: PLMP-1.0-or-later
//! Performance Benchmarks - Layer 10
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
//! cargo bench --bench performance_benchmarks -- --baseline main
//! ```

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use std::fs;
use std::io::Write;
use tempfile::TempDir;
use vsh::commands::{mkdir, rmdir, rm, touch};
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
            let mut state = ShellState::new(temp.path()).unwrap();

            // Perform operation
            mkdir(&mut state, "test_dir", true).unwrap();

            // Benchmark undo
            let start = std::time::Instant::now();
            state.pop_undo().unwrap();
            black_box(start.elapsed());
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
                let mut state = ShellState::new(temp.path()).unwrap();

                // Create operations
                for i in 0..num_ops {
                    mkdir(&mut state, &format!("dir_{}", i), true).unwrap();
                }

                // Benchmark undoing all
                let start = std::time::Instant::now();
                for _ in 0..num_ops {
                    state.pop_undo().unwrap();
                }
                black_box(start.elapsed());
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
            let mut state = ShellState::new(temp.path()).unwrap();

            // Create operation
            mkdir(&mut state, "test_dir", true).unwrap();

            // Undo
            state.pop_undo().unwrap();

            // Benchmark redo
            let start = std::time::Instant::now();
            state.pop_redo().unwrap();
            black_box(start.elapsed());
        });
    });
}

/// Benchmark: Undo/redo cycle efficiency
fn bench_undo_redo_cycle(c: &mut Criterion) {
    let mut group = c.benchmark_group("undo_redo_cycle");

    for num_cycles in [5, 10, 20].iter() {
        group.throughput(Throughput::Elements(*num_cycles as u64));
        group.bench_with_input(
            BenchmarkId::from_parameter(num_cycles),
            num_cycles,
            |b, &num_cycles| {
                b.iter(|| {
                    let temp = TempDir::new().unwrap();
                    let mut state = ShellState::new(temp.path()).unwrap();

                    // Perform operation
                    mkdir(&mut state, "test_dir", true).unwrap();

                    // Benchmark undo/redo cycles
                    let start = std::time::Instant::now();
                    for _ in 0..num_cycles {
                        state.pop_undo().unwrap();
                        state.pop_redo().unwrap();
                    }
                    black_box(start.elapsed());
                });
            },
        );
    }

    group.finish();
}

// ============================================================
// Deep Nesting Performance
// ============================================================

/// Benchmark: Creating deep directory structure
fn bench_deep_nesting_create(c: &mut Criterion) {
    let mut group = c.benchmark_group("deep_nesting_create");

    for depth in [50, 100, 200].iter() {
        group.throughput(Throughput::Elements(*depth as u64));
        group.bench_with_input(BenchmarkId::from_parameter(depth), depth, |b, &depth| {
            b.iter(|| {
                let temp = TempDir::new().unwrap();
                let mut state = ShellState::new(temp.path()).unwrap();

                // Build deep path
                let mut path = String::new();
                for i in 0..depth {
                    if i > 0 {
                        path.push('/');
                    }
                    path.push_str(&format!("level_{}", i));
                }

                // Benchmark creation
                let start = std::time::Instant::now();
                mkdir(&mut state, &path, true).unwrap();
                black_box(start.elapsed());
            });
        });
    }

    group.finish();
}

/// Benchmark: Navigating deep directory structure
fn bench_deep_nesting_navigate(c: &mut Criterion) {
    c.bench_function("deep_nesting_navigate_100", |b| {
        // Pre-create structure
        let temp = TempDir::new().unwrap();
        let mut current_path = temp.path().to_path_buf();
        for i in 0..100 {
            current_path.push(format!("level_{}", i));
        }
        fs::create_dir_all(&current_path).unwrap();

        b.iter(|| {
            // Benchmark stat/exists check on deep path
            let start = std::time::Instant::now();
            let exists = current_path.exists();
            assert!(exists);
            black_box(start.elapsed());
        });
    });
}

// ============================================================
// Large File Operations
// ============================================================

/// Benchmark: Touch on large file (metadata only)
fn bench_large_file_touch(c: &mut Criterion) {
    let temp = TempDir::new().unwrap();
    let large_file = temp.path().join("large.bin");

    // Create 10MB file
    let mut file = fs::File::create(&large_file).unwrap();
    file.write_all(&vec![0u8; 10 * 1024 * 1024]).unwrap();
    drop(file);

    c.bench_function("large_file_touch_10mb", |b| {
        b.iter(|| {
            let mut state = ShellState::new(temp.path()).unwrap();

            // Benchmark touch (should not read file content)
            let start = std::time::Instant::now();
            touch(&mut state, "large.bin", true).unwrap();
            black_box(start.elapsed());
        });
    });
}

/// Benchmark: Undo data storage for large file
fn bench_large_file_undo_storage(c: &mut Criterion) {
    c.bench_function("large_file_undo_storage_1mb", |b| {
        b.iter(|| {
            let temp = TempDir::new().unwrap();
            let file_path = temp.path().join("file.bin");

            // Create 1MB file
            fs::write(&file_path, vec![0u8; 1024 * 1024]).unwrap();

            let mut state = ShellState::new(temp.path()).unwrap();

            // Benchmark undo data creation (should use streaming)
            let start = std::time::Instant::now();
            touch(&mut state, "file.bin", true).unwrap();
            black_box(start.elapsed());
        });
    });
}

// ============================================================
// Glob Expansion Performance
// ============================================================

/// Benchmark: Glob expansion with many files
fn bench_glob_expansion(c: &mut Criterion) {
    let mut group = c.benchmark_group("glob_expansion");

    for num_files in [100, 500, 1000].iter() {
        group.throughput(Throughput::Elements(*num_files as u64));
        group.bench_with_input(
            BenchmarkId::from_parameter(num_files),
            num_files,
            |b, &num_files| {
                // Pre-create files
                let temp = TempDir::new().unwrap();
                for i in 0..num_files {
                    fs::write(temp.path().join(format!("file_{}.txt", i)), b"test").unwrap();
                }

                b.iter(|| {
                    let pattern = format!("{}/*.txt", temp.path().display());

                    // Benchmark glob expansion
                    let start = std::time::Instant::now();
                    let expanded = expand_glob(&pattern).unwrap();
                    assert_eq!(expanded.len(), num_files);
                    black_box(start.elapsed());
                });
            },
        );
    }

    group.finish();
}

/// Benchmark: Recursive glob expansion
fn bench_glob_recursive(c: &mut Criterion) {
    c.bench_function("glob_recursive_**", |b| {
        // Pre-create nested structure
        let temp = TempDir::new().unwrap();
        for level1 in 0..5 {
            for level2 in 0..5 {
                let dir = temp.path().join(format!("dir{}/sub{}", level1, level2));
                fs::create_dir_all(&dir).unwrap();
                for file in 0..4 {
                    fs::write(dir.join(format!("file{}.txt", file)), b"test").unwrap();
                }
            }
        }
        // Total: 5 * 5 * 4 = 100 files

        b.iter(|| {
            let pattern = format!("{}/**/*.txt", temp.path().display());

            // Benchmark recursive glob
            let start = std::time::Instant::now();
            let expanded = expand_glob(&pattern).unwrap();
            assert_eq!(expanded.len(), 100);
            black_box(start.elapsed());
        });
    });
}

// ============================================================
// History Management Performance
// ============================================================

/// Benchmark: History growth with many operations
fn bench_history_growth(c: &mut Criterion) {
    let mut group = c.benchmark_group("history_growth");

    for num_ops in [100, 500, 1000].iter() {
        group.throughput(Throughput::Elements(*num_ops as u64));
        group.bench_with_input(
            BenchmarkId::from_parameter(num_ops),
            num_ops,
            |b, &num_ops| {
                b.iter(|| {
                    let temp = TempDir::new().unwrap();
                    let mut state = ShellState::new(temp.path()).unwrap();

                    // Benchmark many operations
                    let start = std::time::Instant::now();
                    for i in 0..num_ops {
                        touch(&mut state, &format!("file_{}.txt", i), true).unwrap();
                    }
                    black_box(start.elapsed());

                    // Verify history size
                    assert_eq!(state.history.len(), num_ops);
                });
            },
        );
    }

    group.finish();
}

/// Benchmark: History traversal efficiency
fn bench_history_traversal(c: &mut Criterion) {
    c.bench_function("history_traversal_100", |b| {
        // Pre-create history
        let temp = TempDir::new().unwrap();
        let mut state = ShellState::new(temp.path()).unwrap();

        for i in 0..100 {
            touch(&mut state, &format!("file_{}.txt", i), true).unwrap();
        }

        b.iter(|| {
            // Benchmark accessing history items
            let start = std::time::Instant::now();
            for op in &state.history {
                black_box(op);
            }
            black_box(start.elapsed());
        });
    });
}

// ============================================================
// Operation Throughput
// ============================================================

/// Benchmark: mkdir throughput (ops/sec)
fn bench_mkdir_throughput(c: &mut Criterion) {
    let mut group = c.benchmark_group("mkdir_throughput");

    for num_dirs in [50, 100, 200].iter() {
        group.throughput(Throughput::Elements(*num_dirs as u64));
        group.bench_with_input(
            BenchmarkId::from_parameter(num_dirs),
            num_dirs,
            |b, &num_dirs| {
                b.iter(|| {
                    let temp = TempDir::new().unwrap();
                    let mut state = ShellState::new(temp.path()).unwrap();

                    // Benchmark creating many directories
                    let start = std::time::Instant::now();
                    for i in 0..num_dirs {
                        mkdir(&mut state, &format!("dir_{}", i), true).unwrap();
                    }
                    let elapsed = start.elapsed();

                    black_box(elapsed);
                });
            },
        );
    }

    group.finish();
}

/// Benchmark: touch throughput (ops/sec)
fn bench_touch_throughput(c: &mut Criterion) {
    let mut group = c.benchmark_group("touch_throughput");

    for num_files in [50, 100, 200].iter() {
        group.throughput(Throughput::Elements(*num_files as u64));
        group.bench_with_input(
            BenchmarkId::from_parameter(num_files),
            num_files,
            |b, &num_files| {
                b.iter(|| {
                    let temp = TempDir::new().unwrap();
                    let mut state = ShellState::new(temp.path()).unwrap();

                    // Benchmark creating many files
                    let start = std::time::Instant::now();
                    for i in 0..num_files {
                        touch(&mut state, &format!("file_{}.txt", i), true).unwrap();
                    }
                    let elapsed = start.elapsed();

                    black_box(elapsed);
                });
            },
        );
    }

    group.finish();
}

/// Benchmark: Reversible operation pairs (create + delete)
fn bench_reversible_pairs(c: &mut Criterion) {
    let mut group = c.benchmark_group("reversible_pairs");

    for num_pairs in [20, 50, 100].iter() {
        group.throughput(Throughput::Elements(*num_pairs as u64));
        group.bench_with_input(
            BenchmarkId::from_parameter(num_pairs),
            num_pairs,
            |b, &num_pairs| {
                b.iter(|| {
                    let temp = TempDir::new().unwrap();
                    let mut state = ShellState::new(temp.path()).unwrap();

                    // Benchmark create + delete pairs
                    let start = std::time::Instant::now();
                    for i in 0..num_pairs {
                        mkdir(&mut state, &format!("dir_{}", i), true).unwrap();
                        rmdir(&mut state, &format!("dir_{}", i), true).unwrap();
                    }
                    let elapsed = start.elapsed();

                    black_box(elapsed);
                });
            },
        );
    }

    group.finish();
}

// ============================================================
// Memory Efficiency
// ============================================================

/// Benchmark: Memory usage per operation (approximation)
fn bench_operation_memory_footprint(c: &mut Criterion) {
    c.bench_function("operation_memory_footprint", |b| {
        b.iter(|| {
            let temp = TempDir::new().unwrap();
            let mut state = ShellState::new(temp.path()).unwrap();

            // Create 100 operations
            for i in 0..100 {
                touch(&mut state, &format!("file_{}.txt", i), true).unwrap();
            }

            // Each operation should be O(1) in memory (just metadata, not file contents)
            // History should be ~100 * sizeof(Operation) bytes
            // Rough estimate: each operation ~200 bytes max
            // 100 operations = ~20KB max

            let history_size = state.history.len();
            black_box(history_size);
        });
    });
}

criterion_group!(
    undo_redo,
    bench_undo_single,
    bench_undo_scaling,
    bench_redo_after_undo,
    bench_undo_redo_cycle
);

criterion_group!(
    deep_nesting,
    bench_deep_nesting_create,
    bench_deep_nesting_navigate
);

criterion_group!(
    large_files,
    bench_large_file_touch,
    bench_large_file_undo_storage
);

criterion_group!(
    glob_expansion,
    bench_glob_expansion,
    bench_glob_recursive
);

criterion_group!(
    history_management,
    bench_history_growth,
    bench_history_traversal
);

criterion_group!(
    throughput,
    bench_mkdir_throughput,
    bench_touch_throughput,
    bench_reversible_pairs
);

criterion_group!(memory_efficiency, bench_operation_memory_footprint);

criterion_main!(
    undo_redo,
    deep_nesting,
    large_files,
    glob_expansion,
    history_management,
    throughput,
    memory_efficiency
);
