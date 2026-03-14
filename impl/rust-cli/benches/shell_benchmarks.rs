// SPDX-License-Identifier: PMPL-1.0-or-later
//! Shell Benchmarks (TASK 6)
//!
//! Measures:
//! 1. Shell startup time (cold start to state-ready)
//! 2. Command parsing throughput (commands/sec)
//! 3. Pipeline execution overhead
//! 4. State checkpoint/restore cycle time
//!
//! Run with: `cargo bench --bench shell_benchmarks`
//!
//! Author: Jonathan D.A. Jewell

use criterion::{black_box, criterion_group, criterion_main, Criterion, Throughput};
use tempfile::TempDir;
use vsh::commands::{mkdir, rmdir};
use vsh::parser::parse_command;
use vsh::state::ShellState;

// ============================================================
// 1. Shell Startup Time
// ============================================================

/// Benchmark: Cold start from nothing to state-ready
fn bench_shell_startup(c: &mut Criterion) {
    c.bench_function("shell_startup_cold", |b| {
        b.iter(|| {
            let temp = TempDir::new().unwrap();
            let state = ShellState::new(temp.path().to_str().unwrap()).unwrap();
            black_box(&state);
        });
    });
}

/// Benchmark: Startup with pre-existing state file
fn bench_shell_startup_with_state(c: &mut Criterion) {
    c.bench_function("shell_startup_with_state", |b| {
        // Create state once, then benchmark re-opening
        let temp = TempDir::new().unwrap();
        let root = temp.path().to_str().unwrap();
        {
            let mut state = ShellState::new(root).unwrap();
            for i in 0..50 {
                mkdir(&mut state, &format!("dir_{}", i), false).unwrap();
            }
        }

        b.iter(|| {
            let state = ShellState::new(root).unwrap();
            black_box(&state);
        });
    });
}

// ============================================================
// 2. Command Parsing Throughput
// ============================================================

/// Benchmark: Simple command parsing
fn bench_parse_simple(c: &mut Criterion) {
    let mut group = c.benchmark_group("parse_throughput");
    group.throughput(Throughput::Elements(1));

    group.bench_function("simple_mkdir", |b| {
        b.iter(|| {
            let cmd = parse_command("mkdir test_dir").unwrap();
            black_box(cmd);
        });
    });

    group.bench_function("simple_echo", |b| {
        b.iter(|| {
            let cmd = parse_command("echo hello world").unwrap();
            black_box(cmd);
        });
    });

    group.bench_function("with_redirections", |b| {
        b.iter(|| {
            let cmd = parse_command("echo hello > output.txt 2>&1").unwrap();
            black_box(cmd);
        });
    });

    group.bench_function("variable_assignment", |b| {
        b.iter(|| {
            let cmd = parse_command("MY_VAR=hello_world").unwrap();
            black_box(cmd);
        });
    });

    group.bench_function("pipeline", |b| {
        b.iter(|| {
            let cmd = parse_command("ls | grep test | wc -l").unwrap();
            black_box(cmd);
        });
    });

    group.bench_function("logical_operators", |b| {
        b.iter(|| {
            let cmd = parse_command("test -f file && echo yes || echo no").unwrap();
            black_box(cmd);
        });
    });

    group.bench_function("function_definition", |b| {
        b.iter(|| {
            let cmd = parse_command("setup() { mkdir src; touch src/main.rs; }").unwrap();
            black_box(cmd);
        });
    });

    group.bench_function("control_structure_if", |b| {
        b.iter(|| {
            let cmd = parse_command("if [ -f test ]; then echo yes; else echo no; fi").unwrap();
            black_box(cmd);
        });
    });

    group.finish();
}

/// Benchmark: Batch command parsing (many commands in sequence)
fn bench_parse_batch(c: &mut Criterion) {
    let commands = vec![
        "mkdir project",
        "touch project/README.md",
        "echo hello > project/greeting.txt",
        "VAR=value",
        "export PATH",
        "ls | grep txt",
        "if [ -d project ]; then echo yes; fi",
        "cd project",
        "pwd",
        "cd ..",
    ];

    let mut group = c.benchmark_group("parse_batch");
    group.throughput(Throughput::Elements(commands.len() as u64));

    group.bench_function("10_commands", |b| {
        b.iter(|| {
            for cmd_str in &commands {
                let cmd = parse_command(cmd_str).unwrap();
                black_box(&cmd);
            }
        });
    });

    group.finish();
}

// ============================================================
// 3. Pipeline Execution Overhead
// ============================================================

/// Benchmark: Parsing pipeline commands of increasing length
fn bench_pipeline_parsing(c: &mut Criterion) {
    let mut group = c.benchmark_group("pipeline_parsing");

    for stages in [2, 3, 5, 10] {
        let pipeline: String = (0..stages)
            .map(|i| format!("cmd{}", i))
            .collect::<Vec<_>>()
            .join(" | ");

        group.bench_function(format!("{}_stages", stages), |b| {
            b.iter(|| {
                let cmd = parse_command(&pipeline).unwrap();
                black_box(cmd);
            });
        });
    }

    group.finish();
}

// ============================================================
// 4. State Checkpoint/Restore Cycle Time
// ============================================================

/// Benchmark: Creating a checkpoint
fn bench_checkpoint_create(c: &mut Criterion) {
    c.bench_function("checkpoint_create", |b| {
        let temp = TempDir::new().unwrap();
        let mut state = ShellState::new(temp.path().to_str().unwrap()).unwrap();

        // Pre-populate with some operations
        for i in 0..20 {
            mkdir(&mut state, &format!("dir_{}", i), false).unwrap();
        }

        let mut checkpoint_idx = 0;
        b.iter(|| {
            let name = format!("cp_{}", checkpoint_idx);
            state
                .checkpoints
                .insert(name, (state.history.len(), chrono::Utc::now()));
            checkpoint_idx += 1;
            black_box(&state.checkpoints);
        });
    });
}

/// Benchmark: Full checkpoint-modify-restore cycle
fn bench_checkpoint_restore_cycle(c: &mut Criterion) {
    c.bench_function("checkpoint_restore_cycle", |b| {
        b.iter(|| {
            let temp = TempDir::new().unwrap();
            let mut state = ShellState::new(temp.path().to_str().unwrap()).unwrap();

            // Create initial state
            for i in 0..5 {
                mkdir(&mut state, &format!("dir_{}", i), false).unwrap();
            }

            // Checkpoint
            let history_len = state.history.len();
            state
                .checkpoints
                .insert("before".to_string(), (history_len, chrono::Utc::now()));

            // Modify
            for i in 5..10 {
                mkdir(&mut state, &format!("dir_{}", i), false).unwrap();
            }

            // Restore (undo back to checkpoint)
            let ops_to_undo = state.history.len() - history_len;
            for _ in 0..ops_to_undo {
                if let Some(last) = state.history.last() {
                    if !last.undone {
                        let path = last.path.clone();
                        let _ = rmdir(&mut state, &path, false);
                    }
                }
            }

            black_box(&state);
        });
    });
}

// ============================================================
// Benchmark groups
// ============================================================

criterion_group!(
    benches,
    bench_shell_startup,
    bench_shell_startup_with_state,
    bench_parse_simple,
    bench_parse_batch,
    bench_pipeline_parsing,
    bench_checkpoint_create,
    bench_checkpoint_restore_cycle,
);
criterion_main!(benches);
