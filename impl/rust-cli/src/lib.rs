// SPDX-License-Identifier: PLMP-1.0-or-later
//! Library interface for Valence Shell
//!
//! This module exposes internal components for:
//! - Testing (unit and integration tests)
//! - Fuzzing (cargo-fuzz targets)
//! - Benchmarking (criterion benchmarks)
//!
//! The main binary (main.rs) provides the CLI interface.

pub mod arith;
pub mod commands;
pub mod confirmation;
pub mod daemon_client;
pub mod executable;
pub mod external;
pub mod glob;
pub mod history;
pub mod quotes;
pub mod job;
pub mod parser;
pub mod process_sub;
pub mod proof_refs;
pub mod redirection;
pub mod secure_erase;
pub mod signals;
pub mod state;

// Optional Lean 4 runtime verification
#[cfg(feature = "lean-runtime-checks")]
pub mod lean_ffi;

pub mod verification;

// Re-export commonly used types
pub use state::ShellState;
pub use executable::ExecutableCommand;

// Re-export signal handling
pub use signals::INTERRUPT_REQUESTED;
