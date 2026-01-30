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
pub mod audit_log;
pub mod commands;
pub mod confirmation;
pub mod correction;
pub mod daemon_client;
pub mod enhanced_repl;
pub mod executable;
pub mod external;
pub mod friendly_errors;
pub mod glob;
pub mod help;
pub mod highlighter;
pub mod history;
pub mod quotes;
pub mod job;
pub mod pager;
pub mod parser;
pub mod process_sub;
pub mod proof_refs;
pub mod redirection;
pub mod repl;
pub mod secure_erase;
pub mod signals;
pub mod state;
pub mod test_command;

// Optional Lean 4 runtime verification
#[cfg(feature = "lean-runtime-checks")]
pub mod lean_ffi;

pub mod verification;

// Re-export commonly used types
pub use state::ShellState;
pub use executable::ExecutableCommand;

// Re-export signal handling
pub use signals::INTERRUPT_REQUESTED;
