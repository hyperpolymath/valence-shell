// SPDX-License-Identifier: MPL-2.0
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
pub mod enhanced_repl;
pub mod executable;
pub mod external;
pub mod friendly_errors;
pub mod functions;
pub mod glob;
pub mod help;
pub mod highlighter;
pub mod history;
pub mod job;
pub mod pager;
pub mod parser;
pub mod posix_builtins;
pub mod process_sub;
pub mod proof_refs;
pub mod quotes;
pub mod redirection;
pub mod repl;
pub mod secure_erase;
pub mod signals;
pub mod state;
pub mod test_command;

pub mod verification;

/// Echidna property-based verification integration (optional feature)
#[cfg(feature = "echidna")]
pub mod echidna_integration;

// Re-export commonly used types
pub use executable::ExecutableCommand;
pub use state::ShellState;

// Re-export signal handling
pub use signals::INTERRUPT_REQUESTED;
