// SPDX-License-Identifier: PLMP-1.0-or-later
//! Fuzz Target: Path Operations
//!
//! Tests path handling for:
//! - Path traversal attacks
//! - Symlink attacks
//! - Unicode paths
//! - Invalid characters
//! - Extreme lengths

#![no_main]

use libfuzzer_sys::fuzz_target;
use tempfile::TempDir;
use vsh::commands::mkdir;
use vsh::state::ShellState;

fuzz_target!(|data: &[u8]| {
    // Convert to string
    if let Ok(path) = std::str::from_utf8(data) {
        // Limit length
        if path.len() > 500 {
            return;
        }

        // Skip empty paths
        if path.is_empty() {
            return;
        }

        // Create sandbox
        let temp = match TempDir::new() {
            Ok(t) => t,
            Err(_) => return,
        };

        let mut state = match ShellState::new(temp.path()) {
            Ok(s) => s,
            Err(_) => return,
        };

        // Try to create directory with fuzzed path
        // Should either succeed (safe path) or fail gracefully (invalid path)
        // Should NEVER:
        // - Escape sandbox
        // - Execute commands
        // - Cause panic
        let _ = mkdir(&mut state, path, true);

        // Verify sandbox integrity (no escape)
        if let Ok(canonical_root) = std::fs::canonicalize(temp.path()) {
            for entry in walkdir::WalkDir::new(temp.path()).into_iter().flatten() {
                if let Ok(canonical) = std::fs::canonicalize(entry.path()) {
                    assert!(
                        canonical.starts_with(&canonical_root),
                        "Path escaped sandbox: {:?}",
                        canonical
                    );
                }
            }
        }
    }
});
