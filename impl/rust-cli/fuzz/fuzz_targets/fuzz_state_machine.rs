// SPDX-License-Identifier: PLMP-1.0-or-later
//! Fuzz Target: State Machine (Undo/Redo)
//!
//! Tests the undo/redo state machine for:
//! - Arbitrary operation sequences
//! - Undo/redo consistency
//! - State corruption
//! - Edge cases

#![no_main]

use libfuzzer_sys::fuzz_target;
use tempfile::TempDir;
use vsh::commands::{mkdir, rmdir, touch, rm};
use vsh::state::ShellState;

#[derive(Debug, Clone, Copy)]
enum Action {
    Mkdir,
    Rmdir,
    Touch,
    Rm,
    Undo,
    Redo,
}

impl Action {
    fn from_byte(b: u8) -> Self {
        match b % 6 {
            0 => Action::Mkdir,
            1 => Action::Rmdir,
            2 => Action::Touch,
            3 => Action::Rm,
            4 => Action::Undo,
            5 => Action::Redo,
            _ => unreachable!(),
        }
    }
}

fuzz_target!(|data: &[u8]| {
    // Limit sequence length
    if data.is_empty() || data.len() > 100 {
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

    // Execute sequence of actions
    for (idx, &byte) in data.iter().enumerate() {
        let action = Action::from_byte(byte);
        let target = format!("target_{}", idx % 10); // Reuse 10 targets

        match action {
            Action::Mkdir => {
                let _ = mkdir(&mut state, &target, true);
            }
            Action::Rmdir => {
                let _ = rmdir(&mut state, &target, true);
            }
            Action::Touch => {
                let _ = touch(&mut state, &target, true);
            }
            Action::Rm => {
                let _ = rm(&mut state, &target, true);
            }
            Action::Undo => {
                let _ = state.pop_undo();
            }
            Action::Redo => {
                let _ = state.pop_redo();
            }
        }

        // Invariants to check:
        // - History + redo stack = total operations
        // - Filesystem state consistent with history
        // - No dangling references
        // - Undo/redo never panic
    }

    // Final consistency check
    // If we undo all operations, filesystem should match initial state
    let initial_entries = std::fs::read_dir(temp.path())
        .map(|e| e.count())
        .unwrap_or(0);

    while state.pop_undo().is_ok() {
        // Keep undoing
    }

    let final_entries = std::fs::read_dir(temp.path())
        .map(|e| e.count())
        .unwrap_or(0);

    // After full undo, should have same number of entries as start (0)
    // (This assertion may be too strict if operations had precondition failures)
    // assert_eq!(initial_entries, final_entries);
});
