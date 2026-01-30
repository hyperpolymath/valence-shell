// SPDX-License-Identifier: PLMP-1.0-or-later
//! Signal handling for the shell
//!
//! This module manages Unix signal handling, particularly:
//! - SIGINT (Ctrl+C) for interrupting foreground commands
//! - Signal state shared between modules

use std::sync::atomic::{AtomicBool, Ordering};

/// Flag indicating whether a SIGINT (Ctrl+C) was received
///
/// This is checked by command execution code to gracefully interrupt
/// running processes without terminating the shell itself.
pub static INTERRUPT_REQUESTED: AtomicBool = AtomicBool::new(false);

/// Check if an interrupt was requested
pub fn is_interrupt_requested() -> bool {
    INTERRUPT_REQUESTED.load(Ordering::Relaxed)
}

/// Clear the interrupt flag
pub fn clear_interrupt() {
    INTERRUPT_REQUESTED.store(false, Ordering::Relaxed);
}

/// Set the interrupt flag
pub fn request_interrupt() {
    INTERRUPT_REQUESTED.store(true, Ordering::Relaxed);
}
