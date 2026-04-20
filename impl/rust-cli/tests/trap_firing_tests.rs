// SPDX-License-Identifier: PMPL-1.0-or-later
//! Tests for trap handler execution.
//!
//! Verifies that:
//! - EXIT trap fires at shell exit
//! - INT trap fires when SIGINT is received
//! - Trap handlers can execute shell commands
//! - `trap -` resets signal handling

use anyhow::Result;
use tempfile::tempdir;
use vsh::executable::{self, ExecutableCommand};
use vsh::parser::parse_command;
use vsh::posix_builtins::TrapSignal;
use vsh::state::ShellState;

// -------------------------------------------------------------------------
// Trap registration
// -------------------------------------------------------------------------

#[test]
fn trap_set_and_retrieve() -> Result<()> {
    let temp = tempdir()?;
    let mut state = ShellState::new(temp.path().to_str().unwrap())?;

    parse_command("trap 'echo bye' EXIT")?.execute(&mut state)?;

    assert_eq!(state.traps.get(TrapSignal::Exit), Some("echo bye"));
    assert!(state.traps.is_trapped(TrapSignal::Exit));
    Ok(())
}

#[test]
fn trap_reset_with_dash() -> Result<()> {
    let temp = tempdir()?;
    let mut state = ShellState::new(temp.path().to_str().unwrap())?;

    parse_command("trap 'echo bye' EXIT")?.execute(&mut state)?;
    assert!(state.traps.is_trapped(TrapSignal::Exit));

    parse_command("trap - EXIT")?.execute(&mut state)?;
    assert!(!state.traps.is_trapped(TrapSignal::Exit));
    Ok(())
}

#[test]
fn trap_set_int_handler() -> Result<()> {
    let temp = tempdir()?;
    let mut state = ShellState::new(temp.path().to_str().unwrap())?;

    parse_command("trap 'echo caught' INT")?.execute(&mut state)?;

    assert_eq!(state.traps.get(TrapSignal::Int), Some("echo caught"));
    Ok(())
}

// -------------------------------------------------------------------------
// INT trap firing via run_pending_traps
// -------------------------------------------------------------------------

#[test]
fn run_pending_traps_fires_int_handler() -> Result<()> {
    let temp = tempdir()?;
    let mut state = ShellState::new(temp.path().to_str().unwrap())?;

    // Set an INT trap that creates a directory
    parse_command("trap 'mkdir trap_fired' INT")?.execute(&mut state)?;

    // Simulate SIGINT
    vsh::signals::request_interrupt();

    // Fire pending traps
    let should_exit = executable::run_pending_traps(&mut state);
    assert!(!should_exit);

    // The trap handler should have executed
    assert!(state.resolve_path("trap_fired").exists());
    Ok(())
}

#[test]
fn run_pending_traps_no_handler_clears_flag() -> Result<()> {
    let temp = tempdir()?;
    let mut state = ShellState::new(temp.path().to_str().unwrap())?;

    // No trap set — simulate SIGINT
    vsh::signals::request_interrupt();
    assert!(vsh::signals::is_interrupt_requested());

    // run_pending_traps should clear the flag even with no handler
    executable::run_pending_traps(&mut state);
    assert!(!vsh::signals::is_interrupt_requested());
    Ok(())
}

#[test]
fn run_pending_traps_no_signal_is_noop() -> Result<()> {
    let temp = tempdir()?;
    let mut state = ShellState::new(temp.path().to_str().unwrap())?;

    parse_command("trap 'mkdir should_not_exist' INT")?.execute(&mut state)?;

    // No SIGINT simulated
    vsh::signals::clear_interrupt();
    executable::run_pending_traps(&mut state);

    assert!(!state.resolve_path("should_not_exist").exists());
    Ok(())
}

// -------------------------------------------------------------------------
// EXIT trap firing
// -------------------------------------------------------------------------

#[test]
fn exit_trap_is_registered_for_later_firing() -> Result<()> {
    let temp = tempdir()?;
    let mut state = ShellState::new(temp.path().to_str().unwrap())?;

    parse_command("trap 'mkdir exit_cleanup' EXIT")?.execute(&mut state)?;

    // The trap is registered but not yet fired
    assert!(!state.resolve_path("exit_cleanup").exists());
    assert!(state.traps.is_trapped(TrapSignal::Exit));

    // Manually fire the EXIT trap (simulating shell exit)
    if let Some(handler) = state.traps.get(TrapSignal::Exit).map(|s| s.to_string()) {
        parse_command(&handler)?.execute(&mut state)?;
    }

    assert!(state.resolve_path("exit_cleanup").exists());
    Ok(())
}
