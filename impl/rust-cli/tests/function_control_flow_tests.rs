// SPDX-License-Identifier: PMPL-1.0-or-later
//! Regression tests for shell function control-flow semantics.
//!
//! Two bugs motivated this file:
//!
//! 1. **Control structures inside function bodies were fragmented.**
//!    The body of `f() { if x; then y; fi; }` was split into
//!    `["if x", "then y", "fi"]` by a naive `;`-split, so each piece
//!    failed to parse individually. The fix stores the raw body and
//!    uses a control-structure-aware split at call time.
//!
//! 2. **`return` inside nested control structures did nothing.**
//!    The function executor detected returns with `cmd_str.starts_with("return")`,
//!    which never matched when `return` was buried inside `if/fi`, `for/done`,
//!    or `while/done`. The fix introduces `ExecutionResult::Return` that
//!    propagates through every control-structure handler up to the
//!    function call boundary.

use anyhow::Result;
use tempfile::tempdir;
use vsh::executable::ExecutableCommand;
use vsh::parser::parse_command;
use vsh::state::ShellState;

// -------------------------------------------------------------------------
// Control structures inside function bodies
// -------------------------------------------------------------------------

#[test]
fn function_body_contains_if_then_fi() -> Result<()> {
    let temp = tempdir()?;
    let mut state = ShellState::new(temp.path().to_str().unwrap())?;

    parse_command("ifunc() { if true; then mkdir from_if; fi; }")?.execute(&mut state)?;
    parse_command("ifunc")?.execute(&mut state)?;

    assert!(state.resolve_path("from_if").exists());
    Ok(())
}

#[test]
fn function_body_contains_for_loop() -> Result<()> {
    let temp = tempdir()?;
    let mut state = ShellState::new(temp.path().to_str().unwrap())?;

    parse_command("ffunc() { for d in a b c; do mkdir $d; done; }")?
        .execute(&mut state)?;
    parse_command("ffunc")?.execute(&mut state)?;

    assert!(state.resolve_path("a").exists());
    assert!(state.resolve_path("b").exists());
    assert!(state.resolve_path("c").exists());
    Ok(())
}

#[test]
fn function_body_contains_case_statement() -> Result<()> {
    let temp = tempdir()?;
    let mut state = ShellState::new(temp.path().to_str().unwrap())?;

    parse_command(
        "cfunc() { case $1 in a) mkdir chose_a ;; b) mkdir chose_b ;; esac; }",
    )?
    .execute(&mut state)?;

    parse_command("cfunc b")?.execute(&mut state)?;

    assert!(!state.resolve_path("chose_a").exists());
    assert!(state.resolve_path("chose_b").exists());
    Ok(())
}

// -------------------------------------------------------------------------
// `return` inside nested control structures
// -------------------------------------------------------------------------

#[test]
fn return_from_inside_if_sets_exit_code() -> Result<()> {
    let temp = tempdir()?;
    let mut state = ShellState::new(temp.path().to_str().unwrap())?;

    parse_command("rf() { if true; then return 7; fi; mkdir after; }")?
        .execute(&mut state)?;
    parse_command("rf")?.execute(&mut state)?;

    assert_eq!(state.last_exit_code, 7);
    assert!(
        !state.resolve_path("after").exists(),
        "commands after `return` inside `if` should not execute"
    );
    Ok(())
}

#[test]
fn return_from_inside_for_loop_breaks_out_of_function() -> Result<()> {
    let temp = tempdir()?;
    let mut state = ShellState::new(temp.path().to_str().unwrap())?;

    // Should make exactly one directory (the loop returns on the first iteration).
    parse_command("rf() { for x in one two three; do mkdir $x; return 3; done; }")?
        .execute(&mut state)?;
    parse_command("rf")?.execute(&mut state)?;

    assert_eq!(state.last_exit_code, 3);
    assert!(state.resolve_path("one").exists());
    assert!(!state.resolve_path("two").exists());
    assert!(!state.resolve_path("three").exists());
    Ok(())
}

#[test]
fn return_from_inside_nested_if_in_for_breaks_out_of_function() -> Result<()> {
    let temp = tempdir()?;
    let mut state = ShellState::new(temp.path().to_str().unwrap())?;

    // Nested `for ... do if ... then return ...; fi ... done` — the
    // sentinel must propagate up through BOTH layers.
    parse_command(
        "rf() { for x in one two; do if true; then mkdir found; return 9; fi; done; mkdir never; }",
    )?
    .execute(&mut state)?;

    parse_command("rf")?.execute(&mut state)?;

    assert_eq!(state.last_exit_code, 9);
    assert!(state.resolve_path("found").exists());
    assert!(!state.resolve_path("never").exists());
    Ok(())
}

#[test]
fn return_with_no_code_inherits_last_exit_code() -> Result<()> {
    let temp = tempdir()?;
    let mut state = ShellState::new(temp.path().to_str().unwrap())?;

    // `false` sets $? to 1; then `return` with no arg should inherit that.
    parse_command("rf() { false; return; }")?.execute(&mut state)?;
    parse_command("rf")?.execute(&mut state)?;

    assert_eq!(state.last_exit_code, 1);
    Ok(())
}

// -------------------------------------------------------------------------
// Raw body preserves tricky content
// -------------------------------------------------------------------------

#[test]
fn function_body_with_brace_in_quoted_string_parses() -> Result<()> {
    let temp = tempdir()?;
    let mut state = ShellState::new(temp.path().to_str().unwrap())?;

    // A `}` inside single quotes must not be mistaken for the closing brace
    // of the function body. If it were, this would fail to register as a
    // function definition.
    parse_command("lit() { echo '}' ; mkdir ran; }")?.execute(&mut state)?;
    assert!(state.functions.is_defined("lit"));

    parse_command("lit")?.execute(&mut state)?;
    assert!(state.resolve_path("ran").exists());
    Ok(())
}
