// SPDX-License-Identifier: MPL-2.0
// Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//! Tests for POSIX §2.6.1 tilde expansion.
//!
//! Tilde expansion was previously hard-coded only inside the `cd` command.
//! It now runs globally via `expand_variables`, so `mkdir ~/foo`,
//! `echo ~`, `touch ~/bar`, etc. all work.

use anyhow::Result;
use tempfile::tempdir;
use vsh::executable::ExecutableCommand;
use vsh::parser::{expand_variables, parse_command};
use vsh::state::ShellState;

// -------------------------------------------------------------------------
// Unit tests for expand_tilde (via expand_variables)
// -------------------------------------------------------------------------

#[test]
fn tilde_alone_expands_to_home() {
    let temp = tempdir().unwrap();
    let state = ShellState::new(temp.path().to_str().unwrap()).unwrap();

    let home = std::env::var("HOME").unwrap_or_default();
    assert_eq!(expand_variables("~", &state), home);
}

#[test]
fn tilde_slash_path_expands_to_home_slash_path() {
    let temp = tempdir().unwrap();
    let state = ShellState::new(temp.path().to_str().unwrap()).unwrap();

    let home = std::env::var("HOME").unwrap_or_default();
    assert_eq!(
        expand_variables("~/Documents/foo", &state),
        format!("{}/Documents/foo", home)
    );
}

#[test]
fn tilde_plus_expands_to_pwd() {
    let temp = tempdir().unwrap();
    let state = ShellState::new(temp.path().to_str().unwrap()).unwrap();

    std::env::set_var("PWD", "/some/where");
    assert_eq!(expand_variables("~+", &state), "/some/where");
    assert_eq!(expand_variables("~+/subdir", &state), "/some/where/subdir");
}

#[test]
fn tilde_minus_expands_to_oldpwd() {
    let temp = tempdir().unwrap();
    let state = ShellState::new(temp.path().to_str().unwrap()).unwrap();

    std::env::set_var("OLDPWD", "/old/dir");
    assert_eq!(expand_variables("~-", &state), "/old/dir");
    assert_eq!(expand_variables("~-/file", &state), "/old/dir/file");
}

#[test]
fn tilde_not_at_start_stays_literal() {
    let temp = tempdir().unwrap();
    let state = ShellState::new(temp.path().to_str().unwrap()).unwrap();

    assert_eq!(expand_variables("foo~bar", &state), "foo~bar");
}

#[test]
fn escaped_tilde_stays_literal() {
    let temp = tempdir().unwrap();
    let state = ShellState::new(temp.path().to_str().unwrap()).unwrap();

    // `\~` is what quoted_word_to_string produces for '~' or "~"
    assert_eq!(expand_variables("\\~", &state), "~");
    assert_eq!(expand_variables("\\~/foo", &state), "~/foo");
}

#[test]
fn unknown_tilde_user_stays_literal() {
    let temp = tempdir().unwrap();
    let state = ShellState::new(temp.path().to_str().unwrap()).unwrap();

    assert_eq!(
        expand_variables("~nonexistent_user_xyz", &state),
        "~nonexistent_user_xyz"
    );
}

// -------------------------------------------------------------------------
// Integration: tilde expansion works in real commands (not just cd)
// -------------------------------------------------------------------------

#[test]
fn tilde_expands_in_variable_assignments() -> Result<()> {
    let temp = tempdir()?;
    let state = ShellState::new(temp.path().to_str().unwrap())?;

    let home = std::env::var("HOME").unwrap_or_default();

    // Verify tilde expansion works inside commands that use expand_variables
    let expanded = expand_variables("~/.config/vsh", &state);
    assert_eq!(expanded, format!("{}/.config/vsh", home));

    Ok(())
}

/// `cd ~` still expands the tilde, but the shell is confined to its session
/// root (route plan OD-26, option a), so a home directory outside the root
/// is refused and the working directory does not move.
///
/// Until 2026-11-17 this test asserted the opposite: that `cd ~` moved the
/// sandbox root itself to the home directory. That was runtime hole g.
#[test]
fn cd_with_tilde_is_confined_to_the_session_root() -> Result<()> {
    let temp = tempdir()?;
    let mut state = ShellState::new(temp.path().to_str().unwrap())?;
    let root = state.root.clone();

    let home = std::env::var("HOME").unwrap_or_default();
    let home_is_outside = !std::fs::canonicalize(&home)
        .map(|real| real.starts_with(&root))
        .unwrap_or(false);
    assert!(
        home_is_outside,
        "this test needs HOME outside the session root"
    );

    let refused = parse_command("cd ~")?.execute(&mut state);
    assert!(
        refused.is_err(),
        "cd to a home outside the root must be refused"
    );
    assert_eq!(state.root, root, "the session root never moves");
    assert_eq!(state.cwd(), root, "the working directory did not move");

    // A tilde path that lands inside the root is fine: `~-` is the previous
    // directory.
    std::fs::create_dir(root.join("sub"))?;
    parse_command("cd sub")?.execute(&mut state)?;
    assert_eq!(state.cwd(), root.join("sub"));
    parse_command("cd ~-")?.execute(&mut state)?;
    assert_eq!(state.cwd(), root);
    assert_eq!(state.root, root);
    Ok(())
}
