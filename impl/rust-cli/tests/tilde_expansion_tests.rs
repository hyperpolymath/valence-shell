// SPDX-License-Identifier: MPL-2.0
// Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//! Tests for POSIX §2.6.1 tilde expansion.
//!
//! Tilde expansion was previously hard-coded only inside the `cd` command.
//! It now runs globally via `expand_variables`, so `mkdir ~/foo`,
//! `echo ~`, `touch ~/bar`, etc. all work.

mod fixtures;

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

/// `~+` is the shell's working directory. It used to be the process's `PWD`,
/// which `cd` does not change.
#[test]
fn tilde_plus_expands_to_the_working_directory() {
    let temp = tempdir().unwrap();
    let _directory = fixtures::hold_process_directory();
    let mut state = ShellState::new(temp.path().to_str().unwrap()).unwrap();
    let root = state.root.clone();

    assert_eq!(expand_variables("~+", &state), root.to_string_lossy());

    std::fs::create_dir(root.join("sub")).unwrap();
    parse_command("cd sub")
        .unwrap()
        .execute(&mut state)
        .unwrap();
    let sub = root.join("sub");
    assert_eq!(expand_variables("~+", &state), sub.to_string_lossy());
    assert_eq!(
        expand_variables("~+/file", &state),
        format!("{}/file", sub.display())
    );
}

/// `~-` is the directory the shell was in before its last `cd`. It used to
/// be the process's `OLDPWD`, which `cd` does not change, so `cd ~-` went
/// wherever the shell's parent had last been.
#[test]
fn tilde_minus_expands_to_the_previous_directory() {
    let temp = tempdir().unwrap();
    let _directory = fixtures::hold_process_directory();
    let mut state = ShellState::new(temp.path().to_str().unwrap()).unwrap();
    let root = state.root.clone();

    // Before the first `cd` the shell has no previous directory of its own,
    // and falls back to the `OLDPWD` it was started with, if there is one.
    let inherited = std::env::var("OLDPWD").unwrap_or_else(|_| "~-".to_string());
    assert_eq!(expand_variables("~-", &state), inherited);

    std::fs::create_dir(root.join("sub")).unwrap();
    parse_command("cd sub")
        .unwrap()
        .execute(&mut state)
        .unwrap();
    assert_eq!(expand_variables("~-", &state), root.to_string_lossy());
    assert_eq!(
        expand_variables("~-/file", &state),
        format!("{}/file", root.display())
    );
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
    let _directory = fixtures::hold_process_directory();
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

/// The directory a tilde stands for is used as it is. It used to be read
/// for variables with the rest of the word, so in a working directory
/// named `cash$NAME`, `~+` named `cashvalue`.
#[test]
fn a_directory_named_like_a_variable_is_not_expanded() {
    let temp = tempdir().unwrap();
    let mut state = ShellState::new(temp.path().to_str().unwrap()).unwrap();
    let here = state.root.join("cash$NAME");
    std::fs::create_dir(&here).unwrap();
    state.set_variable("NAME", "value");
    state.set_cwd(&here).unwrap();
    state.previous_dir = Some(here.clone());

    for tilde in ["~+", "~-"] {
        assert_eq!(expand_variables(tilde, &state), here.to_string_lossy());
        // What follows the directory is still read for variables.
        assert_eq!(
            expand_variables(&format!("{tilde}/$NAME"), &state),
            format!("{}/value", here.display())
        );
    }
}
