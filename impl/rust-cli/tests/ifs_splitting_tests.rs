// SPDX-License-Identifier: PMPL-1.0-or-later
//! Tests for IFS word splitting in for-loops and related contexts.
//!
//! POSIX §2.6.5 says that after parameter expansion, the result of
//! unquoted expansions is split into fields using `$IFS`.  This affects
//! the `for ... in $words` word list (each expanded word is split) and
//! the `read` builtin (input is split across named variables).

use anyhow::Result;
use tempfile::tempdir;
use vsh::executable::ExecutableCommand;
use vsh::parser::parse_command;
use vsh::state::ShellState;

// -------------------------------------------------------------------------
// IFS splitting in for-loops
// -------------------------------------------------------------------------

#[test]
fn for_loop_splits_variable_by_default_ifs() -> Result<()> {
    let temp = tempdir()?;
    let mut state = ShellState::new(temp.path().to_str().unwrap())?;

    state.set_variable("ITEMS", "alpha beta gamma");

    parse_command("for x in $ITEMS; do mkdir $x; done")?
        .execute(&mut state)?;

    assert!(state.resolve_path("alpha").exists());
    assert!(state.resolve_path("beta").exists());
    assert!(state.resolve_path("gamma").exists());
    Ok(())
}

#[test]
fn for_loop_splits_variable_by_custom_ifs() -> Result<()> {
    let temp = tempdir()?;
    let mut state = ShellState::new(temp.path().to_str().unwrap())?;

    state.set_variable("CSV", "one,two,three");
    state.set_variable("IFS", ",");

    parse_command("for x in $CSV; do mkdir $x; done")?
        .execute(&mut state)?;

    assert!(state.resolve_path("one").exists());
    assert!(state.resolve_path("two").exists());
    assert!(state.resolve_path("three").exists());
    Ok(())
}

#[test]
fn for_loop_with_empty_ifs_does_not_split() -> Result<()> {
    let temp = tempdir()?;
    let mut state = ShellState::new(temp.path().to_str().unwrap())?;

    state.set_variable("WORDS", "hello world");
    state.set_variable("IFS", "");

    // With empty IFS, the entire value is one word.
    // The for-loop body runs once and creates one dir whose name
    // contains a space.
    parse_command("for x in $WORDS; do mkdir $x; done")?
        .execute(&mut state)?;

    // "hello world" stays as one token — but mkdir may receive it as
    // two words due to the shell's argument tokenization. The key test
    // is that IFS="" prevents the for-loop from splitting the expansion
    // into two iterations.
    //
    // Verify we did NOT get separate "hello" and "world" directories.
    assert!(!state.resolve_path("hello").exists());
    assert!(!state.resolve_path("world").exists());
    Ok(())
}

#[test]
fn for_loop_splits_newlines_in_variable() -> Result<()> {
    let temp = tempdir()?;
    let mut state = ShellState::new(temp.path().to_str().unwrap())?;

    // Newline is part of default IFS
    state.set_variable("LINES", "line1\nline2\nline3");

    parse_command("for x in $LINES; do mkdir $x; done")?
        .execute(&mut state)?;

    assert!(state.resolve_path("line1").exists());
    assert!(state.resolve_path("line2").exists());
    assert!(state.resolve_path("line3").exists());
    Ok(())
}

#[test]
fn for_loop_literal_words_not_affected_by_ifs() -> Result<()> {
    let temp = tempdir()?;
    let mut state = ShellState::new(temp.path().to_str().unwrap())?;

    // Literal words in the for-list are already split by the parser
    // at whitespace boundaries. IFS affects EXPANSION splitting, not
    // literal splitting.
    parse_command("for x in one two three; do mkdir $x; done")?
        .execute(&mut state)?;

    assert!(state.resolve_path("one").exists());
    assert!(state.resolve_path("two").exists());
    assert!(state.resolve_path("three").exists());
    Ok(())
}

// -------------------------------------------------------------------------
// read builtin: IFS splitting + multiple variables
// -------------------------------------------------------------------------

// Note: The `read` builtin reads from stdin, which we can't easily mock in
// integration tests. We test the parser changes and IFS logic indirectly
// through the unit tests in posix_builtins.rs and by verifying the Command
// variant is parsed correctly.

#[test]
fn read_parses_multiple_variables() -> Result<()> {
    let cmd = parse_command("read a b c")?;
    let desc = format!("{:?}", cmd);
    // Should have three variable names
    assert!(desc.contains("var_names"));
    assert!(desc.contains("\"a\""));
    assert!(desc.contains("\"b\""));
    assert!(desc.contains("\"c\""));
    Ok(())
}

#[test]
fn read_defaults_to_reply() -> Result<()> {
    let cmd = parse_command("read")?;
    let desc = format!("{:?}", cmd);
    assert!(desc.contains("REPLY"));
    Ok(())
}

#[test]
fn read_with_prompt_and_vars() -> Result<()> {
    let cmd = parse_command("read -p 'Enter: ' first last")?;
    let desc = format!("{:?}", cmd);
    assert!(desc.contains("\"first\""));
    assert!(desc.contains("\"last\""));
    assert!(desc.contains("Enter:"));
    Ok(())
}
