// SPDX-License-Identifier: PMPL-1.0-or-later
//! Regression tests for multi-line script and sourced-file execution.
//!
//! The previous `execute_script_content` and `Command::Source` iterated
//! `content.lines()` and parsed each line in isolation. That broke every
//! control structure spanning multiple lines — the canonical POSIX shape:
//!
//! ```sh
//! if true
//! then
//!   mkdir d
//! fi
//! ```
//!
//! Fix: strip whole-line comments, then split the *entire* content on
//! `split_on_statement_separators` (top-level `;` and `\n`, respecting
//! quotes, parens, control-structure depth, and brace depth — so
//! `foo() { ...; }` stays on a single statement too).

use anyhow::Result;
use std::fs;
use tempfile::tempdir;
use vsh::executable::ExecutableCommand;
use vsh::parser::{parse_command, split_on_statement_separators};
use vsh::state::ShellState;

// -------------------------------------------------------------------------
// Statement splitter unit tests
// -------------------------------------------------------------------------

#[test]
fn statement_splitter_splits_on_newline() {
    let parts = split_on_statement_separators("echo a\necho b");
    let segs: Vec<&str> = parts.iter().map(|s| s.trim()).collect();
    assert_eq!(segs, vec!["echo a", "echo b"]);
}

#[test]
fn statement_splitter_keeps_multiline_if_together() {
    let parts =
        split_on_statement_separators("if true\nthen\n  mkdir d\nfi\necho after");
    let segs: Vec<&str> = parts.iter().map(|s| s.trim()).filter(|s| !s.is_empty()).collect();
    // The whole if/fi block is one segment, echo is a second.
    assert_eq!(segs.len(), 2);
    assert!(segs[0].starts_with("if") && segs[0].ends_with("fi"));
    assert_eq!(segs[1], "echo after");
}

#[test]
fn statement_splitter_keeps_function_def_together() {
    let parts = split_on_statement_separators("foo() { mkdir a; mkdir b; }\necho x");
    let segs: Vec<&str> = parts.iter().map(|s| s.trim()).filter(|s| !s.is_empty()).collect();
    assert_eq!(segs.len(), 2);
    assert_eq!(segs[0], "foo() { mkdir a; mkdir b; }");
    assert_eq!(segs[1], "echo x");
}

#[test]
fn statement_splitter_ignores_newlines_inside_quotes() {
    let parts = split_on_statement_separators("echo 'a\nb'\necho c");
    let segs: Vec<&str> = parts.iter().map(|s| s.trim()).filter(|s| !s.is_empty()).collect();
    assert_eq!(segs.len(), 2);
    assert_eq!(segs[0], "echo 'a\nb'");
    assert_eq!(segs[1], "echo c");
}

// -------------------------------------------------------------------------
// End-to-end: sourced scripts with multi-line control structures
// -------------------------------------------------------------------------

#[test]
fn sourced_script_executes_multiline_if_then_fi() -> Result<()> {
    let temp = tempdir()?;
    let mut state = ShellState::new(temp.path().to_str().unwrap())?;

    let script = temp.path().join("multi.sh");
    fs::write(&script, "if true\nthen\n  mkdir from_multi\nfi\n")?;

    parse_command(&format!("source {}", script.display()))?.execute(&mut state)?;

    assert!(state.resolve_path("from_multi").exists());
    Ok(())
}

#[test]
fn sourced_script_executes_multiline_for_loop() -> Result<()> {
    let temp = tempdir()?;
    let mut state = ShellState::new(temp.path().to_str().unwrap())?;

    let script = temp.path().join("loop.sh");
    fs::write(&script, "for x in a b c\ndo\n  mkdir $x\ndone\n")?;

    parse_command(&format!("source {}", script.display()))?.execute(&mut state)?;

    assert!(state.resolve_path("a").exists());
    assert!(state.resolve_path("b").exists());
    assert!(state.resolve_path("c").exists());
    Ok(())
}

#[test]
fn sourced_script_defines_and_invokes_multiline_function() -> Result<()> {
    let temp = tempdir()?;
    let mut state = ShellState::new(temp.path().to_str().unwrap())?;

    let script = temp.path().join("fns.sh");
    fs::write(
        &script,
        "greet() { mkdir hi; }\n# a comment\ngreet\n",
    )?;

    parse_command(&format!("source {}", script.display()))?.execute(&mut state)?;

    assert!(state.functions.is_defined("greet"));
    assert!(state.resolve_path("hi").exists());
    Ok(())
}

#[test]
fn sourced_script_skips_comment_only_lines() -> Result<()> {
    let temp = tempdir()?;
    let mut state = ShellState::new(temp.path().to_str().unwrap())?;

    let script = temp.path().join("commented.sh");
    fs::write(
        &script,
        "# leading comment\n\n# another\nmkdir real\n   # indented comment\nmkdir also\n",
    )?;

    parse_command(&format!("source {}", script.display()))?.execute(&mut state)?;

    assert!(state.resolve_path("real").exists());
    assert!(state.resolve_path("also").exists());
    Ok(())
}

#[test]
fn sourced_script_preserves_semicolon_inline() -> Result<()> {
    let temp = tempdir()?;
    let mut state = ShellState::new(temp.path().to_str().unwrap())?;

    // Mixed: a single-line if + a multi-line for in the same file.
    let script = temp.path().join("mixed.sh");
    fs::write(
        &script,
        "if true; then mkdir one; fi\nfor x in two three\ndo\n  mkdir $x\ndone\n",
    )?;

    parse_command(&format!("source {}", script.display()))?.execute(&mut state)?;

    assert!(state.resolve_path("one").exists());
    assert!(state.resolve_path("two").exists());
    assert!(state.resolve_path("three").exists());
    Ok(())
}
