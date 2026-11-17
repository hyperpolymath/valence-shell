// SPDX-License-Identifier: MPL-2.0
//! The working directory and the session root are two things.
//!
//! The session root is fixed when the shell starts. `cd` moves only the
//! working directory, and only within the session root. Paths in the history
//! are relative to the session root, so `undo` means the same thing wherever
//! the working directory is by then.

#![cfg(unix)]

mod fixtures;

use fixtures::tempfile::TempDir;
use std::fs;
use std::os::unix::fs::symlink;
use std::path::PathBuf;
use vsh::parser::parse_command;
use vsh::state::ShellState;
use vsh::ExecutableCommand;

struct Sandbox {
    _temp: TempDir,
    root: PathBuf,
    outside: PathBuf,
}

fn sandbox() -> (Sandbox, ShellState) {
    let temp = TempDir::new().unwrap();
    let root = temp.path().join("root");
    let outside = temp.path().join("outside");
    fs::create_dir(&root).unwrap();
    fs::create_dir(&outside).unwrap();
    let root = fs::canonicalize(root).unwrap();
    let outside = fs::canonicalize(outside).unwrap();
    let state = ShellState::new(root.to_str().unwrap()).unwrap();
    (
        Sandbox {
            _temp: temp,
            root,
            outside,
        },
        state,
    )
}

fn run(state: &mut ShellState, command: &str) -> anyhow::Result<()> {
    parse_command(command)?.execute(state).map(|_| ())
}

#[test]
fn cd_moves_the_working_directory_and_never_the_root() {
    let (sandbox, mut state) = sandbox();
    fs::create_dir_all(sandbox.root.join("a/b")).unwrap();

    run(&mut state, "cd a").unwrap();
    assert_eq!(state.cwd(), sandbox.root.join("a"));
    run(&mut state, "cd b").unwrap();
    assert_eq!(state.cwd(), sandbox.root.join("a/b"));
    run(&mut state, "cd ..").unwrap();
    assert_eq!(state.cwd(), sandbox.root.join("a"));
    run(&mut state, "cd -").unwrap();
    assert_eq!(state.cwd(), sandbox.root.join("a/b"));
    run(&mut state, "cd").unwrap();
    assert_eq!(
        state.cwd(),
        sandbox.root,
        "plain `cd` returns to the session root"
    );
    assert_eq!(state.root, sandbox.root);
}

#[test]
fn cd_cannot_go_above_the_root() {
    let (sandbox, mut state) = sandbox();
    fs::create_dir(sandbox.root.join("a")).unwrap();

    // `..` at the root stays at the root, as it does at `/`.
    run(&mut state, "cd ..").unwrap();
    assert_eq!(state.cwd(), sandbox.root);
    run(&mut state, "cd a").unwrap();
    run(&mut state, "cd ../../..").unwrap();
    assert_eq!(state.cwd(), sandbox.root);

    // An absolute path outside the root is refused.
    let outside = sandbox.outside.to_str().unwrap().to_string();
    assert!(run(&mut state, &format!("cd {outside}")).is_err());
    assert_eq!(state.cwd(), sandbox.root);
}

#[test]
fn cd_does_not_follow_a_symlink_out_of_the_root() {
    let (sandbox, mut state) = sandbox();
    symlink(&sandbox.outside, sandbox.root.join("out")).unwrap();
    fs::create_dir(sandbox.root.join("real")).unwrap();
    symlink("real", sandbox.root.join("in")).unwrap();

    let refused = run(&mut state, "cd out").unwrap_err();
    assert!(
        refused.to_string().contains("outside the session root"),
        "{refused}"
    );
    assert_eq!(state.cwd(), sandbox.root);

    // A link that stays inside the root is followed.
    run(&mut state, "cd in").unwrap();
    assert_eq!(state.cwd(), sandbox.root.join("real"));
}

#[test]
fn cd_accepts_a_real_absolute_path_inside_the_root_and_a_root_relative_one() {
    let (sandbox, mut state) = sandbox();
    fs::create_dir_all(sandbox.root.join("a/b")).unwrap();

    let real = sandbox.root.join("a/b");
    run(&mut state, &format!("cd {}", real.display())).unwrap();
    assert_eq!(state.cwd(), real);

    // `/a` is read from the session root, as `touch /a/x` would be.
    run(&mut state, "cd /a").unwrap();
    assert_eq!(state.cwd(), sandbox.root.join("a"));
}

#[test]
fn paths_are_relative_to_the_working_directory() {
    let (sandbox, mut state) = sandbox();
    fs::create_dir(sandbox.root.join("sub")).unwrap();

    run(&mut state, "cd sub").unwrap();
    run(&mut state, "touch f").unwrap();
    run(&mut state, "mkdir d").unwrap();
    run(&mut state, "touch ../top").unwrap();
    assert!(sandbox.root.join("sub/f").is_file());
    assert!(sandbox.root.join("sub/d").is_dir());
    assert!(sandbox.root.join("top").is_file());

    // The history holds paths from the session root.
    let recorded: Vec<&str> = state.history.iter().map(|op| op.path.as_str()).collect();
    assert_eq!(recorded, ["sub/f", "sub/d", "top"]);
}

#[test]
fn undo_after_cd_reverses_the_operation_that_was_made() {
    let (sandbox, mut state) = sandbox();
    fs::create_dir(sandbox.root.join("sub")).unwrap();
    fs::write(sandbox.root.join("sub/f"), "KEEP").unwrap();

    // Made at the root, undone from `sub`, where another `f` lives.
    run(&mut state, "touch f").unwrap();
    run(&mut state, "cd sub").unwrap();
    run(&mut state, "undo").unwrap();
    assert!(!sandbox.root.join("f").exists());
    assert_eq!(fs::read(sandbox.root.join("sub/f")).unwrap(), b"KEEP");

    // Made in `sub`, undone from the root.
    run(&mut state, "touch g").unwrap();
    run(&mut state, "mv g h").unwrap();
    run(&mut state, "cd ..").unwrap();
    run(&mut state, "undo").unwrap();
    assert!(sandbox.root.join("sub/g").exists());
    assert!(!sandbox.root.join("sub/h").exists());
    run(&mut state, "undo").unwrap();
    assert!(!sandbox.root.join("sub/g").exists());

    // And redo, from yet another directory.
    fs::create_dir(sandbox.root.join("other")).unwrap();
    run(&mut state, "cd other").unwrap();
    run(&mut state, "redo").unwrap();
    assert!(sandbox.root.join("sub/g").exists());
}

#[test]
fn rollback_after_cd_reverses_the_operations_that_were_made() {
    let (sandbox, mut state) = sandbox();
    fs::create_dir(sandbox.root.join("sub")).unwrap();

    run(&mut state, "begin t").unwrap();
    run(&mut state, "touch a").unwrap();
    run(&mut state, "cd sub").unwrap();
    run(&mut state, "touch b").unwrap();
    run(&mut state, "rollback").unwrap();
    assert!(!sandbox.root.join("a").exists());
    assert!(!sandbox.root.join("sub/b").exists());
}
