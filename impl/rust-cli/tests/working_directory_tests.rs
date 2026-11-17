// SPDX-License-Identifier: MPL-2.0
//! The working directory and the session root are two things.
//!
//! The session root is fixed when the shell starts. `cd` moves only the
//! working directory, and only within the session root. Paths in the history
//! are relative to the session root, so `undo` means the same thing wherever
//! the working directory is by then.

#![cfg(unix)]

mod fixtures;

use fixtures::sandbox;
use std::fs;
use std::os::unix::fs::symlink;
use vsh::parser::parse_command;
use vsh::state::ShellState;
use vsh::ExecutableCommand;

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

/// Runs the built shell on `script` with `root` as the session root. A
/// redirection changes where the process writes, so these cases need a
/// process of their own.
fn shell(root: &std::path::Path, script: &str) -> std::process::Output {
    std::process::Command::new(env!("CARGO_BIN_EXE_vsh"))
        .arg("-r")
        .arg(root)
        .arg("-c")
        .arg(script)
        .current_dir(root)
        .env("NO_COLOR", "1")
        .env_remove("RUST_BACKTRACE")
        .stdin(std::process::Stdio::null())
        .output()
        .expect("start the built shell")
}

/// A redirection made below the session root is recorded under the path of
/// the file it wrote. It used to be recorded with the working directory
/// added a second time (`sub/sub/f`), so undo failed or changed another
/// file.
#[test]
fn a_redirection_below_the_root_is_recorded_under_its_own_path() {
    let (sandbox, _state) = sandbox();
    fs::create_dir(sandbox.root.join("sub")).unwrap();
    let file = sandbox.root.join("sub/f");

    let run = shell(&sandbox.root, "cd sub; echo one > f; echo two > f");
    assert!(
        run.status.success(),
        "{}",
        String::from_utf8_lossy(&run.stderr)
    );
    assert_eq!(fs::read_to_string(&file).unwrap(), "two\n");
    let saved = fs::read_to_string(sandbox.root.join(".vsh_state.json")).unwrap();
    assert!(saved.contains("\"sub/f\""), "{saved}");
    assert!(!saved.contains("sub/sub"), "{saved}");

    // Undo works from anywhere: here from the root, in a new shell.
    let run = shell(&sandbox.root, "undo");
    assert!(
        run.status.success(),
        "{}",
        String::from_utf8_lossy(&run.stderr)
    );
    assert_eq!(fs::read_to_string(&file).unwrap(), "one\n");
    let run = shell(&sandbox.root, "undo");
    assert!(
        run.status.success(),
        "{}",
        String::from_utf8_lossy(&run.stderr)
    );
    assert!(!file.exists());
    assert!(!sandbox.root.join("sub/sub").exists());
}

/// `ls > file` lists the working directory, as `ls` alone does. It listed
/// the session root.
#[test]
fn a_redirected_ls_lists_the_working_directory() {
    let (sandbox, _state) = sandbox();
    fs::create_dir(sandbox.root.join("sub")).unwrap();
    fs::write(sandbox.root.join("sub/inside"), "").unwrap();
    fs::write(sandbox.root.join("at-root"), "").unwrap();

    let run = shell(&sandbox.root, "cd sub; ls > listing");
    assert!(
        run.status.success(),
        "{}",
        String::from_utf8_lossy(&run.stderr)
    );

    let listing = fs::read_to_string(sandbox.root.join("sub/listing")).unwrap();
    assert!(listing.contains("inside"), "{listing}");
    assert!(!listing.contains("at-root"), "{listing}");
}

/// A working directory whose name is not text is used as the path it is.
/// It used to be written out as text and read back, which named another
/// directory.
#[test]
fn a_working_directory_whose_name_is_not_text_resolves_relative_paths() {
    use std::ffi::OsStr;
    use std::os::unix::ffi::OsStrExt;

    let (sandbox, mut state) = sandbox();
    let odd = sandbox.root.join(OsStr::from_bytes(b"d\xff"));
    fs::create_dir(&odd).unwrap();
    state.set_cwd(&odd).unwrap();

    assert_eq!(state.resolve_path("f"), odd.join("f"));
    assert_eq!(state.resolve_path("./a/../f"), odd.join("f"));
    assert_eq!(state.resolve_path("../f"), sandbox.root.join("f"));
    assert_eq!(state.resolve_path("../../../f"), sandbox.root.join("f"));
}
