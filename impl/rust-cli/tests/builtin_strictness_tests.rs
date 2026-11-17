// SPDX-License-Identifier: MPL-2.0
// Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//! A built-in command refuses what it does not handle, and then does nothing.
//!
//! The built-in file commands take fewer forms than the system ones. They used
//! to take an option for a file name and to drop the operands they had no room
//! for, and report success: `mkdir -p a/b` made a directory named `-p`, and
//! `touch a b c` made only `a`. Each test here runs the built shell and checks
//! both the refusal and that the directory is as it was.

use std::collections::BTreeSet;
use std::fs;
use std::os::unix::fs::PermissionsExt;
use std::path::Path;
use std::process::{Command, Stdio};

struct Run {
    code: i32,
    stdout: String,
    stderr: String,
}

fn vsh(dir: &Path, script: &str) -> Run {
    let output = Command::new(env!("CARGO_BIN_EXE_vsh"))
        .arg("-r")
        .arg(dir)
        .arg("-c")
        .arg(script)
        .current_dir(dir)
        .env("NO_COLOR", "1")
        .env_remove("RUST_BACKTRACE")
        .stdin(Stdio::null())
        .output()
        .expect("start the built shell");
    Run {
        code: output.status.code().unwrap_or(-1),
        stdout: String::from_utf8_lossy(&output.stdout).into_owned(),
        stderr: String::from_utf8_lossy(&output.stderr).into_owned(),
    }
}

/// Every path under `dir`, relative to it, without the shell's own state files.
fn tree(dir: &Path) -> BTreeSet<String> {
    fn walk(base: &Path, at: &Path, found: &mut BTreeSet<String>) {
        for entry in fs::read_dir(at).expect("read directory") {
            let path = entry.expect("directory entry").path();
            let name = path
                .strip_prefix(base)
                .expect("inside the base")
                .to_string_lossy()
                .into_owned();
            if name.starts_with(".vsh") {
                continue;
            }
            let is_dir = fs::symlink_metadata(&path)
                .expect("metadata")
                .file_type()
                .is_dir();
            found.insert(name);
            if is_dir {
                walk(base, &path, found);
            }
        }
    }
    let mut found = BTreeSet::new();
    walk(dir, dir, &mut found);
    found
}

/// A directory holding files `a` and `b`, and a directory `d` holding `inner`.
fn fixture() -> tempfile::TempDir {
    let dir = tempfile::tempdir().expect("temporary directory");
    fs::write(dir.path().join("a"), "alpha\n").expect("write a");
    fs::write(dir.path().join("b"), "beta\n").expect("write b");
    fs::create_dir(dir.path().join("d")).expect("create d");
    fs::write(dir.path().join("d/inner"), "inner\n").expect("write inner");
    dir
}

/// Runs `script`, which must be refused, and checks nothing changed.
fn refused(script: &str, expected_in_message: &str) {
    let dir = fixture();
    let before = tree(dir.path());

    let run = vsh(dir.path(), script);

    assert_ne!(run.code, 0, "`{script}` should not report success");
    assert!(
        run.stderr.contains(expected_in_message),
        "`{script}` should say {expected_in_message:?}; it said {:?}",
        run.stderr
    );
    assert_eq!(
        tree(dir.path()),
        before,
        "`{script}` was refused but still changed the directory"
    );
    assert_eq!(
        fs::read_to_string(dir.path().join("a")).expect("read a"),
        "alpha\n",
        "`{script}` changed the contents of a"
    );
}

#[test]
fn an_option_is_never_taken_for_a_file_name() {
    for script in [
        "mkdir -p x/y",
        "rmdir -p d",
        "touch -c x",
        "rm -rf d",
        "rm -f a",
        "cp -r d e",
        "cp -p a c",
        "mv -f a b",
        "chown -R 0:0 d",
        "ln -sf a l",
        "ls -la",
        "cd -P d",
    ] {
        refused(script, "is not supported by the built-in");
    }
}

#[test]
fn chmod_refuses_its_options_but_takes_a_mode_that_starts_with_a_dash() {
    refused("chmod -R 700 d", "is not supported by the built-in");
    refused(
        "chmod --recursive 700 d",
        "is not supported by the built-in",
    );

    let dir = fixture();
    let file = dir.path().join("a");
    fs::set_permissions(&file, fs::Permissions::from_mode(0o755)).expect("set mode");

    let run = vsh(dir.path(), "chmod -x a");

    assert_eq!(run.code, 0, "chmod -x a failed: {}", run.stderr);
    let mode = fs::metadata(&file).expect("metadata").permissions().mode() & 0o777;
    assert_eq!(mode, 0o644, "the execute bits should be gone");
}

#[test]
fn operands_with_no_place_to_go_are_never_dropped() {
    for script in [
        "mkdir x y",
        "rmdir d e",
        "touch x y z",
        "rm a b",
        "cp a b d",
        "mv a b d",
        "chown 0:0 a b",
        "ln -s a l m",
        "ls d d",
        "cd d d",
    ] {
        refused(script, "were given; nothing was done");
    }
}

#[test]
fn chmod_does_not_change_the_first_file_when_given_two() {
    let dir = fixture();
    let before = fs::metadata(dir.path().join("a"))
        .expect("metadata")
        .permissions()
        .mode();

    let run = vsh(dir.path(), "chmod 600 a b");

    assert_ne!(run.code, 0);
    let after = fs::metadata(dir.path().join("a"))
        .expect("metadata")
        .permissions()
        .mode();
    assert_eq!(after, before, "a refused chmod must change no mode");
}

#[test]
fn obliterate_refuses_a_second_target_and_an_unknown_option() {
    refused("obliterate --force a b", "were given; nothing was done");
    refused("obliterate --frce a", "is not supported by the built-in");
}

#[test]
fn undo_and_redo_refuse_a_count_they_cannot_read() {
    let dir = tempfile::tempdir().expect("temporary directory");

    let run = vsh(dir.path(), "touch kept; undo many");

    assert_ne!(run.code, 0);
    assert!(
        run.stderr.contains("is not a count of operations"),
        "undo said {:?}",
        run.stderr
    );
    assert!(
        dir.path().join("kept").exists(),
        "`undo many` must not undo anything"
    );

    let run = vsh(dir.path(), "undo 1 2");
    assert_ne!(run.code, 0);
    assert!(dir.path().join("kept").exists());

    let run = vsh(dir.path(), "redo 0");
    assert_ne!(run.code, 0);
}

#[test]
fn a_double_dash_lets_a_name_start_with_a_dash() {
    let dir = tempfile::tempdir().expect("temporary directory");

    let run = vsh(dir.path(), "mkdir -- -p");

    assert_eq!(run.code, 0, "mkdir -- -p failed: {}", run.stderr);
    assert!(dir.path().join("-p").is_dir());
}

/// The parser sees `$opt`, not what it holds. A word that reads as an option
/// only once it is expanded is refused as well: `opt=-p; mkdir $opt` used to
/// make a directory named `-p`.
#[test]
fn an_operand_that_expands_to_an_option_is_refused() {
    refused("opt=-p; mkdir $opt", "expands to '-p'");
    refused("opt=-rf; rm $opt", "expands to '-rf'");
    refused("opt=-r; rmdir $opt", "expands to '-r'");
    refused("opt=-c; touch $opt", "expands to '-c'");
    refused("opt=-la; ls $opt", "expands to '-la'");
    refused("opt=-L; cd $opt", "expands to '-L'");
    refused("opt=-r; cp $opt a", "expands to '-r'");
    refused("opt=-f; mv a $opt", "expands to '-f'");
    refused("opt=-f; ln -s a $opt", "expands to '-f'");
    refused("opt=--force; obliterate $opt", "expands to '--force'");
    refused("opt=-R; chmod $opt a", "expands to '-R'");
    refused("opt=-v; chmod 600 $opt", "expands to '-v'");
}

/// Such a refusal fails its own command and no more, like one found while
/// the line was parsed.
#[test]
fn a_refusal_after_expansion_does_not_end_the_script() {
    let dir = tempfile::tempdir().expect("temporary directory");

    let run = vsh(dir.path(), "opt=-p; mkdir $opt; echo status=$?");

    assert_eq!(run.stdout, "status=1\n", "stderr: {}", run.stderr);
    assert!(tree(dir.path()).is_empty());
}

/// What an expansion may still produce: a mode that starts with a dash, and
/// the lone dash that means the previous directory.
#[test]
fn an_expansion_may_still_give_a_mode_or_a_lone_dash() {
    let dir = fixture();

    let run = vsh(dir.path(), "m=-w; chmod $m a; cd d; p=-; cd $p");

    assert_eq!(run.code, 0, "stderr: {}", run.stderr);
    let mode = fs::metadata(dir.path().join("a"))
        .expect("metadata")
        .permissions()
        .mode();
    assert_eq!(mode & 0o222, 0, "write permission was removed");
}

/// `exit` with more than one operand is an error, and a script stops there
/// with status 1, as it does under bash and dash. It used to print the error
/// and carry on with the rest of the script.
#[test]
fn exit_with_too_many_operands_stops_the_script() {
    let dir = tempfile::tempdir().expect("temporary directory");

    let run = vsh(dir.path(), "exit 1 2; touch after");

    assert_eq!(run.code, 1);
    assert!(
        run.stderr.contains("too many arguments"),
        "stderr: {}",
        run.stderr
    );
    assert!(!dir.path().join("after").exists());
}

#[test]
fn a_refusal_does_not_end_the_script() {
    let dir = tempfile::tempdir().expect("temporary directory");

    let run = vsh(dir.path(), "mkdir -p x/y; echo after");

    assert!(
        run.stdout.contains("after"),
        "the script should go on after a refused command; stdout was {:?}",
        run.stdout
    );
}

#[test]
fn the_forms_the_built_ins_do_handle_still_work() {
    let dir = tempfile::tempdir().expect("temporary directory");

    let run = vsh(
        dir.path(),
        "mkdir d; touch d/f; cp d/f g; mv g h; chmod 600 h; ln -s h l; rm d/f; rmdir d; ls",
    );

    assert_eq!(run.code, 0, "stderr: {}", run.stderr);
    let expected: BTreeSet<String> = ["h", "l"].iter().map(|name| name.to_string()).collect();
    assert_eq!(tree(dir.path()), expected);
    let mode = fs::metadata(dir.path().join("h"))
        .expect("metadata")
        .permissions()
        .mode()
        & 0o777;
    assert_eq!(mode, 0o600);
}
