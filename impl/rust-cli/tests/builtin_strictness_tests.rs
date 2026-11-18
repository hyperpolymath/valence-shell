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

/// The same inside a function, a loop and an `if`: the refused command fails
/// and the body goes on. A refusal used to be an error there, which ended
/// the whole enclosing command.
#[test]
fn a_refusal_after_expansion_does_not_end_a_function_a_loop_or_an_if() {
    for script in [
        "f() { opt=-p; mkdir $opt; echo after; }; f",
        "for x in 1; do opt=-p; mkdir $opt; echo after; done",
        "if true; then opt=-p; mkdir $opt; echo after; fi",
    ] {
        let dir = tempfile::tempdir().expect("temporary directory");

        let run = vsh(dir.path(), script);

        assert_eq!(run.stdout, "after\n", "`{script}`: stderr {}", run.stderr);
        assert!(run.stderr.contains("expands to '-p'"), "`{script}`");
        assert!(tree(dir.path()).is_empty(), "`{script}` made something");
    }
}

/// `--` ends the options for `chmod` as for the other built-ins. It used to
/// be taken for an option itself and refused.
#[test]
fn chmod_takes_its_mode_after_a_double_dash() {
    let dir = fixture();

    let run = vsh(dir.path(), "chmod -- 600 a; chmod -- -w b");

    assert_eq!(run.code, 0, "stderr: {}", run.stderr);
    let mode = |name: &str| {
        fs::metadata(dir.path().join(name))
            .expect("metadata")
            .permissions()
            .mode()
            & 0o777
    };
    assert_eq!(mode("a"), 0o600);
    assert_eq!(mode("b") & 0o222, 0, "write permission was removed");
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

/// A status that is not a number comes before the count of operands: status
/// 2, and the script stops, as under bash and dash.
#[test]
fn exit_with_a_status_that_is_not_a_number_ends_with_status_two() {
    for script in ["exit nope; touch after", "exit nope 2; touch after"] {
        let dir = tempfile::tempdir().expect("temporary directory");

        let run = vsh(dir.path(), script);

        assert_eq!(run.code, 2, "`{script}`");
        assert!(
            run.stderr.contains("numeric argument required"),
            "`{script}`: stderr {}",
            run.stderr
        );
        assert!(!dir.path().join("after").exists(), "`{script}`");
    }
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

/// A built-in that refuses its arguments fails its own command, and what
/// follows goes on from that failure. The refusal used to be a parse
/// error, which stopped the whole list, condition or loop from being read:
/// `mkdir -p x || echo fallback` printed nothing at all.
#[test]
fn a_refused_built_in_fails_only_its_own_command() {
    for (script, expected) in [
        ("mkdir -p x || echo fallback", "fallback\n"),
        ("mkdir -p x && echo and; echo status=$?", "status=1\n"),
        ("if mkdir -p x; then echo yes; else echo no; fi", "no\n"),
        (
            "for i in 1 2; do mkdir -p x; echo after; done",
            "after\nafter\n",
        ),
        ("mkdir a b || echo fallback", "fallback\n"),
        ("mkdir || echo fallback", "fallback\n"),
        ("chmod -R 600 f || echo fallback", "fallback\n"),
        ("rm -r x; echo status=$?", "status=1\n"),
    ] {
        let dir = tempfile::tempdir().expect("temporary directory");

        let run = vsh(dir.path(), script);

        assert_eq!(run.stdout, expected, "`{script}`: {}", run.stderr);
        assert!(
            tree(dir.path()).is_empty(),
            "`{script}` changed the directory: {:?}",
            tree(dir.path())
        );
    }

    // On its own, the refusal is the status of the line.
    let dir = tempfile::tempdir().expect("temporary directory");
    let run = vsh(dir.path(), "mkdir -p x");
    assert_eq!(run.code, 1, "{}", run.stderr);
    assert!(run.stderr.contains("not supported"), "{}", run.stderr);
}

/// A line that is not well formed is still a parse error, not a refusal.
#[test]
fn a_malformed_line_is_still_a_parse_error() {
    use vsh::parser::{parse_command, Command as Parsed};

    assert!(parse_command("if [ true then echo yes fi").is_err());
    assert!(parse_command("echo \"unclosed").is_err());
    assert!(matches!(
        parse_command("mkdir -p x"),
        Ok(Parsed::Refused { .. })
    ));
}

/// What follows a command sees its status as `$?`: the right side of `||`
/// and `&&`, and the branches of an `if`. They used to see the status of
/// whatever had run before the whole list, so `false || echo $?` printed 0.
#[test]
fn what_follows_a_command_sees_its_status() {
    let dir = tempfile::tempdir().expect("temporary directory");

    let run = vsh(
        dir.path(),
        "false || echo \"left $?\"; true && echo \"left $?\"; \
         if false; then echo yes; else echo \"condition $?\"; fi; \
         mkdir -p x || echo \"refused $?\"",
    );

    assert_eq!(
        run.stdout, "left 1\nleft 0\ncondition 1\nrefused 1\n",
        "stderr: {}",
        run.stderr
    );

    // The condition of an `elif` and of a loop is published in the same way.
    let run = vsh(
        dir.path(),
        "if false; then echo a; elif true; then echo \"elif $?\"; fi; \
         until false; do echo \"loop $?\"; exit 0; done",
    );

    assert_eq!(run.stdout, "elif 0\nloop 1\n", "stderr: {}", run.stderr);
}

/// A count that `undo` or `redo` cannot read is a refusal like the others:
/// the command fails and the line goes on. It used to end the line.
#[test]
fn a_count_that_cannot_be_read_fails_only_its_own_command() {
    let dir = tempfile::tempdir().expect("temporary directory");

    let run = vsh(
        dir.path(),
        "undo many || echo first; redo 1 2 || echo second",
    );

    assert_eq!(run.stdout, "first\nsecond\n", "stderr: {}", run.stderr);
    assert_eq!(run.code, 0);
}

/// The text of an EXIT trap is a list of commands, and each of them runs.
/// It used to be read as one command: `echo` was given `first; echo second`.
#[test]
fn an_exit_trap_runs_every_statement_of_its_text() {
    let dir = tempfile::tempdir().expect("temporary directory");

    let run = vsh(dir.path(), "trap 'echo first; echo second' EXIT; exit 3");

    assert_eq!(run.stdout, "first\nsecond\n", "stderr: {}", run.stderr);
    assert_eq!(run.code, 3);
}

/// A statement of an EXIT trap that fails is reported, and the statements
/// after it still run. Its error was dropped without a word.
#[test]
fn an_exit_trap_reports_a_statement_that_fails() {
    let dir = tempfile::tempdir().expect("temporary directory");

    let run = vsh(
        dir.path(),
        "mkdir d\ntrap 'mkdir d; echo second' EXIT\necho body",
    );

    assert!(
        run.stdout.ends_with("body\nsecond\n"),
        "stdout: {}",
        run.stdout
    );
    assert!(run.stderr.contains("vsh: trap: "), "stderr: {}", run.stderr);
    assert!(run.stderr.contains("exists"), "stderr: {}", run.stderr);
}
