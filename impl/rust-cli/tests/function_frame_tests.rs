// SPDX-License-Identifier: MPL-2.0
// Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//! A function gives its caller's variables and positional parameters back,
//! also when a command in it fails.
//!
//! A call pushes a frame: the caller's positional parameters, and the old
//! value of each variable the body declares `local`. The frame was popped
//! when the body ran to its end or reached `return`. A command that returned
//! an error left through `?`, past the pop. The caller then kept the
//! function's `local` values, had the function's arguments as `$1`, `$2`,
//! ..., and the shell went on as if it were still inside the function.
//!
//! These tests run the built shell, and they run it as a person does: at the
//! prompt, through a pseudo-terminal. That is where the fault shows. The
//! prompt reports an error and reads the next line with the same state. With
//! `-c` or a script file the first error ends the whole run (another fault,
//! not this one), so no command is left to show what the caller kept.
//!
//! The `after:` lines expected here are what GNU bash 5.2.21 prints for the
//! same lines.
//!
//! Built on Linux only: the pseudo-terminal handling here has been run
//! nowhere else.

#![cfg(target_os = "linux")]

use std::fs::{self, File};
use std::io::{Read, Write};
use std::path::Path;
use std::process::{Command, Stdio};
use std::sync::mpsc;
use std::time::{Duration, Instant};

use nix::fcntl::{fcntl, FcntlArg, FdFlag};
use nix::pty::{openpty, Winsize};

/// The line editor asks the terminal where the cursor is before it draws the
/// prompt, and gives up after two seconds without an answer.
const CURSOR_QUERY: &[u8] = b"\x1b[6n";

/// What a terminal answers: row 1, column 1.
const CURSOR_ANSWER: &[u8] = b"\x1b[1;1R";

/// Every prompt of the shell ends like this, in both of its builds.
const PROMPT_END: &str = "> ";

/// The longest a session may take. One takes well under a second.
const LIMIT: Duration = Duration::from_secs(30);

/// Runs the built shell at its prompt in `dir`, types `lines` and then
/// `exit`, and returns everything the shell sent to the terminal.
///
/// The shell has two prompts. The default build reads keys through a line
/// editor; a build with `--no-default-features` prints a prompt and reads a
/// line. Both are driven here, whichever was built.
fn at_the_prompt(dir: &Path, lines: &[&str]) -> String {
    let size = Winsize {
        ws_row: 24,
        ws_col: 80,
        ws_xpixel: 0,
        ws_ypixel: 0,
    };
    let pty = openpty(Some(&size), None).expect("open a pseudo-terminal");
    // Keep both ends out of the shells that other tests start meanwhile.
    for end in [&pty.master, &pty.slave] {
        fcntl(end, FcntlArg::F_SETFD(FdFlag::FD_CLOEXEC)).expect("set close-on-exec");
    }
    let mut screen = File::from(pty.master);
    let mut keyboard = screen.try_clone().expect("a second handle on the terminal");

    let mut shell = {
        let terminal = pty.slave;
        let mut command = Command::new(env!("CARGO_BIN_EXE_vsh"));
        command
            .arg("-r")
            .arg(dir)
            .current_dir(dir)
            // The line editor keeps its history file in the home directory.
            .env("HOME", dir)
            .env("NO_COLOR", "1")
            .env("TERM", "xterm")
            .env_remove("RUST_BACKTRACE")
            .stdin(Stdio::from(
                terminal.try_clone().expect("terminal for input"),
            ))
            .stdout(Stdio::from(
                terminal.try_clone().expect("terminal for output"),
            ))
            .stderr(Stdio::from(terminal));
        command.spawn().expect("start the built shell")
        // `command` ends here, and with it this process's handles on the
        // shell's end of the terminal: reading `screen` stops once the
        // shell has gone.
    };

    // Read on a thread of its own, so that a shell that never finishes
    // cannot hold the test past `LIMIT`.
    let (sender, sent) = mpsc::channel::<Vec<u8>>();
    let reader = std::thread::spawn(move || {
        let mut chunk = [0u8; 4096];
        // Reading ends with an error once the shell has gone.
        while let Ok(count) = screen.read(&mut chunk) {
            if count == 0 || sender.send(chunk[..count].to_vec()).is_err() {
                break;
            }
        }
    });

    let started = Instant::now();
    let mut to_type = lines.iter().copied().chain(["exit"]);
    let mut transcript: Vec<u8> = Vec::new();
    let mut searched = 0;
    let mut line_editor = false;
    let mut typed_at = 0;
    let status = loop {
        let gone = match sent.recv_timeout(Duration::from_millis(20)) {
            Ok(chunk) => {
                transcript.extend_from_slice(&chunk);
                false
            }
            Err(mpsc::RecvTimeoutError::Timeout) => false,
            Err(mpsc::RecvTimeoutError::Disconnected) => true,
        };

        // The line editor asks for the cursor before it draws each prompt.
        while let Some(at) = find(&transcript[searched..], CURSOR_QUERY) {
            searched += at + CURSOR_QUERY.len();
            press(&mut keyboard, CURSOR_ANSWER);
            if !line_editor {
                // The first query means the editor is reading keys. Type
                // every line now: it takes one line at each Enter and keeps
                // the rest for its next prompt.
                line_editor = true;
                for line in to_type.by_ref() {
                    type_line(&mut keyboard, line);
                }
            }
        }

        // The plain prompt asks nothing: it is printed, and the shell waits
        // for a line. Type one line at each new prompt.
        if !line_editor && transcript.len() > typed_at {
            let shown = plain(&String::from_utf8_lossy(&transcript));
            if shown.ends_with(PROMPT_END) {
                if let Some(line) = to_type.next() {
                    type_line(&mut keyboard, line);
                    typed_at = transcript.len();
                }
            }
        }

        if gone {
            match shell.try_wait().expect("wait for the shell") {
                Some(status) => break status,
                // The terminal closes a moment before the shell can be
                // waited for.
                None => std::thread::sleep(Duration::from_millis(1)),
            }
        }
        if started.elapsed() > LIMIT {
            let _ = shell.kill();
            let _ = shell.wait();
            panic!(
                "the shell did not finish within {LIMIT:?}; the terminal showed:\n{}",
                plain(&String::from_utf8_lossy(&transcript))
            );
        }
    };
    reader.join().expect("the reading thread");

    let transcript = String::from_utf8_lossy(&transcript).into_owned();
    assert!(
        to_type.next().is_none(),
        "the shell left ({status}) before every line was typed; the terminal showed:\n{}",
        plain(&transcript)
    );
    transcript
}

/// Sends `keys` to the shell as if they were pressed.
///
/// The write fails only when the shell has gone. The transcript then says
/// why, and the assertions show it.
fn press(keyboard: &mut File, keys: &[u8]) {
    let _ = keyboard.write_all(keys);
}

/// Types `line` and presses Enter.
fn type_line(keyboard: &mut File, line: &str) {
    press(keyboard, line.as_bytes());
    press(keyboard, b"\r");
}

fn find(haystack: &[u8], needle: &[u8]) -> Option<usize> {
    haystack
        .windows(needle.len())
        .position(|window| window == needle)
}

/// `text` without the colour and cursor codes the line editor sends.
fn plain(text: &str) -> String {
    let mut out = String::new();
    let mut chars = text.chars();
    while let Some(c) = chars.next() {
        if c != '\x1b' {
            out.push(c);
            continue;
        }
        // Either `ESC [`, parameters and a final letter, or `ESC` and one
        // character.
        if chars.next() == Some('[') {
            for c in chars.by_ref() {
                if ('@'..='~').contains(&c) {
                    break;
                }
            }
        }
    }
    out
}

/// The lines the shell printed that start with `prefix`.
///
/// A line the test typed never does: it is shown after the prompt.
fn printed(transcript: &str, prefix: &str) -> Vec<String> {
    plain(transcript)
        .lines()
        .map(str::trim_end)
        .filter(|line| line.starts_with(prefix))
        .map(String::from)
        .collect()
}

/// A fresh directory holding `functions` in `defs.sh`, for `source`.
///
/// The functions come from a file because the prompt cuts a typed line at
/// every `;`, also inside `{ }`: a body of two commands cannot be typed
/// there on one line.
fn directory_with(functions: &str) -> tempfile::TempDir {
    let dir = tempfile::tempdir().expect("temporary directory");
    fs::write(dir.path().join("defs.sh"), functions).expect("write defs.sh");
    dir
}

/// In every test the command that fails is `mkdir` under a directory that
/// does not exist. The built-in returns an error for it.
const NO_PARENT: &str = "mkdir /no/such/parent/dir";

#[test]
fn a_function_that_fails_leaves_the_callers_variable_as_it_was() {
    let dir = directory_with(&format!("f() {{ local x=inner; {NO_PARENT}; }}\n"));

    let seen = at_the_prompt(
        dir.path(),
        &[
            "source ./defs.sh",
            "x=outer",
            "f",
            r#"echo "after: x is $x.""#,
        ],
    );

    assert_eq!(
        printed(&seen, "after:"),
        ["after: x is outer."],
        "the terminal showed:\n{}",
        plain(&seen)
    );
    // The frame is popped; the failure is still reported.
    assert_eq!(
        printed(&seen, "vsh: Parent directory does not exist").len(),
        1,
        "the failed mkdir should be reported once; the terminal showed:\n{}",
        plain(&seen)
    );
}

#[test]
fn a_function_that_fails_gives_the_caller_its_positional_parameters_back() {
    let dir = directory_with(&format!("f() {{ {NO_PARENT}; }}\n"));

    let seen = at_the_prompt(
        dir.path(),
        &[
            "source ./defs.sh",
            "set -- outer1 outer2",
            "f inner1",
            r#"echo "after: first is $1, count is $#.""#,
        ],
    );

    assert_eq!(
        printed(&seen, "after:"),
        ["after: first is outer1, count is 2."],
        "the terminal showed:\n{}",
        plain(&seen)
    );
}

/// `outer` calls `inner`, and a command in `inner` fails. The error passes
/// through both, so both frames have to go: the caller sees neither
/// `inner`'s variable and argument nor `outer`'s.
#[test]
fn a_failure_in_a_nested_call_pops_the_frame_of_every_function_it_leaves() {
    let dir = directory_with(&format!(
        "inner() {{ local x=in; {NO_PARENT}; }}\n\
         outer() {{ local x=mid; inner deep; }}\n"
    ));

    let seen = at_the_prompt(
        dir.path(),
        &[
            "source ./defs.sh",
            "x=top",
            "set -- top1",
            "outer mid1 mid2",
            r#"echo "after: x is $x, first is $1, count is $#.""#,
        ],
    );

    assert_eq!(
        printed(&seen, "after:"),
        ["after: x is top, first is top1, count is 1."],
        "the terminal showed:\n{}",
        plain(&seen)
    );
}

/// The shell counts frames to know whether it is inside a function. With
/// the frame left behind, `local` and `return` typed at the prompt were
/// accepted. bash refuses both there.
#[test]
fn after_a_function_failed_the_shell_is_no_longer_inside_it() {
    let dir = directory_with(&format!("f() {{ {NO_PARENT}; }}\n"));

    let seen = at_the_prompt(
        dir.path(),
        &["source ./defs.sh", "f", "local y=1", "return 0"],
    );

    for refused in ["vsh: local:", "vsh: return:"] {
        assert_eq!(
            printed(&seen, refused).len(),
            1,
            "a line starting {refused:?} should be printed once; the terminal showed:\n{}",
            plain(&seen)
        );
    }
}
