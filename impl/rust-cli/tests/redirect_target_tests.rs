// SPDX-License-Identifier: MPL-2.0
// Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//! A built-in's redirected output goes to the file that was opened and
//! checked when the redirection was set up.
//!
//! This file holds one test, in a process of its own: capturing a
//! built-in's output redirects the standard output of the whole process.

#![cfg(unix)]

mod fixtures;

use fixtures::sandbox;
use std::fs;
use vsh::redirection::{capture_and_redirect, Redirection};

/// Between the set-up and the write, the name is given to a file outside
/// the session root, as a hard link. The write used to open the name a
/// second time. That open was beneath the root, so a symbolic link was
/// refused, but a hard link is an ordinary file: the file outside was
/// truncated and written, without the check on the number of links that
/// the set-up had made.
#[test]
fn a_built_in_writes_to_the_file_that_was_opened_and_checked() {
    let (sandbox, mut state) = sandbox();
    let victim = sandbox.outside.join("victim");
    fs::write(&victim, "PRECIOUS").unwrap();
    let out = sandbox.root.join("out");
    let redirects = vec![Redirection::Output {
        file: "out".to_string(),
    }];

    capture_and_redirect(&redirects, &mut state, |_| {
        fs::remove_file(&out).unwrap();
        fs::hard_link(&victim, &out).unwrap();
        println!("from the built-in");
        Ok(())
    })
    .unwrap();

    assert_eq!(fs::read_to_string(&victim).unwrap(), "PRECIOUS");
}
