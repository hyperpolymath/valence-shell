// SPDX-License-Identifier: MPL-2.0
// Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//! The SIGCHLD handler. It installs a process-wide handler and reads a global
//! flag, so it runs in its own test binary, apart from the job table tests.

#![cfg(unix)]

use std::time::{Duration, Instant};

#[test]
fn the_sigchld_handler_sets_the_flag() {
    vsh::job::install_sigchld_handler().unwrap();
    vsh::job::take_sigchld();
    // SAFETY: getpid and kill take plain integers; the signal goes to
    // this process, whose SIGCHLD handler only stores to an atomic.
    unsafe {
        libc::kill(libc::getpid(), libc::SIGCHLD);
    }
    let started = Instant::now();
    while !vsh::job::take_sigchld() {
        assert!(started.elapsed() < Duration::from_secs(5), "flag not set");
        std::thread::sleep(Duration::from_millis(5));
    }
}

#[test]
fn a_read_interrupted_by_sigchld_is_restarted() {
    // A raw read(2) is not retried by std: without SA_RESTART it returns
    // EINTR when SIGCHLD arrives during it.
    vsh::job::install_sigchld_handler().unwrap();
    let mut fds = [0; 2];
    // SAFETY: `fds` is a live array of two c_ints for pipe(2) to fill.
    assert_eq!(unsafe { libc::pipe(fds.as_mut_ptr()) }, 0);
    let (read_fd, write_fd) = (fds[0], fds[1]);
    let (tx, rx) = std::sync::mpsc::channel();
    let reader = std::thread::spawn(move || {
        // SAFETY: pthread_self takes no arguments.
        tx.send(unsafe { libc::pthread_self() }).unwrap();
        let mut byte = 0u8;
        // SAFETY: `byte` is a live, exclusively borrowed u8 and the length
        // is 1; read_fd is the open read end of the pipe.
        let n = unsafe { libc::read(read_fd, (&mut byte as *mut u8).cast(), 1) };
        let errno = std::io::Error::last_os_error();
        (n, byte, errno)
    });
    let thread = rx.recv().unwrap();
    std::thread::sleep(Duration::from_millis(100));
    // SAFETY: `thread` is the live reader thread, blocked in read(2).
    assert_eq!(unsafe { libc::pthread_kill(thread, libc::SIGCHLD) }, 0);
    std::thread::sleep(Duration::from_millis(100));
    // SAFETY: write_fd is the open write end; one byte from a live u8.
    assert_eq!(
        unsafe { libc::write(write_fd, (&b'x' as *const u8).cast(), 1) },
        1
    );
    let (n, byte, errno) = reader.join().unwrap();
    assert_eq!(n, 1, "read was interrupted: {errno}");
    assert_eq!(byte, b'x');
    // SAFETY: both descriptors are open and owned by this test.
    unsafe {
        libc::close(read_fd);
        libc::close(write_fd);
    }
}
