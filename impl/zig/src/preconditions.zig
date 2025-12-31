// SPDX-License-Identifier: AGPL-3.0-or-later
//! Valence Shell - Precondition Checking
//!
//! This module implements precondition checks derived from Coq proofs.
//! Each check corresponds to a proven precondition in filesystem_model.v
//!
//! CORRESPONDENCE TO COQ:
//!
//! mkdir_precondition p fs :=
//!   ~ path_exists p fs /\
//!   parent_exists p fs /\
//!   parent_is_dir p fs /\
//!   parent_writable p fs
//!
//! rmdir_precondition p fs :=
//!   path_exists p fs /\
//!   is_directory p fs /\
//!   is_empty p fs /\
//!   parent_writable p fs /\
//!   ~ is_root p

const std = @import("std");
const lib = @import("lib.zig");
const PosixError = lib.PosixError;

/// Check mkdir preconditions (from Coq filesystem_model.v)
///
/// Returns .success if all preconditions hold, otherwise returns
/// the appropriate POSIX error code.
pub fn checkMkdirPreconditions(full_path: []const u8) PosixError {
    // Precondition 1: Path does not exist
    if (pathExists(full_path)) {
        return .eexist;
    }

    // Get parent path
    const parent = std.fs.path.dirname(full_path) orelse return .einval;

    // Precondition 2: Parent exists
    if (!pathExists(parent)) {
        return .enoent;
    }

    // Precondition 3: Parent is a directory
    if (!isDirectory(parent)) {
        return .enotdir;
    }

    // Precondition 4: Parent is writable
    if (!isWritable(parent)) {
        return .eacces;
    }

    return .success;
}

/// Check rmdir preconditions (from Coq filesystem_model.v)
pub fn checkRmdirPreconditions(full_path: []const u8) PosixError {
    // Precondition 1: Path exists
    if (!pathExists(full_path)) {
        return .enoent;
    }

    // Precondition 2: Path is a directory
    if (!isDirectory(full_path)) {
        return .enotdir;
    }

    // Precondition 3: Directory is empty
    if (!isEmptyDirectory(full_path)) {
        return .enotempty;
    }

    // Precondition 4: Not root
    if (isRoot(full_path)) {
        return .eacces;
    }

    // Precondition 5: Parent writable
    const parent = std.fs.path.dirname(full_path) orelse return .einval;
    if (!isWritable(parent)) {
        return .eacces;
    }

    return .success;
}

/// Check create_file preconditions (from Coq file_operations.v)
pub fn checkCreateFilePreconditions(full_path: []const u8) PosixError {
    // Precondition 1: Path does not exist
    if (pathExists(full_path)) {
        return .eexist;
    }

    // Get parent path
    const parent = std.fs.path.dirname(full_path) orelse return .einval;

    // Precondition 2: Parent exists
    if (!pathExists(parent)) {
        return .enoent;
    }

    // Precondition 3: Parent is a directory
    if (!isDirectory(parent)) {
        return .enotdir;
    }

    // Precondition 4: Parent is writable
    if (!isWritable(parent)) {
        return .eacces;
    }

    return .success;
}

/// Check delete_file preconditions (from Coq file_operations.v)
pub fn checkDeleteFilePreconditions(full_path: []const u8) PosixError {
    // Precondition 1: Path exists
    if (!pathExists(full_path)) {
        return .enoent;
    }

    // Precondition 2: Path is a file (not directory)
    if (isDirectory(full_path)) {
        return .eisdir;
    }

    // Precondition 3: Parent writable
    const parent = std.fs.path.dirname(full_path) orelse return .einval;
    if (!isWritable(parent)) {
        return .eacces;
    }

    return .success;
}

// =========================================================
// Helper functions for precondition checks
// =========================================================

fn pathExists(path: []const u8) bool {
    std.fs.accessAbsolute(path, .{}) catch return false;
    return true;
}

fn isDirectory(path: []const u8) bool {
    var dir = std.fs.openDirAbsolute(path, .{}) catch return false;
    dir.close();
    return true;
}

fn isEmptyDirectory(path: []const u8) bool {
    var dir = std.fs.openDirAbsolute(path, .{ .iterate = true }) catch return false;
    defer dir.close();

    var iter = dir.iterate();
    if (iter.next() catch null) |_| {
        return false;
    }
    return true;
}

fn isWritable(path: []const u8) bool {
    // Check write access
    std.fs.accessAbsolute(path, .{ .mode = .write_only }) catch return false;
    return true;
}

fn isRoot(path: []const u8) bool {
    return std.mem.eql(u8, path, "/");
}

// =========================================================
// Extended preconditions for future operations
// =========================================================

/// Write file preconditions (for file content operations)
pub fn checkWriteFilePreconditions(full_path: []const u8) PosixError {
    // Precondition 1: Path exists
    if (!pathExists(full_path)) {
        return .enoent;
    }

    // Precondition 2: Path is a file
    if (isDirectory(full_path)) {
        return .eisdir;
    }

    // Precondition 3: File is writable
    if (!isWritable(full_path)) {
        return .eacces;
    }

    return .success;
}

/// Read file preconditions
pub fn checkReadFilePreconditions(full_path: []const u8) PosixError {
    // Precondition 1: Path exists
    if (!pathExists(full_path)) {
        return .enoent;
    }

    // Precondition 2: Path is a file
    if (isDirectory(full_path)) {
        return .eisdir;
    }

    // Precondition 3: File is readable
    std.fs.accessAbsolute(full_path, .{ .mode = .read_only }) catch return .eacces;

    return .success;
}

// =========================================================
// Tests
// =========================================================

test "mkdir_preconditions_eexist" {
    // Create test directory
    std.fs.makeDirAbsolute("/tmp/vsh_precond_test") catch {};
    defer std.fs.deleteDirAbsolute("/tmp/vsh_precond_test") catch {};

    std.fs.makeDirAbsolute("/tmp/vsh_precond_test/existing") catch {};
    defer std.fs.deleteDirAbsolute("/tmp/vsh_precond_test/existing") catch {};

    const result = checkMkdirPreconditions("/tmp/vsh_precond_test/existing");
    try std.testing.expect(result == .eexist);
}

test "mkdir_preconditions_enoent" {
    const result = checkMkdirPreconditions("/tmp/nonexistent_parent/child");
    try std.testing.expect(result == .enoent);
}

test "mkdir_preconditions_success" {
    std.fs.makeDirAbsolute("/tmp/vsh_precond_test") catch {};
    defer std.fs.deleteDirAbsolute("/tmp/vsh_precond_test") catch {};

    const result = checkMkdirPreconditions("/tmp/vsh_precond_test/newdir");
    try std.testing.expect(result == .success);
}
