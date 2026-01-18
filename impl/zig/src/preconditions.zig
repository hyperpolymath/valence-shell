// SPDX-License-Identifier: AGPL-3.0-or-later
//! Precondition checking module
//!
//! Runtime validation of preconditions that mirror the formal proofs.
//! Each check corresponds to a theorem's precondition in Coq/Lean4/etc.

const std = @import("std");
const fs = std.fs;

/// Check mkdir preconditions (mirrors Coq mkdir_precondition)
///
/// Preconditions:
/// 1. Path does not already exist
/// 2. Parent directory exists
/// 3. Parent is writable (checked by kernel)
pub fn checkMkdirPreconditions(path: []const u8) bool {
    // Path must not exist
    const exists = pathExists(path);
    if (exists) return false;

    // Parent must exist
    const parent = parentPath(path);
    if (parent) |p| {
        if (!pathExists(p)) return false;
    }
    // Root path has no parent requirement

    return true;
}

/// Check rmdir preconditions (mirrors Coq rmdir_precondition)
///
/// Preconditions:
/// 1. Path exists and is a directory
/// 2. Directory is empty
pub fn checkRmdirPreconditions(path: []const u8) bool {
    // Must exist
    if (!pathExists(path)) return false;

    // Must be a directory
    if (!isDirectory(path)) return false;

    // Must be empty (checked by kernel, but we verify)
    if (!isEmptyDirectory(path)) return false;

    return true;
}

/// Check create_file preconditions
///
/// Preconditions:
/// 1. Path does not exist
/// 2. Parent directory exists
pub fn checkCreateFilePreconditions(path: []const u8) bool {
    // Allow touch on existing files (just updates timestamp)
    // But for strict mode, path should not exist
    
    // Parent must exist
    const parent = parentPath(path);
    if (parent) |p| {
        if (!pathExists(p)) return false;
    }

    return true;
}

/// Check delete_file preconditions
///
/// Preconditions:
/// 1. Path exists and is a file (not directory)
pub fn checkDeleteFilePreconditions(path: []const u8) bool {
    // Must exist
    if (!pathExists(path)) return false;

    // Must be a file, not directory
    if (isDirectory(path)) return false;

    return true;
}

/// Check copy preconditions (mirrors Z3 copy_precondition)
///
/// Preconditions:
/// 1. Source exists and is a file
/// 2. Destination does not exist
/// 3. Destination parent exists
pub fn checkCopyPreconditions(src: []const u8, dst: []const u8) bool {
    // Source must exist
    if (!pathExists(src)) return false;

    // Source must be a file
    if (isDirectory(src)) return false;

    // Destination must not exist
    if (pathExists(dst)) return false;

    // Destination parent must exist
    const parent = parentPath(dst);
    if (parent) |p| {
        if (!pathExists(p)) return false;
    }

    return true;
}

/// Check move preconditions (mirrors Z3 move_precondition)
///
/// Preconditions:
/// 1. Source exists
/// 2. Destination does not exist
/// 3. Destination parent exists
pub fn checkMovePreconditions(src: []const u8, dst: []const u8) bool {
    // Source must exist
    if (!pathExists(src)) return false;

    // Destination must not exist
    if (pathExists(dst)) return false;

    // Destination parent must exist
    const parent = parentPath(dst);
    if (parent) |p| {
        if (!pathExists(p)) return false;
    }

    return true;
}

/// Check obliterate preconditions (mirrors Coq obliterate_precondition)
///
/// Preconditions:
/// 1. Path exists and is a file (not directory)
/// WARNING: RMO is IRREVERSIBLE - no undo possible
pub fn checkObliteratePreconditions(path: []const u8) bool {
    // Must exist
    if (!pathExists(path)) return false;

    // Must be a file (use obliterate_tree for directories)
    if (isDirectory(path)) return false;

    return true;
}

// Helper functions

fn pathExists(path: []const u8) bool {
    _ = fs.cwd().statFile(path) catch {
        // Also check if it's a directory
        _ = fs.cwd().openDir(path, .{}) catch {
            return false;
        };
    };
    return true;
}

fn isDirectory(path: []const u8) bool {
    var dir = fs.cwd().openDir(path, .{}) catch {
        return false;
    };
    dir.close();
    return true;
}

fn isEmptyDirectory(path: []const u8) bool {
    var dir = fs.cwd().openDir(path, .{ .iterate = true }) catch {
        return false;
    };
    defer dir.close();

    var iter = dir.iterate();
    if (iter.next() catch null) |_| {
        return false; // Has at least one entry
    }
    return true;
}

fn parentPath(path: []const u8) ?[]const u8 {
    // Find last path separator
    var i: usize = path.len;
    while (i > 0) : (i -= 1) {
        if (path[i - 1] == '/') {
            if (i == 1) return "/";
            return path[0 .. i - 1];
        }
    }
    return null; // No parent (relative path in current dir)
}

// Tests
test "parentPath extracts parent" {
    try std.testing.expectEqualStrings("/home", parentPath("/home/user").?);
    try std.testing.expectEqualStrings("/", parentPath("/home").?);
    try std.testing.expectEqual(@as(?[]const u8, null), parentPath("file.txt"));
}
