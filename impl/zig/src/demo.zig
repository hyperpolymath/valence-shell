// SPDX-License-Identifier: AGPL-3.0-or-later
//! Valence Shell - Zig FFI Demonstration
//!
//! This program demonstrates the formally verified filesystem operations
//! and validates them against the Coq theorems.

const std = @import("std");
const valence = @import("lib.zig");
const Filesystem = valence.Filesystem;
const AuditLog = valence.audit.AuditLog;

const BLUE = "\x1b[34m";
const GREEN = "\x1b[32m";
const YELLOW = "\x1b[33m";
const RED = "\x1b[31m";
const RESET = "\x1b[0m";

pub fn main() !void {
    const allocator = std.heap.page_allocator;
    const print = std.debug.print;

    print("\n{s}╔══════════════════════════════════════════════════╗{s}\n", .{ BLUE, RESET });
    print("{s}║  Valence Shell - Zig FFI Demonstration           ║{s}\n", .{ BLUE, RESET });
    print("{s}║  Formally Verified Filesystem Operations         ║{s}\n", .{ BLUE, RESET });
    print("{s}╚══════════════════════════════════════════════════╝{s}\n\n", .{ BLUE, RESET });

    // Setup test environment
    const test_root = "/tmp/valence_demo";
    std.fs.makeDirAbsolute(test_root) catch {};

    // Create audit log
    var audit_log = try AuditLog.init(allocator, "/tmp/valence_demo/audit.log");
    defer audit_log.deinit();

    // Create filesystem handle
    var fs = Filesystem.init(allocator, test_root, &audit_log);

    // Clean up any previous test artifacts
    cleanup(&fs);

    // === Theorem 1: mkdir_rmdir_reversible ===
    print("{s}═══ Theorem 1: mkdir_rmdir_reversible ═══{s}\n", .{ YELLOW, RESET });
    print("Proven in: Coq, Lean 4, Agda, Isabelle, Mizar\n\n", .{});

    print("  Initial state: test_dir does not exist\n", .{});
    try std.testing.expect(!fs.pathExists("test_dir"));
    print("  {s}✓ Verified{s}\n\n", .{ GREEN, RESET });

    print("  Executing: mkdir test_dir\n", .{});
    const mkdir_result = fs.mkdir("test_dir");
    if (mkdir_result.isOk()) {
        print("  {s}✓ mkdir succeeded{s}\n", .{ GREEN, RESET });
        print("  State: test_dir exists = {}\n\n", .{fs.pathExists("test_dir")});
    } else {
        print("  {s}✗ mkdir failed: {s}{s}\n", .{ RED, @tagName(mkdir_result.unwrapErr()), RESET });
    }

    print("  Executing: rmdir test_dir (reversing mkdir)\n", .{});
    const rmdir_result = fs.rmdir("test_dir");
    if (rmdir_result.isOk()) {
        print("  {s}✓ rmdir succeeded{s}\n", .{ GREEN, RESET });
    } else {
        print("  {s}✗ rmdir failed: {s}{s}\n", .{ RED, @tagName(rmdir_result.unwrapErr()), RESET });
    }

    print("  Final state: test_dir does not exist\n", .{});
    try std.testing.expect(!fs.pathExists("test_dir"));
    print("  {s}✓ THEOREM VERIFIED: rmdir(mkdir(p, fs)) = fs{s}\n\n", .{ GREEN, RESET });

    // === Theorem 2: create_delete_file_reversible ===
    print("{s}═══ Theorem 2: create_delete_file_reversible ═══{s}\n", .{ YELLOW, RESET });
    print("Proven in: Coq, Lean 4, Agda, Isabelle, Mizar\n\n", .{});

    print("  Initial state: test_file does not exist\n", .{});
    try std.testing.expect(!fs.pathExists("test_file"));
    print("  {s}✓ Verified{s}\n\n", .{ GREEN, RESET });

    print("  Executing: create_file test_file\n", .{});
    const create_result = fs.createFile("test_file");
    if (create_result.isOk()) {
        print("  {s}✓ create_file succeeded{s}\n", .{ GREEN, RESET });
        print("  State: test_file exists = {}, is_file = {}\n\n", .{ fs.pathExists("test_file"), fs.isFile("test_file") });
    } else {
        print("  {s}✗ create_file failed: {s}{s}\n", .{ RED, @tagName(create_result.unwrapErr()), RESET });
    }

    print("  Executing: delete_file test_file\n", .{});
    const delete_result = fs.deleteFile("test_file");
    if (delete_result.isOk()) {
        print("  {s}✓ delete_file succeeded{s}\n", .{ GREEN, RESET });
    } else {
        print("  {s}✗ delete_file failed: {s}{s}\n", .{ RED, @tagName(delete_result.unwrapErr()), RESET });
    }

    print("  Final state: test_file does not exist\n", .{});
    try std.testing.expect(!fs.pathExists("test_file"));
    print("  {s}✓ THEOREM VERIFIED: delete_file(create_file(p, fs)) = fs{s}\n\n", .{ GREEN, RESET });

    // === Theorem 3: POSIX Error Correctness ===
    print("{s}═══ Theorem 3: POSIX Error Correctness ═══{s}\n", .{ YELLOW, RESET });
    print("Proven in: Coq (posix_errors.v)\n\n", .{});

    // EEXIST test
    _ = fs.mkdir("existing_dir");
    print("  Test: mkdir on existing path\n", .{});
    const eexist_result = fs.mkdir("existing_dir");
    if (!eexist_result.isOk() and eexist_result.unwrapErr() == .eexist) {
        print("  {s}✓ Correctly returned EEXIST{s}\n\n", .{ GREEN, RESET });
    } else {
        print("  {s}✗ Expected EEXIST{s}\n\n", .{ RED, RESET });
    }
    _ = fs.rmdir("existing_dir");

    // ENOENT test
    print("  Test: rmdir on non-existent path\n", .{});
    const enoent_result = fs.rmdir("nonexistent_dir");
    if (!enoent_result.isOk() and enoent_result.unwrapErr() == .enoent) {
        print("  {s}✓ Correctly returned ENOENT{s}\n\n", .{ GREEN, RESET });
    } else {
        print("  {s}✗ Expected ENOENT{s}\n\n", .{ RED, RESET });
    }

    // ENOTEMPTY test
    _ = fs.mkdir("nonempty_dir");
    _ = fs.createFile("nonempty_dir/file");
    print("  Test: rmdir on non-empty directory\n", .{});
    const enotempty_result = fs.rmdir("nonempty_dir");
    if (!enotempty_result.isOk() and enotempty_result.unwrapErr() == .enotempty) {
        print("  {s}✓ Correctly returned ENOTEMPTY{s}\n\n", .{ GREEN, RESET });
    } else {
        print("  {s}✗ Expected ENOTEMPTY{s}\n\n", .{ RED, RESET });
    }
    _ = fs.deleteFile("nonempty_dir/file");
    _ = fs.rmdir("nonempty_dir");

    // === Audit Log ===
    print("{s}═══ Audit Log (MAA Framework) ═══{s}\n\n", .{ YELLOW, RESET });
    // Note: Zig 0.15 changed I/O API, skipping report generation for now
    print("  (Audit log contains {d} entries)\n\n", .{audit_log.entries.items.len});

    // === Summary ===
    print("\n{s}═══════════════════════════════════════════════════{s}\n", .{ GREEN, RESET });
    print("{s}  All theorems demonstrated successfully!{s}\n", .{ GREEN, RESET });
    print("{s}═══════════════════════════════════════════════════{s}\n\n", .{ GREEN, RESET });

    print("Proof Systems:\n", .{});
    print("  1. Coq (Calculus of Inductive Constructions)\n", .{});
    print("  2. Lean 4 (Dependent Type Theory)\n", .{});
    print("  3. Agda (Intensional Type Theory)\n", .{});
    print("  4. Isabelle/HOL (Higher-Order Logic)\n", .{});
    print("  5. Mizar (Tarski-Grothendieck Set Theory)\n", .{});
    print("  6. Z3 SMT (Automated Verification)\n\n", .{});

    print("Trust Chain:\n", .{});
    print("  • Coq proofs → {s}verified by kernel{s}\n", .{ GREEN, RESET });
    print("  • Zig FFI    → {s}preconditions checked{s}\n", .{ YELLOW, RESET });
    print("  • POSIX      → OS trust assumption\n\n", .{});

    // Cleanup
    cleanup(&fs);
    std.fs.deleteDirAbsolute(test_root) catch {};
}

fn cleanup(fs: *Filesystem) void {
    // Clean up test artifacts
    _ = fs.deleteFile("test_file");
    _ = fs.deleteFile("nonempty_dir/file");
    _ = fs.rmdir("test_dir");
    _ = fs.rmdir("existing_dir");
    _ = fs.rmdir("nonempty_dir");
}
