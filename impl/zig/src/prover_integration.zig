// SPDX-License-Identifier: AGPL-3.0-or-later
//! Valence Shell - Prover Integration
//!
//! Demonstrates integration with zig-prover-ffi for runtime verification
//! of formal proofs. This bridges the Coq/Lean/Agda/Isabelle/Mizar/Z3
//! proof files in proofs/ with the Zig implementation.
//!
//! Use cases:
//! 1. CI verification of proof files
//! 2. Runtime verification before critical operations
//! 3. Proof certificate validation

const std = @import("std");
const prover = @import("prover");

/// Proof verification result for valence-shell operations
pub const VerificationResult = struct {
    status: prover.ProofStatus,
    prover_used: prover.ProverKind,
    duration_ms: u64,
    message: []const u8,

    pub fn isVerified(self: VerificationResult) bool {
        return self.status == .verified;
    }
};

/// Verifies a proof file using the appropriate prover
pub fn verifyProofFile(
    allocator: std.mem.Allocator,
    file_path: []const u8,
    endpoint: []const u8,
) !VerificationResult {
    // Detect prover from file extension
    const ext = std.fs.path.extension(file_path);
    const prover_kind = prover.ProverKind.fromExtension(ext) orelse {
        return VerificationResult{
            .status = .unknown,
            .prover_used = .z3, // placeholder
            .duration_ms = 0,
            .message = "Unknown file extension - cannot determine prover",
        };
    };

    // Read file content
    const file = try std.fs.cwd().openFile(file_path, .{});
    defer file.close();
    const content = try file.readToEndAlloc(allocator, 10 * 1024 * 1024); // 10MB max
    defer allocator.free(content);

    // Initialize prover client
    var client = prover.ProverClient.init(allocator, endpoint);

    // Verify
    const result = client.verifyProof(prover_kind, content, file_path) catch |err| {
        return VerificationResult{
            .status = .err,
            .prover_used = prover_kind,
            .duration_ms = 0,
            .message = switch (err) {
                prover.Error.ProverNotFound => "Prover not found - is it installed?",
                prover.Error.Timeout => "Verification timed out",
                prover.Error.SubprocessFailed => "Prover subprocess failed",
                else => "Verification failed",
            },
        };
    };

    return VerificationResult{
        .status = result.status,
        .prover_used = prover_kind,
        .duration_ms = result.duration_ms,
        .message = result.message,
    };
}

/// Verify all proofs in a directory
pub fn verifyProofDirectory(
    allocator: std.mem.Allocator,
    dir_path: []const u8,
    endpoint: []const u8,
) !struct { passed: u32, failed: u32, skipped: u32 } {
    var passed: u32 = 0;
    var failed: u32 = 0;
    var skipped: u32 = 0;

    var dir = try std.fs.cwd().openDir(dir_path, .{ .iterate = true });
    defer dir.close();

    var iter = dir.iterate();
    while (try iter.next()) |entry| {
        if (entry.kind != .file) continue;

        // Check if it's a proof file
        const ext = std.fs.path.extension(entry.name);
        if (prover.ProverKind.fromExtension(ext) == null) {
            skipped += 1;
            continue;
        }

        // Build full path
        var path_buf: [std.fs.max_path_bytes]u8 = undefined;
        const full_path = try std.fmt.bufPrint(&path_buf, "{s}/{s}", .{ dir_path, entry.name });

        const result = verifyProofFile(allocator, full_path, endpoint) catch {
            failed += 1;
            continue;
        };

        if (result.isVerified()) {
            passed += 1;
        } else {
            failed += 1;
        }
    }

    return .{ .passed = passed, .failed = failed, .skipped = skipped };
}

/// Valence-specific: Check if filesystem operation has valid proof backing
pub const ProofBackingCheck = struct {
    /// Operation types that require proof backing
    pub const Operation = enum {
        mkdir,
        rmdir,
        create_file,
        delete_file,

        pub fn proofFile(self: Operation, prover_system: []const u8) []const u8 {
            return switch (self) {
                .mkdir, .rmdir => switch (prover_system[0]) {
                    'c' => "proofs/coq/filesystem_model.v",
                    'l' => "proofs/lean4/FilesystemModel.lean",
                    'a' => "proofs/agda/FilesystemModel.agda",
                    'i' => "proofs/isabelle/FilesystemModel.thy",
                    'm' => "proofs/mizar/filesystem_model.miz",
                    'z' => "proofs/z3/filesystem_operations.smt2",
                    else => "proofs/coq/filesystem_model.v",
                },
                .create_file, .delete_file => switch (prover_system[0]) {
                    'c' => "proofs/coq/file_operations.v",
                    'l' => "proofs/lean4/FileOperations.lean",
                    'a' => "proofs/agda/FileOperations.agda",
                    'i' => "proofs/isabelle/FileOperations.thy",
                    'm' => "proofs/mizar/file_operations.miz",
                    'z' => "proofs/z3/filesystem_operations.smt2",
                    else => "proofs/coq/file_operations.v",
                },
            };
        }
    };

    /// Verify that the proof backing for an operation is valid
    pub fn checkProofBacking(
        allocator: std.mem.Allocator,
        operation: Operation,
        prover_system: []const u8,
        endpoint: []const u8,
    ) !bool {
        const proof_file = operation.proofFile(prover_system);
        const result = try verifyProofFile(allocator, proof_file, endpoint);
        return result.isVerified();
    }
};

// =============================================================================
// Main - CLI tool for proof verification
// =============================================================================

pub fn main() !void {
    const allocator = std.heap.page_allocator;

    const args = try std.process.argsAlloc(allocator);
    defer std.process.argsFree(allocator, args);

    if (args.len < 2) {
        std.debug.print(
            \\Valence Shell - Prover Integration
            \\
            \\Usage:
            \\  prover_test <proof-file>           Verify a single proof file
            \\  prover_test --dir <directory>      Verify all proofs in directory
            \\  prover_test --check <operation>    Check proof backing for operation
            \\
            \\Supported provers (12 total):
            \\  Tier 1: Agda (.agda), Coq (.v), Lean (.lean), Isabelle (.thy), Z3 (.smt2), CVC5
            \\  Tier 2: Metamath (.mm), HOL Light (.ml), Mizar (.miz)
            \\  Tier 3: PVS (.pvs), ACL2 (.lisp), HOL4 (.sml)
            \\
            \\Examples:
            \\  prover_test proofs/coq/filesystem_model.v
            \\  prover_test --dir proofs/lean4
            \\  prover_test --check mkdir
            \\
        , .{});
        return;
    }

    const endpoint = "http://localhost:8080/graphql"; // ECHIDNA Core endpoint

    if (std.mem.eql(u8, args[1], "--dir")) {
        if (args.len < 3) {
            std.debug.print("Error: --dir requires a directory path\n", .{});
            return;
        }
        const result = try verifyProofDirectory(allocator, args[2], endpoint);
        std.debug.print(
            \\Directory verification complete:
            \\  Passed:  {d}
            \\  Failed:  {d}
            \\  Skipped: {d}
            \\
        , .{ result.passed, result.failed, result.skipped });
    } else if (std.mem.eql(u8, args[1], "--check")) {
        if (args.len < 3) {
            std.debug.print("Error: --check requires an operation name\n", .{});
            return;
        }
        const op = std.meta.stringToEnum(ProofBackingCheck.Operation, args[2]) orelse {
            std.debug.print("Error: Unknown operation '{s}'\n", .{args[2]});
            return;
        };
        const has_backing = try ProofBackingCheck.checkProofBacking(allocator, op, "coq", endpoint);
        std.debug.print("Operation '{s}' proof backing: {s}\n", .{
            args[2],
            if (has_backing) "VERIFIED" else "NOT VERIFIED",
        });
    } else {
        // Single file verification
        const result = try verifyProofFile(allocator, args[1], endpoint);
        std.debug.print(
            \\Verification result:
            \\  File:     {s}
            \\  Prover:   {s}
            \\  Status:   {s}
            \\  Duration: {d}ms
            \\  Message:  {s}
            \\
        , .{
            args[1],
            result.prover_used.displayName(),
            @tagName(result.status),
            result.duration_ms,
            result.message,
        });
    }
}

// =============================================================================
// Tests
// =============================================================================

test "prover kind detection" {
    try std.testing.expectEqual(prover.ProverKind.coq, prover.ProverKind.fromExtension(".v").?);
    try std.testing.expectEqual(prover.ProverKind.lean, prover.ProverKind.fromExtension(".lean").?);
    try std.testing.expectEqual(prover.ProverKind.agda, prover.ProverKind.fromExtension(".agda").?);
    try std.testing.expectEqual(prover.ProverKind.isabelle, prover.ProverKind.fromExtension(".thy").?);
    try std.testing.expectEqual(prover.ProverKind.z3, prover.ProverKind.fromExtension(".smt2").?);
    try std.testing.expectEqual(prover.ProverKind.mizar, prover.ProverKind.fromExtension(".miz").?);
}

test "prover tiers" {
    try std.testing.expectEqual(@as(u8, 1), prover.ProverKind.coq.tier());
    try std.testing.expectEqual(@as(u8, 1), prover.ProverKind.lean.tier());
    try std.testing.expectEqual(@as(u8, 2), prover.ProverKind.mizar.tier());
    try std.testing.expectEqual(@as(u8, 3), prover.ProverKind.pvs.tier());
}

test "proof backing file paths" {
    const mkdir_coq = ProofBackingCheck.Operation.mkdir.proofFile("coq");
    try std.testing.expectEqualStrings("proofs/coq/filesystem_model.v", mkdir_coq);

    const create_lean = ProofBackingCheck.Operation.create_file.proofFile("lean4");
    try std.testing.expectEqualStrings("proofs/lean4/FileOperations.lean", create_lean);
}
