// SPDX-License-Identifier: PLMP-1.0-or-later
//! Valence Shell - Audit Logging for MAA Framework
//!
//! Implements the Mutually Assured Accountability audit trail.
//! Every filesystem operation is logged with:
//! - Timestamp
//! - Operation type
//! - Path
//! - Result (success/failure with error code)
//! - Proof reference (which Coq theorem guarantees this op)
//!
//! This creates an accountable, auditable record that can be
//! used for GDPR compliance and forensic analysis.

const std = @import("std");
const Allocator = std.mem.Allocator;
const lib = @import("lib.zig");
const PosixError = lib.PosixError;

/// Operation types matching Coq definitions
pub const OperationType = enum {
    mkdir,
    rmdir,
    create_file,
    delete_file,
    write_file,
    read_file,

    /// Get the Coq theorem that proves this operation's reversibility
    pub fn proofReference(self: OperationType) []const u8 {
        return switch (self) {
            .mkdir => "mkdir_rmdir_reversible (filesystem_model.v:L45)",
            .rmdir => "mkdir_rmdir_reversible (filesystem_model.v:L45)",
            .create_file => "create_delete_file_reversible (file_operations.v:L32)",
            .delete_file => "create_delete_file_reversible (file_operations.v:L32)",
            .write_file => "write_file_reversible (file_content_operations.v:L67)",
            .read_file => "read_only_no_mutation (file_content_operations.v:L12)",
        };
    }

    /// Get the inverse operation (for reversibility)
    pub fn inverse(self: OperationType) ?OperationType {
        return switch (self) {
            .mkdir => .rmdir,
            .rmdir => .mkdir,
            .create_file => .delete_file,
            .delete_file => .create_file,
            .write_file => .write_file, // self-inverse with old content
            .read_file => null, // no inverse needed
        };
    }
};

/// Operation status
pub const OperationStatus = union(enum) {
    pending,
    succeeded,
    failed: PosixError,
};

/// Single audit log entry
pub const AuditEntry = struct {
    /// Unique operation ID
    id: u64,

    /// Timestamp (nanoseconds since epoch)
    timestamp: i128,

    /// Type of operation
    operation: OperationType,

    /// Path operated on
    path: []const u8,

    /// Result of operation
    status: OperationStatus,

    /// Reference to proving theorem
    proof_ref: []const u8,

    /// For reversible ops: the inverse operation ID (if executed)
    inverse_id: ?u64,
};

/// Audit log - append-only operation record
pub const AuditLog = struct {
    allocator: Allocator,

    /// Log entries (append-only for integrity)
    entries: std.ArrayList(AuditEntry),

    /// Next operation ID
    next_id: u64,

    /// Optional file backing for persistence
    backing_file: ?std.fs.File,

    const Self = @This();

    /// Create a new audit log
    pub fn init(allocator: Allocator, backing_path: ?[]const u8) !Self {
        var log = Self{
            .allocator = allocator,
            .entries = .empty,
            .next_id = 1,
            .backing_file = null,
        };

        if (backing_path) |path| {
            log.backing_file = try std.fs.createFileAbsolute(path, .{
                .truncate = false,
            });

            // Write header
            const header = "# Valence Shell Audit Log\n# Format: ID|TIMESTAMP|OP|PATH|STATUS|PROOF\n";
            _ = try log.backing_file.?.write(header);
        }

        return log;
    }

    /// Clean up resources
    pub fn deinit(self: *Self) void {
        if (self.backing_file) |*f| {
            f.close();
        }
        self.entries.deinit(self.allocator);
    }

    /// Log an operation
    pub fn logOperation(
        self: *Self,
        operation: OperationType,
        path: []const u8,
        status: OperationStatus,
    ) void {
        const entry = AuditEntry{
            .id = self.next_id,
            .timestamp = std.time.nanoTimestamp(),
            .operation = operation,
            .path = path,
            .status = status,
            .proof_ref = operation.proofReference(),
            .inverse_id = null,
        };

        self.entries.append(self.allocator, entry) catch return;
        self.next_id += 1;

        // Write to backing file if present
        if (self.backing_file) |*f| {
            const status_str = switch (status) {
                .pending => "PENDING",
                .succeeded => "OK",
                .failed => |e| @tagName(e),
            };

            // Format log entry to buffer
            var buf: [512]u8 = undefined;
            const line = std.fmt.bufPrint(&buf, "{d}|{d}|{s}|{s}|{s}|{s}\n", .{
                entry.id,
                entry.timestamp,
                @tagName(operation),
                path,
                status_str,
                entry.proof_ref,
            }) catch return;
            _ = f.write(line) catch {};
        }
    }

    /// Get the last operation ID
    pub fn getLastOperationId(self: *const Self) u64 {
        if (self.next_id > 1) {
            return self.next_id - 1;
        }
        return 0;
    }

    /// Get entry by ID
    pub fn getEntry(self: *const Self, id: u64) ?AuditEntry {
        for (self.entries.items) |entry| {
            if (entry.id == id) {
                return entry;
            }
        }
        return null;
    }

    /// Link operation to its inverse (for undo tracking)
    pub fn linkInverse(self: *Self, original_id: u64, inverse_id: u64) void {
        for (self.entries.items, 0..) |entry, i| {
            if (entry.id == original_id) {
                self.entries.items[i].inverse_id = inverse_id;
                return;
            }
        }
    }

    /// Get all operations that can be undone (succeeded, has inverse, not yet undone)
    pub fn getUndoableOperations(self: *const Self) []const AuditEntry {
        var result: std.ArrayList(AuditEntry) = .empty;

        for (self.entries.items) |entry| {
            if (entry.status == .succeeded and
                entry.operation.inverse() != null and
                entry.inverse_id == null)
            {
                result.append(self.allocator, entry) catch continue;
            }
        }

        return result.toOwnedSlice(self.allocator) catch &[_]AuditEntry{};
    }

    /// Generate human-readable audit report
    pub fn generateReport(self: *const Self, writer: anytype) !void {
        try writer.print("=== Valence Shell Audit Report ===\n\n", .{});
        try writer.print("Total operations: {d}\n\n", .{self.entries.items.len});

        for (self.entries.items) |entry| {
            const status_str = switch (entry.status) {
                .pending => "PENDING",
                .succeeded => "OK",
                .failed => |e| @tagName(e),
            };

            try writer.print(
                "[{d}] {s} {s} -> {s}\n",
                .{ entry.id, @tagName(entry.operation), entry.path, status_str },
            );
            try writer.print("    Proof: {s}\n", .{entry.proof_ref});

            if (entry.inverse_id) |inv_id| {
                try writer.print("    Undone by: {d}\n", .{inv_id});
            }
        }
    }
};

/// Structured audit format for external consumption (JSON-compatible)
pub const AuditRecord = struct {
    version: []const u8 = "1.0",
    operation_id: u64,
    timestamp_ns: i128,
    operation_type: []const u8,
    path: []const u8,
    success: bool,
    error_code: ?i32,
    proof_theorem: []const u8,
    proof_file: []const u8,
    reversible: bool,
    inverse_operation: ?[]const u8,
};

// =========================================================
// Tests
// =========================================================

test "audit_log_basic" {
    const allocator = std.testing.allocator;

    var log = try AuditLog.init(allocator, null);
    defer log.deinit();

    log.logOperation(.mkdir, "/test/path", .succeeded);

    try std.testing.expect(log.entries.items.len == 1);
    try std.testing.expect(log.entries.items[0].operation == .mkdir);
    try std.testing.expect(log.entries.items[0].status == .succeeded);
}

test "audit_log_proof_reference" {
    try std.testing.expectEqualStrings(
        "mkdir_rmdir_reversible (filesystem_model.v:L45)",
        OperationType.mkdir.proofReference(),
    );
}

test "audit_log_inverse" {
    try std.testing.expect(OperationType.mkdir.inverse() == .rmdir);
    try std.testing.expect(OperationType.rmdir.inverse() == .mkdir);
    try std.testing.expect(OperationType.read_file.inverse() == null);
}
