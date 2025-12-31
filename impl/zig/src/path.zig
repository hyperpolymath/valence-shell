// SPDX-License-Identifier: AGPL-3.0-or-later
//! Valence Shell - Path Operations
//!
//! Path handling matching the Coq path model.
//!
//! In Coq: Path = list PathComponent
//! Here: We use []const u8 slices with / separators
//!
//! Security: This module handles path normalization to prevent
//! directory traversal attacks.

const std = @import("std");
const Allocator = std.mem.Allocator;

/// Path component (single directory/file name)
pub const PathComponent = []const u8;

/// Full path as list of components (matches Coq model)
pub const Path = struct {
    components: []PathComponent,
    allocator: Allocator,

    const Self = @This();

    /// Parse a string path into components
    pub fn fromString(allocator: Allocator, path_str: []const u8) !Self {
        var components = std.ArrayList(PathComponent).init(allocator);

        var iter = std.mem.splitScalar(u8, path_str, '/');
        while (iter.next()) |component| {
            if (component.len > 0) {
                try components.append(component);
            }
        }

        return .{
            .components = try components.toOwnedSlice(),
            .allocator = allocator,
        };
    }

    /// Convert back to string
    pub fn toString(self: *const Self, allocator: Allocator) ![]const u8 {
        if (self.components.len == 0) {
            return try allocator.dupe(u8, "/");
        }

        var result = std.ArrayList(u8).init(allocator);
        for (self.components) |comp| {
            try result.append('/');
            try result.appendSlice(comp);
        }

        return try result.toOwnedSlice();
    }

    /// Get parent path (matches Coq parent_path function)
    pub fn parent(self: *const Self) ?Self {
        if (self.components.len <= 1) {
            return null;
        }

        return .{
            .components = self.components[0 .. self.components.len - 1],
            .allocator = self.allocator,
        };
    }

    /// Get the final component (filename/dirname)
    pub fn basename(self: *const Self) ?PathComponent {
        if (self.components.len == 0) {
            return null;
        }
        return self.components[self.components.len - 1];
    }

    /// Check if this is the root path
    pub fn isRoot(self: *const Self) bool {
        return self.components.len == 0;
    }

    /// Check if path contains dangerous components
    pub fn containsTraversal(self: *const Self) bool {
        for (self.components) |comp| {
            if (std.mem.eql(u8, comp, "..") or std.mem.eql(u8, comp, ".")) {
                return true;
            }
        }
        return false;
    }

    pub fn deinit(self: *Self) void {
        self.allocator.free(self.components);
    }
};

/// Normalize a path string (resolve . and .., remove double slashes)
pub fn normalizePath(allocator: Allocator, path_str: []const u8) ![]const u8 {
    var components = std.ArrayList([]const u8).init(allocator);
    defer components.deinit();

    var iter = std.mem.splitScalar(u8, path_str, '/');
    while (iter.next()) |comp| {
        if (comp.len == 0 or std.mem.eql(u8, comp, ".")) {
            // Skip empty and current-dir references
            continue;
        } else if (std.mem.eql(u8, comp, "..")) {
            // Go up one level if possible
            if (components.items.len > 0) {
                _ = components.pop();
            }
        } else {
            try components.append(comp);
        }
    }

    // Rebuild path
    if (components.items.len == 0) {
        return try allocator.dupe(u8, "/");
    }

    var result = std.ArrayList(u8).init(allocator);
    for (components.items) |comp| {
        try result.append('/');
        try result.appendSlice(comp);
    }

    return try result.toOwnedSlice();
}

/// Join two paths safely
pub fn joinPaths(allocator: Allocator, base: []const u8, relative: []const u8) ![]const u8 {
    // If relative is absolute, use it directly
    if (relative.len > 0 and relative[0] == '/') {
        return try normalizePath(allocator, relative);
    }

    const combined = try std.fmt.allocPrint(allocator, "{s}/{s}", .{ base, relative });
    defer allocator.free(combined);

    return try normalizePath(allocator, combined);
}

/// Check if a path is within a given root (for sandboxing)
pub fn isWithinRoot(path: []const u8, root: []const u8) bool {
    // Both paths should be normalized first
    if (path.len < root.len) {
        return false;
    }

    // Check prefix match
    if (!std.mem.startsWith(u8, path, root)) {
        return false;
    }

    // Make sure we're not matching partial component names
    // e.g., /tmp/test should not match /tmp/testing
    if (path.len > root.len) {
        const next_char = path[root.len];
        if (next_char != '/') {
            return false;
        }
    }

    return true;
}

// =========================================================
// Tests
// =========================================================

test "path_from_string" {
    const allocator = std.testing.allocator;

    var path = try Path.fromString(allocator, "/home/user/test");
    defer path.deinit();

    try std.testing.expect(path.components.len == 3);
    try std.testing.expectEqualStrings("home", path.components[0]);
    try std.testing.expectEqualStrings("user", path.components[1]);
    try std.testing.expectEqualStrings("test", path.components[2]);
}

test "path_parent" {
    const allocator = std.testing.allocator;

    var path = try Path.fromString(allocator, "/home/user/test");
    defer path.deinit();

    const parent_opt = path.parent();
    try std.testing.expect(parent_opt != null);

    const par = parent_opt.?;
    try std.testing.expect(par.components.len == 2);
}

test "normalize_path" {
    const allocator = std.testing.allocator;

    const normalized = try normalizePath(allocator, "/home/user/../test/./file");
    defer allocator.free(normalized);

    try std.testing.expectEqualStrings("/home/test/file", normalized);
}

test "is_within_root" {
    try std.testing.expect(isWithinRoot("/tmp/vsh/test", "/tmp/vsh"));
    try std.testing.expect(isWithinRoot("/tmp/vsh", "/tmp/vsh"));
    try std.testing.expect(!isWithinRoot("/tmp/vsh_escape", "/tmp/vsh"));
    try std.testing.expect(!isWithinRoot("/etc/passwd", "/tmp/vsh"));
}
