// SPDX-License-Identifier: PLMP-1.0-or-later
//! Daemon Client - Unix Socket Communication
//!
//! JSON-RPC 2.0 client for communicating with the BEAM daemon.
//! Handles complex operations: undo, redo, history, obliterate, cp, mv

const std = @import("std");
const fs = std.fs;
const mem = std.mem;
const posix = std.posix;

/// Default daemon socket path
pub const SOCKET_PATH = "/tmp/vsh-daemon.sock";

/// Check if daemon is running by testing socket accessibility
pub fn isDaemonRunning() bool {
    // Check if socket file exists
    fs.cwd().access(SOCKET_PATH, .{}) catch {
        return false;
    };

    // Try to connect to verify daemon is actually listening
    const socket_fd = posix.socket(posix.AF.UNIX, posix.SOCK.STREAM, 0) catch {
        return false;
    };
    defer posix.close(socket_fd);

    var addr: posix.sockaddr.un = undefined;
    addr.family = posix.AF.UNIX;

    // Copy socket path
    const path_bytes = SOCKET_PATH;
    @memcpy(addr.path[0..path_bytes.len], path_bytes);
    addr.path[path_bytes.len] = 0;

    // Try to connect
    posix.connect(socket_fd, @ptrCast(&addr), @sizeOf(posix.sockaddr.un)) catch {
        return false;
    };

    return true;
}

/// Print daemon not running message
pub fn printDaemonNotRunning(cmd: []const u8) !void {
    const stderr = std.io.getStdErr().writer();
    try stderr.print(
        \\vsh: '{s}' requires BEAM daemon
        \\
        \\The VSH daemon provides:
        \\  - Undo/redo functionality
        \\  - Operation history
        \\  - Transaction support
        \\  - Secure deletion (obliterate)
        \\
        \\Start the daemon:
        \\  cd impl/elixir && mix vsh.daemon start
        \\
        \\Or run in foreground:
        \\  cd impl/elixir && iex -S mix
        \\  iex> VSH.Daemon.start_link()
        \\
    , .{cmd});
}

/// Send a simple request to the daemon and get response
/// Returns true on success, false on failure
pub fn sendSimpleRequest(
    allocator: mem.Allocator,
    method: []const u8,
    path: ?[]const u8,
) !bool {
    _ = allocator;

    const socket_fd = posix.socket(posix.AF.UNIX, posix.SOCK.STREAM, 0) catch {
        return false;
    };
    defer posix.close(socket_fd);

    var addr: posix.sockaddr.un = undefined;
    addr.family = posix.AF.UNIX;
    const path_bytes = SOCKET_PATH;
    @memcpy(addr.path[0..path_bytes.len], path_bytes);
    addr.path[path_bytes.len] = 0;

    posix.connect(socket_fd, @ptrCast(&addr), @sizeOf(posix.sockaddr.un)) catch {
        return false;
    };

    // Build simple JSON-RPC request
    var buf: [4096]u8 = undefined;
    var fbs = std.io.fixedBufferStream(&buf);
    const writer = fbs.writer();

    if (path) |p| {
        try writer.print(
            \\{{"jsonrpc":"2.0","method":"{s}","params":{{"path":"{s}"}},"id":1}}
            \\
        , .{ method, p });
    } else {
        try writer.print(
            \\{{"jsonrpc":"2.0","method":"{s}","params":{{}},"id":1}}
            \\
        , .{method});
    }

    const request = fbs.getWritten();

    // Send request
    _ = posix.write(socket_fd, request) catch {
        return false;
    };

    // Read response
    var response_buf: [65536]u8 = undefined;
    const bytes_read = posix.read(socket_fd, &response_buf) catch {
        return false;
    };

    if (bytes_read == 0) {
        return false;
    }

    // Check for success (simple check for "result" in response)
    const response = response_buf[0..bytes_read];
    return mem.indexOf(u8, response, "\"result\"") != null;
}

// Tests
test "isDaemonRunning returns value without crashing" {
    // This test just ensures the function doesn't crash
    const running = isDaemonRunning();
    _ = running;
}
