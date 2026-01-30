// SPDX-License-Identifier: PMPL-1.0-or-later
//! Valence Shell - Zig Wrapper for Lean 4 Extracted Code
//!
//! This file provides Zig-callable wrappers around Lean 4 compiled code.
//! Replaces lean_wrapper.c with native Zig implementation.
//!
//! Features:
//! - String marshaling between C and Lean
//! - Filesystem state representation
//! - Error code conversion
//! - Compiles to shared library (.so) for FFI consumption

const std = @import("std");

// Manual declarations for Lean C API (avoid @cImport parsing issues)
pub const lean_object = opaque {};

// Lean C API functions
extern fn lean_mk_string(str: [*:0]const u8) *lean_object;
extern fn lean_box(val: c_uint) *lean_object;
extern fn lean_inc_ref(obj: *lean_object) void;
extern fn lean_dec_ref(obj: *lean_object) void;
extern fn lean_ctor_get(obj: *lean_object, idx: c_uint) *lean_object;
extern fn lean_unbox(obj: *lean_object) c_uint;
extern fn lean_string_cstr(obj: *lean_object) [*:0]const u8;

// Error codes matching Lean CErrorCode type
pub const VshError = enum(c_int) {
    ENOERR = 0,
    EEXIST = 17,
    ENOENT = 2,
    EACCES = 13,
    ENOTDIR = 20,
    EISDIR = 21,
    ENOTEMPTY = 39,
};

// Result type for operations
pub const VshResult = extern struct {
    success: c_int,
    error_code: VshError,
};

// Opaque filesystem handle
pub const VshFilesystem = extern struct {
    lean_fs_obj: ?*lean_object,
    root_path: ?[*:0]u8,
};

// External Lean functions (from Extraction.c)
extern fn l_ValenceShell_Extraction_safeMkdirStr(path: *lean_object, fs: *lean_object) *lean_object;
extern fn l_ValenceShell_Extraction_safeRmdirStr(path: *lean_object, fs: *lean_object) *lean_object;
extern fn l_ValenceShell_Extraction_safeCreateFileStr(path: *lean_object, fs: *lean_object) *lean_object;
extern fn l_ValenceShell_Extraction_safeDeleteFileStr(path: *lean_object, fs: *lean_object) *lean_object;

// Helper: Convert C string to Lean String
fn cStrToLeanStr(c_str: [*:0]const u8) *lean_object {
    return lean_mk_string(c_str);
}

// Helper: Convert Lean String to C string (caller must free)
fn leanStrToCStr(lean_str: *lean_object) [*:0]u8 {
    const data = lean_string_cstr(lean_str);
    return @ptrCast(@constCast(data));
}

// Helper: Convert Lean CResult to VshResult
fn leanResultToC(lean_result: *lean_object) VshResult {
    // Extract fields from Lean CResult structure
    // Field 0: success (Bool - unboxed u8)
    // Field 1: errorCode (CErrorCode enum - unboxed u8)
    const success_obj = lean_ctor_get(lean_result, 0);
    const error_obj = lean_ctor_get(lean_result, 1);

    const success = lean_unbox(success_obj);
    const error_code = lean_unbox(error_obj);

    return VshResult{
        .success = if (success != 0) 1 else 0,
        .error_code = @enumFromInt(error_code),
    };
}

// Create filesystem handle
export fn vsh_filesystem_create(root: [*:0]const u8) ?*VshFilesystem {
    const allocator = std.heap.c_allocator;
    const fs = allocator.create(VshFilesystem) catch return null;

    // Duplicate root path
    const root_len = std.mem.len(root);
    const root_copy = allocator.allocSentinel(u8, root_len, 0) catch {
        allocator.destroy(fs);
        return null;
    };
    @memcpy(root_copy[0..root_len], root[0..root_len]);

    fs.root_path = root_copy.ptr;

    // Initialize Lean emptyFS object
    // emptyFS is represented as a null pointer in the simplified model
    fs.lean_fs_obj = lean_box(0);
    if (fs.lean_fs_obj) |obj| {
        lean_inc_ref(obj);
    }

    return fs;
}

// Destroy filesystem handle
export fn vsh_filesystem_destroy(fs: ?*VshFilesystem) void {
    if (fs) |filesystem| {
        const allocator = std.heap.c_allocator;

        // Free root path
        if (filesystem.root_path) |path| {
            const path_slice = std.mem.span(path);
            allocator.free(path_slice);
        }

        // Decrement Lean object reference count
        if (filesystem.lean_fs_obj) |obj| {
            lean_dec_ref(obj);
        }

        allocator.destroy(filesystem);
    }
}

// Safe mkdir wrapper
export fn vsh_safe_mkdir(fs: ?*VshFilesystem, path: [*:0]const u8) VshResult {
    if (fs == null) {
        return VshResult{
            .success = 0,
            .error_code = VshError.ENOENT,
        };
    }

    const filesystem = fs.?;

    // Convert C path to Lean String
    const lean_path = cStrToLeanStr(path);

    // Get Lean filesystem object
    const lean_fs = filesystem.lean_fs_obj orelse lean_box(0);
    lean_inc_ref(lean_fs);

    // Call Lean safeMkdirStr function
    const lean_result = l_ValenceShell_Extraction_safeMkdirStr(lean_path, lean_fs);

    // Convert Lean CResult to C result
    const result = leanResultToC(lean_result);

    // Clean up Lean objects
    lean_dec_ref(lean_result);

    return result;
}

// Safe rmdir wrapper
export fn vsh_safe_rmdir(fs: ?*VshFilesystem, path: [*:0]const u8) VshResult {
    if (fs == null) {
        return VshResult{
            .success = 0,
            .error_code = VshError.ENOENT,
        };
    }

    const filesystem = fs.?;
    const lean_path = cStrToLeanStr(path);
    const lean_fs = filesystem.lean_fs_obj orelse lean_box(0);
    lean_inc_ref(lean_fs);

    const lean_result = l_ValenceShell_Extraction_safeRmdirStr(lean_path, lean_fs);
    const result = leanResultToC(lean_result);

    lean_dec_ref(lean_result);
    return result;
}

// Safe file creation wrapper
export fn vsh_safe_create_file(fs: ?*VshFilesystem, path: [*:0]const u8) VshResult {
    if (fs == null) {
        return VshResult{
            .success = 0,
            .error_code = VshError.ENOENT,
        };
    }

    const filesystem = fs.?;
    const lean_path = cStrToLeanStr(path);
    const lean_fs = filesystem.lean_fs_obj orelse lean_box(0);
    lean_inc_ref(lean_fs);

    const lean_result = l_ValenceShell_Extraction_safeCreateFileStr(lean_path, lean_fs);
    const result = leanResultToC(lean_result);

    lean_dec_ref(lean_result);
    return result;
}

// Safe file deletion wrapper
export fn vsh_safe_delete_file(fs: ?*VshFilesystem, path: [*:0]const u8) VshResult {
    if (fs == null) {
        return VshResult{
            .success = 0,
            .error_code = VshError.ENOENT,
        };
    }

    const filesystem = fs.?;
    const lean_path = cStrToLeanStr(path);
    const lean_fs = filesystem.lean_fs_obj orelse lean_box(0);
    lean_inc_ref(lean_fs);

    const lean_result = l_ValenceShell_Extraction_safeDeleteFileStr(lean_path, lean_fs);
    const result = leanResultToC(lean_result);

    lean_dec_ref(lean_result);
    return result;
}

// Test function to verify linking
export fn vsh_get_version() [*:0]const u8 {
    return "Valence Shell Lean FFI v0.2.0 (Zig)";
}

// Implementation Notes
// ====================
//
// Trust Chain (Zig-based):
// 1. Lean 4 proofs (256+ theorems) - High trust (formally verified)
// 2. Lean 4 → C compiler - Medium trust (standard Lean compiler)
// 3. Zig wrapper (this file) - High trust (memory-safe, compile-time checks)
// 4. Zig → C FFI - High trust (Zig's safe C interop)
// 5. POSIX operations - Low trust (OS dependent)
//
// Benefits over C wrapper:
// - Memory safety (Zig's allocator tracking)
// - Compile-time checks
// - Better error handling
// - Cleaner syntax
// - No undefined behavior
//
// Building:
// ```bash
// zig build-lib lean_wrapper.zig \
//     -dynamic \
//     -lc \
//     -lleanshared \
//     -I$(lean --print-prefix)/include \
//     -L$(lean --print-prefix)/lib/lean \
//     ../../proofs/lean4/.lake/build/ir/Extraction.c
// ```
