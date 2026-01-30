// SPDX-License-Identifier: PMPL-1.0-or-later
//! Build script for Lean FFI Zig wrapper

const std = @import("std");

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});

    // Get Lean installation path
    const lean_prefix_result = std.process.Child.run(.{
        .allocator = b.allocator,
        .argv = &[_][]const u8{ "lean", "--print-prefix" },
    }) catch @panic("Failed to run 'lean --print-prefix' - is Lean 4 installed?");

    const lean_prefix = std.mem.trim(u8, lean_prefix_result.stdout, " \n\r\t");

    // Build shared library
    const lib = b.addSharedLibrary(.{
        .name = "lean_vsh",
        .root_source_file = b.path("lean_wrapper.zig"),
        .target = target,
        .optimize = optimize,
    });

    // Add Lean include directory
    const lean_include = b.fmt("{s}/include", .{lean_prefix});
    lib.addIncludePath(.{ .cwd_relative = lean_include });

    // Add Lean library directory
    const lean_lib = b.fmt("{s}/lib/lean", .{lean_prefix});
    lib.addLibraryPath(.{ .cwd_relative = lean_lib });

    // Link against Lean runtime
    lib.linkSystemLibrary("leanshared");
    lib.linkLibC();

    // Link pre-compiled Lean module object files
    // (Compiled separately to avoid Zig parsing Lean C headers)
    const lean_modules = [_][]const u8{
        "Extraction.o",
        "FileOperations.o",
        "FilesystemComposition.o",
        "FilesystemModel.o",
    };
    for (lean_modules) |obj| {
        lib.addObjectFile(.{ .cwd_relative = obj });
    }

    // Set rpath for runtime library loading
    lib.addRPath(.{ .cwd_relative = lean_lib });

    // Install the library
    b.installArtifact(lib);

    // Create a test step
    const test_step = b.step("test", "Test the Zig wrapper");
    const lib_tests = b.addTest(.{
        .root_source_file = b.path("lean_wrapper.zig"),
        .target = target,
        .optimize = optimize,
    });
    lib_tests.addIncludePath(.{ .cwd_relative = lean_include });
    lib_tests.addLibraryPath(.{ .cwd_relative = lean_lib });
    lib_tests.linkSystemLibrary("leanshared");
    lib_tests.linkLibC();

    const run_lib_tests = b.addRunArtifact(lib_tests);
    test_step.dependOn(&run_lib_tests.step);
}
