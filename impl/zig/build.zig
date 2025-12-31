// SPDX-License-Identifier: AGPL-3.0-or-later
//! Valence Shell - Zig FFI Build Configuration
//!
//! Builds the formally-verified filesystem FFI layer.
//! This provides the bridge between Coq proofs and POSIX syscalls.

const std = @import("std");

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});

    // Main library - C ABI for integration with other runtimes
    const lib = b.addStaticLibrary(.{
        .name = "valence_ffi",
        .root_source_file = b.path("src/lib.zig"),
        .target = target,
        .optimize = optimize,
    });

    // Link libc for POSIX syscalls
    lib.linkLibC();

    // Export C headers
    lib.installHeader(b.path("src/valence_ffi.h"), "valence_ffi.h");

    b.installArtifact(lib);

    // Shared library for dynamic linking
    const shared_lib = b.addSharedLibrary(.{
        .name = "valence_ffi",
        .root_source_file = b.path("src/lib.zig"),
        .target = target,
        .optimize = optimize,
    });
    shared_lib.linkLibC();
    b.installArtifact(shared_lib);

    // Test executable
    const tests = b.addTest(.{
        .root_source_file = b.path("src/lib.zig"),
        .target = target,
        .optimize = optimize,
    });
    tests.linkLibC();

    const run_tests = b.addRunArtifact(tests);
    const test_step = b.step("test", "Run FFI tests");
    test_step.dependOn(&run_tests.step);

    // Demo executable
    const demo = b.addExecutable(.{
        .name = "vsh_demo",
        .root_source_file = b.path("src/demo.zig"),
        .target = target,
        .optimize = optimize,
    });
    demo.linkLibC();
    demo.root_module.addImport("valence", &lib.root_module);
    b.installArtifact(demo);

    const run_demo = b.addRunArtifact(demo);
    const demo_step = b.step("demo", "Run FFI demonstration");
    demo_step.dependOn(&run_demo.step);
}
