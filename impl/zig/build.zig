// SPDX-License-Identifier: AGPL-3.0-or-later
//! Valence Shell - Zig FFI Build Configuration
//!
//! Builds the formally-verified filesystem FFI layer with prover integration.
//! This provides the bridge between Coq proofs and POSIX syscalls,
//! plus runtime proof verification via zig-prover-ffi.

const std = @import("std");

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});

    // zig-prover-ffi dependency
    const prover_dep = b.dependency("zig_prover_ffi", .{
        .target = target,
        .optimize = optimize,
    });
    const prover_module = prover_dep.module("zig-prover-ffi");

    // Main library - C ABI for integration with other runtimes
    const lib = b.addLibrary(.{
        .name = "valence_ffi",
        .root_module = b.createModule(.{
            .root_source_file = b.path("src/lib.zig"),
            .target = target,
            .optimize = optimize,
            .imports = &.{
                .{ .name = "prover", .module = prover_module },
            },
        }),
        .linkage = .static,
    });
    lib.linkLibC();
    b.installArtifact(lib);

    // Shared library for dynamic linking
    const shared_lib = b.addLibrary(.{
        .name = "valence_ffi",
        .root_module = b.createModule(.{
            .root_source_file = b.path("src/lib.zig"),
            .target = target,
            .optimize = optimize,
            .imports = &.{
                .{ .name = "prover", .module = prover_module },
            },
        }),
        .linkage = .dynamic,
    });
    shared_lib.linkLibC();
    b.installArtifact(shared_lib);

    // Test executable
    const tests = b.addTest(.{
        .root_module = b.createModule(.{
            .root_source_file = b.path("src/lib.zig"),
            .target = target,
            .optimize = optimize,
            .imports = &.{
                .{ .name = "prover", .module = prover_module },
            },
        }),
    });
    tests.linkLibC();

    const run_tests = b.addRunArtifact(tests);
    const test_step = b.step("test", "Run FFI tests");
    test_step.dependOn(&run_tests.step);

    // Demo executable
    const demo = b.addExecutable(.{
        .name = "vsh_demo",
        .root_module = b.createModule(.{
            .root_source_file = b.path("src/demo.zig"),
            .target = target,
            .optimize = optimize,
            .imports = &.{
                .{ .name = "prover", .module = prover_module },
            },
        }),
    });
    demo.linkLibC();
    b.installArtifact(demo);

    const run_demo = b.addRunArtifact(demo);
    const demo_step = b.step("demo", "Run FFI demonstration");
    demo_step.dependOn(&run_demo.step);

    // Prover test executable
    const prover_test = b.addExecutable(.{
        .name = "prover_test",
        .root_module = b.createModule(.{
            .root_source_file = b.path("src/prover_integration.zig"),
            .target = target,
            .optimize = optimize,
            .imports = &.{
                .{ .name = "prover", .module = prover_module },
            },
        }),
    });
    prover_test.linkLibC();
    b.installArtifact(prover_test);

    const run_prover_test = b.addRunArtifact(prover_test);
    const prover_step = b.step("prover", "Run prover integration test");
    prover_step.dependOn(&run_prover_test.step);
}
