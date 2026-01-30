// SPDX-License-Identifier: PLMP-1.0-or-later
//! Valence Shell - Zig Build with Lean 4 Integration
//!
//! This is an enhanced build configuration that optionally links against
//! Lean 4 verified code for formal precondition checking.
//!
//! Build options:
//!   -Dlean-verified=true   Enable Lean 4 verification (requires Lean runtime)
//!   -Dlean-verified=false  Use manual precondition checking (default)
//!
//! Usage:
//!   zig build                        # Manual preconditions
//!   zig build -Dlean-verified=true   # Lean-verified preconditions

const std = @import("std");

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});

    // Build option: Enable Lean verification
    const lean_verified = b.option(bool, "lean-verified", "Use Lean 4 verified preconditions") orelse false;

    // Main executable - vsh fast path
    const exe = b.addExecutable(.{
        .name = "vsh",
        .root_module = b.createModule(.{
            .root_source_file = b.path("src/main.zig"),
        }),
        .target = target,
        .optimize = optimize,
    });

    // Link libc for POSIX syscalls
    exe.linkLibC();

    // If Lean verification enabled, link against Lean runtime and wrapper
    if (lean_verified) {
        // Get Lean installation prefix
        const lean_prefix = getLeanPrefix(b) catch |err| {
            std.log.err("Failed to get Lean prefix: {}", .{err});
            std.log.err("Is Lean 4 installed? Run: curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh", .{});
            @panic("Lean 4 not found");
        };

        // Add Lean include path
        const lean_include = b.pathJoin(&.{ lean_prefix, "include" });
        exe.addIncludePath(.{ .cwd_relative = lean_include });

        // Add Lean library path
        const lean_lib = b.pathJoin(&.{ lean_prefix, "lib", "lean" });
        exe.addLibraryPath(.{ .cwd_relative = lean_lib });

        // Link Lean shared library
        exe.linkSystemLibrary("leanshared");

        // Link our C wrapper (lean_wrapper.c -> liblean_vsh.so)
        const wrapper_lib_path = "../ocaml/liblean_vsh.so";
        if (std.fs.cwd().access(wrapper_lib_path, .{})) {
            exe.addLibraryPath(.{ .cwd_relative = "../ocaml" });
            exe.linkSystemLibrary("lean_vsh");
        } else |_| {
            std.log.warn("Lean wrapper library not found at {s}", .{wrapper_lib_path});
            std.log.warn("Build it with: cd ../ocaml && make lean_wrapper", .{});
            std.log.warn("Falling back to manual preconditions", .{});
        }

        // Add build option to code
        const options = b.addOptions();
        options.addOption(bool, "lean_verified", true);
        exe.root_module.addOptions("build_options", options);

        std.log.info("Building with Lean 4 verification enabled", .{});
    } else {
        // Manual preconditions
        const options = b.addOptions();
        options.addOption(bool, "lean_verified", false);
        exe.root_module.addOptions("build_options", options);

        std.log.info("Building with manual preconditions (use -Dlean-verified=true for verification)", .{});
    }

    b.installArtifact(exe);

    // Shared library - C FFI/ABI for language bindings
    const lib = b.addSharedLibrary(.{
        .name = "valence_ffi",
        .root_module = b.createModule(.{
            .root_source_file = b.path("src/lib.zig"),
        }),
        .target = target,
        .optimize = optimize,
        .version = .{ .major = 0, .minor = 1, .patch = 0 },
    });

    lib.linkLibC();

    // Link Lean for shared library if enabled
    if (lean_verified) {
        const lean_prefix = getLeanPrefix(b) catch unreachable;
        const lean_include = b.pathJoin(&.{ lean_prefix, "include" });
        const lean_lib = b.pathJoin(&.{ lean_prefix, "lib", "lean" });

        lib.addIncludePath(.{ .cwd_relative = lean_include });
        lib.addLibraryPath(.{ .cwd_relative = lean_lib });
        lib.linkSystemLibrary("leanshared");

        const options = b.addOptions();
        options.addOption(bool, "lean_verified", true);
        lib.root_module.addOptions("build_options", options);
    } else {
        const options = b.addOptions();
        options.addOption(bool, "lean_verified", false);
        lib.root_module.addOptions("build_options", options);
    }

    b.installArtifact(lib);

    // Static library variant
    const lib_static = b.addStaticLibrary(.{
        .name = "valence_ffi",
        .root_module = b.createModule(.{
            .root_source_file = b.path("src/lib.zig"),
        }),
        .target = target,
        .optimize = optimize,
    });

    lib_static.linkLibC();
    b.installArtifact(lib_static);

    // Run command
    const run_cmd = b.addRunArtifact(exe);
    run_cmd.step.dependOn(b.getInstallStep());

    if (b.args) |args| {
        run_cmd.addArgs(args);
    }

    const run_step = b.step("run", "Run the vsh fast path");
    run_step.dependOn(&run_cmd.step);

    // Unit tests
    const unit_tests = b.addTest(.{
        .root_module = b.createModule(.{
            .root_source_file = b.path("src/main.zig"),
        }),
        .target = target,
        .optimize = optimize,
    });

    const run_unit_tests = b.addRunArtifact(unit_tests);
    const test_step = b.step("test", "Run unit tests");
    test_step.dependOn(&run_unit_tests.step);

    // Lean bindings tests (only if Lean enabled)
    if (lean_verified) {
        const lean_tests = b.addTest(.{
            .root_module = b.createModule(.{
                .root_source_file = b.path("src/lean_bindings.zig"),
            }),
            .target = target,
            .optimize = optimize,
        });

        lean_tests.linkLibC();

        const lean_prefix = getLeanPrefix(b) catch unreachable;
        const lean_include = b.pathJoin(&.{ lean_prefix, "include" });
        const lean_lib = b.pathJoin(&.{ lean_prefix, "lib", "lean" });

        lean_tests.addIncludePath(.{ .cwd_relative = lean_include });
        lean_tests.addLibraryPath(.{ .cwd_relative = lean_lib });
        lean_tests.linkSystemLibrary("leanshared");

        const run_lean_tests = b.addRunArtifact(lean_tests);

        const lean_test_step = b.step("test-lean", "Run Lean integration tests");
        lean_test_step.dependOn(&run_lean_tests.step);
    }
}

/// Get Lean installation prefix by running `lean --print-prefix`
fn getLeanPrefix(b: *std.Build) ![]const u8 {
    const result = try std.process.Child.run(.{
        .allocator = b.allocator,
        .argv = &[_][]const u8{ "lean", "--print-prefix" },
    });

    if (result.term.Exited != 0) {
        return error.LeanNotFound;
    }

    // Trim trailing newline
    const prefix = std.mem.trim(u8, result.stdout, &std.ascii.whitespace);
    return b.allocator.dupe(u8, prefix);
}
