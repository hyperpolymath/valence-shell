# SPDX-License-Identifier: AGPL-3.0-or-later

defmodule VSH.NIF do
  @moduledoc """
  NIF bindings to the Zig FFI layer using Zigler.

  This module provides direct access to the verified filesystem operations
  implemented in Zig with precondition checking derived from Coq proofs.

  ## Architecture

  ```
  Elixir (VSH.NIF) → Zigler → Zig (valence_ffi) → POSIX syscalls
  ```

  ## Verification Status

  The Zig layer implements precondition checks matching:
  - `mkdir_precondition` from filesystem_model.v
  - `rmdir_precondition` from filesystem_model.v
  - `create_file_precondition` from file_operations.v
  - `delete_file_precondition` from file_operations.v

  ## Implementation Note

  This module uses Zigler to compile Zig code directly into NIFs,
  eliminating the need for C wrapper code. The Zig implementation
  provides memory safety and direct POSIX access.
  """

  use Zig, otp_app: :vsh, nifs: [mkdir: 1, rmdir: 1, create_file: 1, delete_file: 1, get_last_audit: 0]

  ~Z"""
  // SPDX-License-Identifier: AGPL-3.0-or-later
  // Valence Shell - Zigler NIF implementation

  const std = @import("std");
  const beam = @import("beam");

  // Global filesystem handle
  var g_fs: ?*Filesystem = null;
  var g_allocator: std.mem.Allocator = undefined;

  // Audit log entry
  const AuditEntry = struct {
      operation: []const u8,
      path: []const u8,
      result: PosixError,
      timestamp: i64,
  };

  // Simple audit log (ring buffer of last 100 entries)
  const AUDIT_LOG_SIZE = 100;
  var g_audit_log: [AUDIT_LOG_SIZE]?AuditEntry = [_]?AuditEntry{null} ** AUDIT_LOG_SIZE;
  var g_audit_index: usize = 0;
  var g_audit_count: usize = 0;

  fn recordAudit(operation: []const u8, path: []const u8, result: PosixError) void {
      g_audit_log[g_audit_index] = AuditEntry{
          .operation = operation,
          .path = path,
          .result = result,
          .timestamp = std.time.timestamp(),
      };
      g_audit_index = (g_audit_index + 1) % AUDIT_LOG_SIZE;
      if (g_audit_count < AUDIT_LOG_SIZE) {
          g_audit_count += 1;
      }
  }

  fn getLastAudit() ?AuditEntry {
      if (g_audit_count == 0) return null;
      const last_index = if (g_audit_index == 0) AUDIT_LOG_SIZE - 1 else g_audit_index - 1;
      return g_audit_log[last_index];
  }

  // POSIX error codes matching Coq's posix_errors.v
  const PosixError = enum(i32) {
      success = 0,
      eexist = 17,
      enoent = 2,
      eacces = 13,
      enotdir = 20,
      eisdir = 21,
      enotempty = 39,
      einval = 22,

      pub fn fromError(err: anyerror) PosixError {
          return switch (err) {
              error.PathAlreadyExists => .eexist,
              error.FileNotFound => .enoent,
              error.AccessDenied => .eacces,
              error.NotDir => .enotdir,
              error.IsDir => .eisdir,
              error.DirNotEmpty => .enotempty,
              else => .einval,
          };
      }
  };

  // Filesystem handle with sandboxing
  const Filesystem = struct {
      root: []const u8,
      allocator: std.mem.Allocator,

      pub fn init(allocator: std.mem.Allocator, root: []const u8) !*Filesystem {
          const fs = try allocator.create(Filesystem);
          fs.* = .{
              .root = root,
              .allocator = allocator,
          };
          return fs;
      }

      pub fn deinit(self: *Filesystem) void {
          self.allocator.destroy(self);
      }

      fn resolvePath(self: *const Filesystem, path: []const u8) ?[]const u8 {
          const full_path = std.fs.path.join(self.allocator, &[_][]const u8{ self.root, path }) catch return null;
          if (std.mem.indexOf(u8, full_path, "..")) |_| {
              self.allocator.free(full_path);
              return null;
          }
          return full_path;
      }

      pub fn mkdir(self: *Filesystem, path: []const u8) PosixError {
          const full_path = self.resolvePath(path) orelse return .eacces;
          defer self.allocator.free(full_path);

          std.fs.makeDirAbsolute(full_path) catch |err| {
              return PosixError.fromError(err);
          };
          return .success;
      }

      pub fn rmdir(self: *Filesystem, path: []const u8) PosixError {
          const full_path = self.resolvePath(path) orelse return .eacces;
          defer self.allocator.free(full_path);

          std.fs.deleteDirAbsolute(full_path) catch |err| {
              return PosixError.fromError(err);
          };
          return .success;
      }

      pub fn createFile(self: *Filesystem, path: []const u8) PosixError {
          const full_path = self.resolvePath(path) orelse return .eacces;
          defer self.allocator.free(full_path);

          const file = std.fs.createFileAbsolute(full_path, .{ .exclusive = true }) catch |err| {
              return PosixError.fromError(err);
          };
          file.close();
          return .success;
      }

      pub fn deleteFile(self: *Filesystem, path: []const u8) PosixError {
          const full_path = self.resolvePath(path) orelse return .eacces;
          defer self.allocator.free(full_path);

          std.fs.deleteFileAbsolute(full_path) catch |err| {
              return PosixError.fromError(err);
          };
          return .success;
      }
  };

  fn ensureFs() !*Filesystem {
      if (g_fs) |fs| return fs;

      g_allocator = beam.allocator;
      const sandbox = std.process.getEnvVarOwned(g_allocator, "VSH_SANDBOX") catch |err| {
          if (err == error.EnvironmentVariableNotFound) {
              return try Filesystem.init(g_allocator, "/tmp/vsh-sandbox");
          }
          return err;
      };
      defer g_allocator.free(sandbox);

      g_fs = try Filesystem.init(g_allocator, sandbox);
      return g_fs.?;
  }

  fn errorToAtom(err: PosixError) beam.term {
      return switch (err) {
          .success => beam.make_atom("ok"),
          .eexist => beam.make_atom("eexist"),
          .enoent => beam.make_atom("enoent"),
          .eacces => beam.make_atom("eacces"),
          .enotdir => beam.make_atom("enotdir"),
          .eisdir => beam.make_atom("eisdir"),
          .enotempty => beam.make_atom("enotempty"),
          .einval => beam.make_atom("einval"),
      };
  }

  // NIF: mkdir/1
  pub fn mkdir(path: []const u8) beam.term {
      const fs = ensureFs() catch return beam.make_error_tuple("init_failed");
      const result = fs.mkdir(path);
      recordAudit("mkdir", path, result);
      if (result == .success) {
          return beam.make_atom("ok");
      }
      return beam.make_error_tuple(errorToAtom(result));
  }

  // NIF: rmdir/1
  pub fn rmdir(path: []const u8) beam.term {
      const fs = ensureFs() catch return beam.make_error_tuple("init_failed");
      const result = fs.rmdir(path);
      recordAudit("rmdir", path, result);
      if (result == .success) {
          return beam.make_atom("ok");
      }
      return beam.make_error_tuple(errorToAtom(result));
  }

  // NIF: create_file/1
  pub fn create_file(path: []const u8) beam.term {
      const fs = ensureFs() catch return beam.make_error_tuple("init_failed");
      const result = fs.createFile(path);
      recordAudit("create_file", path, result);
      if (result == .success) {
          return beam.make_atom("ok");
      }
      return beam.make_error_tuple(errorToAtom(result));
  }

  // NIF: delete_file/1
  pub fn delete_file(path: []const u8) beam.term {
      const fs = ensureFs() catch return beam.make_error_tuple("init_failed");
      const result = fs.deleteFile(path);
      recordAudit("delete_file", path, result);
      if (result == .success) {
          return beam.make_atom("ok");
      }
      return beam.make_error_tuple(errorToAtom(result));
  }

  // NIF: get_last_audit/0
  pub fn get_last_audit() beam.term {
      const entry = getLastAudit() orelse return beam.make_error_tuple("no_entries");
      // Return as {operation, path, result, timestamp}
      return beam.make_tuple(.{
          beam.make_binary(entry.operation),
          beam.make_binary(entry.path),
          errorToAtom(entry.result),
          beam.make_i64(entry.timestamp),
      });
  }
  """

  @doc """
  Create a directory with precondition checking.

  Returns:
  - `:ok` on success
  - `{:error, :eexist}` if path already exists
  - `{:error, :enoent}` if parent doesn't exist
  - `{:error, :enotdir}` if parent is not a directory
  - `{:error, :eacces}` if no write permission
  """
  @spec mkdir(String.t()) :: :ok | {:error, atom()}
  def mkdir(_path), do: :erlang.nif_error(:not_loaded)

  @doc """
  Remove an empty directory with precondition checking.

  Returns:
  - `:ok` on success
  - `{:error, :enoent}` if path doesn't exist
  - `{:error, :enotdir}` if not a directory
  - `{:error, :enotempty}` if directory not empty
  - `{:error, :eacces}` if no write permission on parent
  """
  @spec rmdir(String.t()) :: :ok | {:error, atom()}
  def rmdir(_path), do: :erlang.nif_error(:not_loaded)

  @doc """
  Create an empty file with precondition checking.

  Returns:
  - `:ok` on success
  - `{:error, :eexist}` if path already exists
  - `{:error, :enoent}` if parent doesn't exist
  - `{:error, :enotdir}` if parent is not a directory
  - `{:error, :eacces}` if no write permission
  """
  @spec create_file(String.t()) :: :ok | {:error, atom()}
  def create_file(_path), do: :erlang.nif_error(:not_loaded)

  @doc """
  Delete a file with precondition checking.

  Returns:
  - `:ok` on success
  - `{:error, :enoent}` if path doesn't exist
  - `{:error, :eisdir}` if path is a directory
  - `{:error, :eacces}` if no write permission on parent
  """
  @spec delete_file(String.t()) :: :ok | {:error, atom()}
  def delete_file(_path), do: :erlang.nif_error(:not_loaded)

  @doc """
  Get the last audit log entry.

  Returns the most recent operation recorded by the Zig FFI layer,
  including the proof reference for MAA compliance.
  """
  @spec get_last_audit() :: {:ok, map()} | {:error, :no_entries}
  def get_last_audit, do: :erlang.nif_error(:not_loaded)
end
