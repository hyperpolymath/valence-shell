/* SPDX-License-Identifier: AGPL-3.0-or-later */
/**
 * Valence Shell - C FFI Header
 *
 * This header provides the C ABI interface to the Valence Shell
 * formally verified filesystem operations.
 *
 * USAGE:
 *   1. Link against libvalence_ffi.a (static) or libvalence_ffi.so (dynamic)
 *   2. Create a filesystem handle with valence_fs_create()
 *   3. Call operations (valence_mkdir, valence_rmdir, etc.)
 *   4. Destroy handle with valence_fs_destroy()
 *
 * VERIFICATION:
 *   Each operation checks preconditions derived from Coq proofs.
 *   See proofs/coq/filesystem_model.v for the formal specification.
 *
 * ERROR CODES:
 *   0       = Success
 *   EEXIST  = Path already exists (mkdir, create_file)
 *   ENOENT  = Path does not exist (rmdir, delete_file)
 *   EACCES  = Permission denied
 *   ENOTDIR = Parent is not a directory
 *   EISDIR  = Cannot delete directory with delete_file
 *   ENOTEMPTY = Directory not empty (rmdir)
 */

#ifndef VALENCE_FFI_H
#define VALENCE_FFI_H

#include <stdbool.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* Opaque filesystem handle */
typedef struct ValenceFS ValenceFS;

/* Error type (matches POSIX errno values) */
typedef int ValenceError;

/* Error codes */
#define VALENCE_SUCCESS   0
#define VALENCE_EEXIST    17
#define VALENCE_ENOENT    2
#define VALENCE_EACCES    13
#define VALENCE_ENOTDIR   20
#define VALENCE_EISDIR    21
#define VALENCE_ENOTEMPTY 39
#define VALENCE_EINVAL    22

/**
 * Create a new filesystem handle.
 *
 * The root path defines the sandbox boundary. All operations are
 * restricted to paths within this root directory.
 *
 * @param root  Absolute path to sandbox root (null-terminated)
 * @return      Filesystem handle, or NULL on failure
 *
 * Example:
 *   ValenceFS* fs = valence_fs_create("/home/user/sandbox");
 */
ValenceFS* valence_fs_create(const char* root);

/**
 * Destroy a filesystem handle.
 *
 * @param handle  Handle returned by valence_fs_create()
 */
void valence_fs_destroy(ValenceFS* handle);

/**
 * Create a directory (formally verified operation).
 *
 * THEOREM: mkdir_rmdir_reversible
 *   rmdir(path, mkdir(path, fs)) = fs
 *   (when preconditions are met)
 *
 * PRECONDITIONS:
 *   - Path does not exist
 *   - Parent directory exists and is a directory
 *   - Parent directory is writable
 *
 * @param handle  Filesystem handle
 * @param path    Path relative to sandbox root (null-terminated)
 * @return        0 on success, error code on failure
 */
ValenceError valence_mkdir(ValenceFS* handle, const char* path);

/**
 * Remove a directory (formally verified operation).
 *
 * PRECONDITIONS:
 *   - Path exists and is a directory
 *   - Directory is empty
 *   - Parent directory is writable
 *   - Not the root directory
 *
 * @param handle  Filesystem handle
 * @param path    Path relative to sandbox root
 * @return        0 on success, error code on failure
 */
ValenceError valence_rmdir(ValenceFS* handle, const char* path);

/**
 * Create an empty file (formally verified operation).
 *
 * THEOREM: create_delete_file_reversible
 *   delete_file(path, create_file(path, fs)) = fs
 *
 * PRECONDITIONS:
 *   - Path does not exist
 *   - Parent directory exists and is a directory
 *   - Parent directory is writable
 *
 * @param handle  Filesystem handle
 * @param path    Path relative to sandbox root
 * @return        0 on success, error code on failure
 */
ValenceError valence_create_file(ValenceFS* handle, const char* path);

/**
 * Delete a file (formally verified operation).
 *
 * PRECONDITIONS:
 *   - Path exists and is a file (not directory)
 *   - Parent directory is writable
 *
 * @param handle  Filesystem handle
 * @param path    Path relative to sandbox root
 * @return        0 on success, error code on failure
 */
ValenceError valence_delete_file(ValenceFS* handle, const char* path);

/**
 * Check if a path exists.
 *
 * @param handle  Filesystem handle
 * @param path    Path relative to sandbox root
 * @return        true if path exists, false otherwise
 */
bool valence_path_exists(ValenceFS* handle, const char* path);

/**
 * Check if a path is a directory.
 *
 * @param handle  Filesystem handle
 * @param path    Path relative to sandbox root
 * @return        true if path is a directory, false otherwise
 */
bool valence_is_directory(ValenceFS* handle, const char* path);

/**
 * Check if a path is a regular file.
 *
 * @param handle  Filesystem handle
 * @param path    Path relative to sandbox root
 * @return        true if path is a file, false otherwise
 */
bool valence_is_file(ValenceFS* handle, const char* path);

/* === Extended API (with audit support) === */

/**
 * Create filesystem handle with audit logging.
 *
 * @param root        Sandbox root path
 * @param audit_path  Path to audit log file (NULL to disable)
 * @return            Filesystem handle
 */
ValenceFS* valence_fs_create_with_audit(const char* root, const char* audit_path);

/**
 * Get the error message for an error code.
 *
 * @param error  Error code from a valence operation
 * @return       Human-readable error message
 */
const char* valence_strerror(ValenceError error);

/**
 * Get the proof reference for an operation type.
 *
 * @param operation  Operation name ("mkdir", "rmdir", etc.)
 * @return           Coq theorem reference, or NULL if unknown
 */
const char* valence_proof_reference(const char* operation);

#ifdef __cplusplus
}
#endif

#endif /* VALENCE_FFI_H */
