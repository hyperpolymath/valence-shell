/* SPDX-License-Identifier: MPL-2.0
 * Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
 *
 * C ABI for libvalence_shell — the stable boundary that any language may call.
 *
 * This header is the C projection of the ABI/FFI spine:
 *
 *     src/abi  — Idris2 ABI declarations (%foreign)
 *         │
 *         ▼
 *     ffi/zig/src/main.zig  — Zig FFI implementation (`export fn`)
 *         │  compiled to libvalence_shell.{so,a}
 *         ▼
 *     THIS HEADER  →  C, Rust, ReScript, Julia, …
 *
 * NOTE ON PROVENANCE: this file is HAND-MAINTAINED to match the `export fn`
 * signatures in ffi/zig/src/main.zig and the `%foreign` declarations in
 * src/abi/Foreign.idr. Older docs describe an `idris2 --cg c-header` step, but
 * Idris2 ships no such codegen (only chez/node/racket/refc), so the header is
 * authored by hand. When you add or change a Zig `export fn`, update this
 * header in the same commit. See docs/ABI-FFI-BOUNDARY.md.
 */

#ifndef VALENCE_SHELL_H
#define VALENCE_SHELL_H

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* Opaque library handle. Its layout is private to the Zig implementation;
 * C consumers only ever hold a pointer to it. (Matches `?*Handle`.) */
typedef struct ValenceShellHandle ValenceShellHandle;

/* Result codes. Backed by `c_int` to match `enum(c_int)` in main.zig and the
 * Idris2 `Result` type in src/abi/Types.idr. */
typedef enum ValenceShellResult {
    VALENCE_SHELL_OK            = 0,
    VALENCE_SHELL_ERROR         = 1,
    VALENCE_SHELL_INVALID_PARAM = 2,
    VALENCE_SHELL_OUT_OF_MEMORY = 3,
    VALENCE_SHELL_NULL_POINTER  = 4
} ValenceShellResult;

/* Callback invoked by the library. Matches
 * `*const fn (u64, u32) callconv(.C) u32`. */
typedef uint32_t (*ValenceShellCallback)(uint64_t context, uint32_t value);

/* --- Lifecycle -------------------------------------------------------------- */

/* Initialize the library. Returns a handle, or NULL on failure. */
ValenceShellHandle *valence_shell_init(void);

/* Release a handle previously returned by valence_shell_init. */
void valence_shell_free(ValenceShellHandle *handle);

/* Non-zero if `handle` refers to an initialized library instance. */
uint32_t valence_shell_is_initialized(ValenceShellHandle *handle);

/* --- Operations ------------------------------------------------------------- */

/* Process a single 32-bit input. */
ValenceShellResult valence_shell_process(ValenceShellHandle *handle,
                                         uint32_t input);

/* Process `len` bytes at `buffer`. */
ValenceShellResult valence_shell_process_array(ValenceShellHandle *handle,
                                               const uint8_t *buffer,
                                               uint32_t len);

/* Register a C callback. */
ValenceShellResult valence_shell_register_callback(ValenceShellHandle *handle,
                                                   ValenceShellCallback callback);

/* --- Strings ---------------------------------------------------------------- */

/* Borrow the handle's current result string, or NULL. The returned pointer is
 * owned by the library; free it with valence_shell_free_string. */
const char *valence_shell_get_string(ValenceShellHandle *handle);

/* Free a string previously returned by the library. */
void valence_shell_free_string(const char *str);

/* --- Diagnostics ------------------------------------------------------------ */

/* Last error message for the calling thread, or NULL if none. Owned by the
 * library; do not free. */
const char *valence_shell_last_error(void);

/* Library version string (never NULL). Owned by the library; do not free. */
const char *valence_shell_version(void);

/* Build-info string (never NULL). Owned by the library; do not free. */
const char *valence_shell_build_info(void);

#ifdef __cplusplus
} /* extern "C" */
#endif

#endif /* VALENCE_SHELL_H */
