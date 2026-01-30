// SPDX-License-Identifier: PMPL-1.0-or-later
/* Valence Shell - C Wrapper for Lean 4 Extracted Code
 *
 * This file provides C-callable wrappers around Lean 4 compiled code.
 * It handles:
 * - String marshaling between C and Lean
 * - Filesystem state representation
 * - Error code conversion
 *
 * Compiles to shared library (.so) for OCaml FFI consumption.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <lean/lean.h>

#ifdef __cplusplus
extern "C" {
#endif

/* Error codes matching Lean CErrorCode type */
typedef enum {
    VSH_ENOERR = 0,
    VSH_EEXIST = 17,
    VSH_ENOENT = 2,
    VSH_EACCES = 13,
    VSH_ENOTDIR = 20,
    VSH_EISDIR = 21,
    VSH_ENOTEMPTY = 39
} vsh_error_t;

/* Result type for operations */
typedef struct {
    int success;       /* 1 = success, 0 = failure */
    vsh_error_t error; /* Error code if success = 0 */
} vsh_result_t;

/* Opaque filesystem handle
 *
 * In a full implementation, this would wrap:
 * - Lean Filesystem value (abstract map)
 * - Real POSIX filesystem root
 * - Audit log handle
 *
 * For now, placeholder structure.
 */
typedef struct vsh_filesystem {
    void* lean_fs_obj;  /* Lean object representing filesystem state */
    char* root_path;    /* Root path for sandboxing */
} vsh_filesystem_t;

/* Create filesystem handle */
vsh_filesystem_t* vsh_filesystem_create(const char* root) {
    vsh_filesystem_t* fs = malloc(sizeof(vsh_filesystem_t));
    if (!fs) return NULL;

    fs->root_path = strdup(root);

    /* Initialize Lean emptyFS object
     * emptyFS : Filesystem = fun _ => none
     * This is a constant empty map represented as a closure
     */
    fs->lean_fs_obj = lean_box(0);  /* Empty filesystem represented as null pointer */
    lean_inc_ref(fs->lean_fs_obj);   /* Increment reference count */

    return fs;
}

/* Destroy filesystem handle */
void vsh_filesystem_destroy(vsh_filesystem_t* fs) {
    if (!fs) return;
    free(fs->root_path);

    /* Decrement Lean object reference count */
    if (fs->lean_fs_obj) {
        lean_dec_ref(fs->lean_fs_obj);
    }

    free(fs);
}

/* Helper: Convert C string to Lean String
 *
 * Lean strings are UTF-8 encoded objects.
 * This uses Lean runtime API to create them.
 */
static lean_object* c_str_to_lean_str(const char* c_str) {
    return lean_mk_string(c_str);
}

/* Helper: Convert Lean String to C string
 *
 * Returns newly allocated C string (caller must free).
 */
static char* lean_str_to_c_str(lean_object* lean_str) {
    const char* data = lean_string_cstr(lean_str);
    return strdup(data);
}

/* Helper: Convert Lean CResult to vsh_result_t */
static vsh_result_t lean_result_to_c(lean_object* lean_result) {
    vsh_result_t result;

    /* Extract fields from Lean CResult structure
     *
     * Lean structure layout:
     * CResult.mk : Bool -> CErrorCode -> CResult
     *
     * Field 0: success (Bool - unboxed u8)
     * Field 1: errorCode (CErrorCode enum - unboxed u8)
     */

    /* Extract success field (Bool) */
    uint8_t success = lean_unbox(lean_ctor_get(lean_result, 0));
    result.success = (success != 0) ? 1 : 0;

    /* Extract errorCode field (CErrorCode enum) */
    uint8_t error_code = lean_unbox(lean_ctor_get(lean_result, 1));
    result.error = (vsh_error_t)error_code;

    return result;
}

/* Safe mkdir wrapper
 *
 * Calls Lean safeMkdirStr function to check preconditions.
 * Returns success/error code.
 * Does NOT perform actual mkdir (that's done by OCaml FFI layer).
 */
vsh_result_t vsh_safe_mkdir(vsh_filesystem_t* fs, const char* path) {
    if (!fs || !path) {
        vsh_result_t err = {0, VSH_ENOENT};
        return err;
    }

    /* Convert C path to Lean String */
    lean_object* lean_path = c_str_to_lean_str(path);

    /* Get Lean filesystem object */
    lean_object* lean_fs = (lean_object*)fs->lean_fs_obj;
    lean_inc_ref(lean_fs);  /* Increment before passing to Lean */

    /* Call Lean safeMkdirStr function
     * Signature: safeMkdirStr (pathStr : String) (fs : Filesystem) : CResult
     */
    extern lean_object* l_ValenceShell_Extraction_safeMkdirStr(lean_object*, lean_object*);
    lean_object* lean_result = l_ValenceShell_Extraction_safeMkdirStr(lean_path, lean_fs);

    /* Convert Lean CResult to C result */
    vsh_result_t result = lean_result_to_c(lean_result);

    /* Clean up Lean objects */
    lean_dec_ref(lean_result);

    return result;
}

/* Safe rmdir wrapper */
vsh_result_t vsh_safe_rmdir(vsh_filesystem_t* fs, const char* path) {
    if (!fs || !path) {
        vsh_result_t err = {0, VSH_ENOENT};
        return err;
    }

    lean_object* lean_path = c_str_to_lean_str(path);

    /* Get Lean filesystem object */
    lean_object* lean_fs = (lean_object*)fs->lean_fs_obj;
    lean_inc_ref(lean_fs);

    /* Call Lean safeRmdirStr function */
    extern lean_object* l_ValenceShell_Extraction_safeRmdirStr(lean_object*, lean_object*);
    lean_object* lean_result = l_ValenceShell_Extraction_safeRmdirStr(lean_path, lean_fs);

    vsh_result_t result = lean_result_to_c(lean_result);

    lean_dec_ref(lean_result);
    return result;
}

/* Safe file creation wrapper */
vsh_result_t vsh_safe_create_file(vsh_filesystem_t* fs, const char* path) {
    if (!fs || !path) {
        vsh_result_t err = {0, VSH_ENOENT};
        return err;
    }

    lean_object* lean_path = c_str_to_lean_str(path);

    /* Get Lean filesystem object */
    lean_object* lean_fs = (lean_object*)fs->lean_fs_obj;
    lean_inc_ref(lean_fs);

    /* Call Lean safeCreateFileStr function */
    extern lean_object* l_ValenceShell_Extraction_safeCreateFileStr(lean_object*, lean_object*);
    lean_object* lean_result = l_ValenceShell_Extraction_safeCreateFileStr(lean_path, lean_fs);

    vsh_result_t result = lean_result_to_c(lean_result);

    lean_dec_ref(lean_result);
    return result;
}

/* Safe file deletion wrapper */
vsh_result_t vsh_safe_delete_file(vsh_filesystem_t* fs, const char* path) {
    if (!fs || !path) {
        vsh_result_t err = {0, VSH_ENOENT};
        return err;
    }

    lean_object* lean_path = c_str_to_lean_str(path);

    /* Get Lean filesystem object */
    lean_object* lean_fs = (lean_object*)fs->lean_fs_obj;
    lean_inc_ref(lean_fs);

    /* Call Lean safeDeleteFileStr function */
    extern lean_object* l_ValenceShell_Extraction_safeDeleteFileStr(lean_object*, lean_object*);
    lean_object* lean_result = l_ValenceShell_Extraction_safeDeleteFileStr(lean_path, lean_fs);

    vsh_result_t result = lean_result_to_c(lean_result);

    lean_dec_ref(lean_result);
    return result;
}

/* Test function to verify linking */
const char* vsh_get_version(void) {
    return "Valence Shell Lean FFI v0.1.0";
}

#ifdef __cplusplus
}
#endif

/*
 * Implementation Notes
 * ====================
 *
 * Completing this wrapper requires:
 *
 * 1. Include Lean-generated header:
 *    #include "Extraction.h"  // Generated by Lean compiler
 *
 * 2. Link against Lean runtime:
 *    -lleanshared
 *
 * 3. Understand Lean object layout:
 *    - Lean objects are reference-counted
 *    - Use lean_inc_ref() / lean_dec_ref()
 *    - Structures accessed via field offsets
 *
 * 4. Call Lean functions:
 *    extern lean_object* ValenceShell_Extraction_safeMkdirStr(
 *        lean_object* path,
 *        lean_object* fs
 *    );
 *
 * 5. Handle Lean Sum/Option types:
 *    - CResult is a structure: { success : Bool, errorCode : CErrorCode }
 *    - Extract via lean_ctor_get()
 *
 * Example complete implementation of vsh_safe_mkdir:
 *
 * vsh_result_t vsh_safe_mkdir(vsh_filesystem_t* fs, const char* path) {
 *     lean_object* lean_path = c_str_to_lean_str(path);
 *     lean_object* lean_fs = (lean_object*)fs->lean_fs_obj;
 *
 *     // Call Lean function
 *     lean_object* lean_result = ValenceShell_Extraction_safeMkdirStr(
 *         lean_path, lean_fs
 *     );
 *
 *     // Extract fields from CResult structure
 *     uint8_t success = lean_unbox(lean_ctor_get(lean_result, 0));
 *     uint8_t error_code = lean_unbox(lean_ctor_get(lean_result, 1));
 *
 *     vsh_result_t result = {
 *         .success = success,
 *         .error = (vsh_error_t)error_code
 *     };
 *
 *     // Clean up
 *     lean_dec_ref(lean_result);
 *
 *     return result;
 * }
 *
 * Reference:
 * - Lean 4 FFI Guide: https://lean-lang.org/lean4/doc/dev/ffi.html
 * - Lean Runtime API: $(lean --print-prefix)/include/lean/lean.h
 */
