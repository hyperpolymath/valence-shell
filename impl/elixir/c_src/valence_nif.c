// SPDX-License-Identifier: AGPL-3.0-or-later
// Valence Shell - Erlang NIF wrapper for Zig FFI

#include <erl_nif.h>
#include <stdlib.h>
#include <string.h>

// Include the Zig header from the Zig source directory
#include "valence_ffi.h"

// Atoms
static ERL_NIF_TERM atom_ok;
static ERL_NIF_TERM atom_error;
static ERL_NIF_TERM atom_eexist;
static ERL_NIF_TERM atom_enoent;
static ERL_NIF_TERM atom_enotdir;
static ERL_NIF_TERM atom_eisdir;
static ERL_NIF_TERM atom_enotempty;
static ERL_NIF_TERM atom_eacces;
static ERL_NIF_TERM atom_einval;
static ERL_NIF_TERM atom_eio;
static ERL_NIF_TERM atom_no_entries;

// Global filesystem handle (ValenceFS from Zig header)
static ValenceFS* g_fs = NULL;

// Convert POSIX error code to Erlang atom
// Uses actual POSIX error numbers from Zig PosixError enum
static ERL_NIF_TERM error_to_atom(ErlNifEnv* env, int err) {
    switch (err) {
        case 0:  return atom_ok;
        case 2:  return atom_enoent;    // ENOENT
        case 13: return atom_eacces;    // EACCES
        case 17: return atom_eexist;    // EEXIST
        case 20: return atom_enotdir;   // ENOTDIR
        case 21: return atom_eisdir;    // EISDIR
        case 22: return atom_einval;    // EINVAL
        case 39: return atom_enotempty; // ENOTEMPTY
        default: return atom_eio;
    }
}

// NIF: mkdir/1
static ERL_NIF_TERM nif_mkdir(ErlNifEnv* env, int argc, const ERL_NIF_TERM argv[]) {
    if (argc != 1) return enif_make_badarg(env);

    ErlNifBinary path_bin;
    if (!enif_inspect_binary(env, argv[0], &path_bin)) {
        // Try as iolist
        if (!enif_inspect_iolist_as_binary(env, argv[0], &path_bin)) {
            return enif_make_badarg(env);
        }
    }

    // Null-terminate the path
    char* path = enif_alloc(path_bin.size + 1);
    memcpy(path, path_bin.data, path_bin.size);
    path[path_bin.size] = '\0';

    int result = valence_mkdir(g_fs, path);
    enif_free(path);

    if (result == 0) {
        return atom_ok;
    } else {
        return enif_make_tuple2(env, atom_error, error_to_atom(env, result));
    }
}

// NIF: rmdir/1
static ERL_NIF_TERM nif_rmdir(ErlNifEnv* env, int argc, const ERL_NIF_TERM argv[]) {
    if (argc != 1) return enif_make_badarg(env);

    ErlNifBinary path_bin;
    if (!enif_inspect_iolist_as_binary(env, argv[0], &path_bin)) {
        return enif_make_badarg(env);
    }

    char* path = enif_alloc(path_bin.size + 1);
    memcpy(path, path_bin.data, path_bin.size);
    path[path_bin.size] = '\0';

    int result = valence_rmdir(g_fs, path);
    enif_free(path);

    if (result == 0) {
        return atom_ok;
    } else {
        return enif_make_tuple2(env, atom_error, error_to_atom(env, result));
    }
}

// NIF: create_file/1
static ERL_NIF_TERM nif_create_file(ErlNifEnv* env, int argc, const ERL_NIF_TERM argv[]) {
    if (argc != 1) return enif_make_badarg(env);

    ErlNifBinary path_bin;
    if (!enif_inspect_iolist_as_binary(env, argv[0], &path_bin)) {
        return enif_make_badarg(env);
    }

    char* path = enif_alloc(path_bin.size + 1);
    memcpy(path, path_bin.data, path_bin.size);
    path[path_bin.size] = '\0';

    int result = valence_create_file(g_fs, path);
    enif_free(path);

    if (result == 0) {
        return atom_ok;
    } else {
        return enif_make_tuple2(env, atom_error, error_to_atom(env, result));
    }
}

// NIF: delete_file/1
static ERL_NIF_TERM nif_delete_file(ErlNifEnv* env, int argc, const ERL_NIF_TERM argv[]) {
    if (argc != 1) return enif_make_badarg(env);

    ErlNifBinary path_bin;
    if (!enif_inspect_iolist_as_binary(env, argv[0], &path_bin)) {
        return enif_make_badarg(env);
    }

    char* path = enif_alloc(path_bin.size + 1);
    memcpy(path, path_bin.data, path_bin.size);
    path[path_bin.size] = '\0';

    int result = valence_delete_file(g_fs, path);
    enif_free(path);

    if (result == 0) {
        return atom_ok;
    } else {
        return enif_make_tuple2(env, atom_error, error_to_atom(env, result));
    }
}

// NIF: get_last_audit/0
static ERL_NIF_TERM nif_get_last_audit(ErlNifEnv* env, int argc, const ERL_NIF_TERM argv[]) {
    (void)argc;
    (void)argv;

    // TODO: Implement audit log retrieval from Zig
    return enif_make_tuple2(env, atom_error, atom_no_entries);
}

// NIF function table
static ErlNifFunc nif_funcs[] = {
    {"mkdir", 1, nif_mkdir, 0},
    {"rmdir", 1, nif_rmdir, 0},
    {"create_file", 1, nif_create_file, 0},
    {"delete_file", 1, nif_delete_file, 0},
    {"get_last_audit", 0, nif_get_last_audit, 0}
};

// NIF load callback
static int load(ErlNifEnv* env, void** priv_data, ERL_NIF_TERM load_info) {
    (void)priv_data;
    (void)load_info;

    // Create atoms
    atom_ok = enif_make_atom(env, "ok");
    atom_error = enif_make_atom(env, "error");
    atom_eexist = enif_make_atom(env, "eexist");
    atom_enoent = enif_make_atom(env, "enoent");
    atom_enotdir = enif_make_atom(env, "enotdir");
    atom_eisdir = enif_make_atom(env, "eisdir");
    atom_enotempty = enif_make_atom(env, "enotempty");
    atom_eacces = enif_make_atom(env, "eacces");
    atom_einval = enif_make_atom(env, "einval");
    atom_eio = enif_make_atom(env, "eio");
    atom_no_entries = enif_make_atom(env, "no_entries");

    // Initialize filesystem with sandbox root
    const char* sandbox = getenv("VSH_SANDBOX");
    if (!sandbox) sandbox = "/tmp/vsh-sandbox";

    g_fs = valence_fs_create(sandbox);
    if (!g_fs) {
        return -1;
    }

    return 0;
}

// NIF unload callback
static void unload(ErlNifEnv* env, void* priv_data) {
    (void)env;
    (void)priv_data;

    if (g_fs) {
        valence_fs_destroy(g_fs);
        g_fs = NULL;
    }
}

ERL_NIF_INIT(Elixir.VSH.NIF, nif_funcs, load, NULL, NULL, unload)
