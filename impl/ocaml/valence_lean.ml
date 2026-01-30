(* SPDX-License-Identifier: PMPL-1.0-or-later *)
(** Valence Shell - OCaml Bindings to Lean 4 Verified Code

    This module provides OCaml bindings to the Lean 4 compiled code
    via C FFI using Ctypes.

    Architecture:
    - Lean 4 proofs → C code (via Lean compiler)
    - C wrapper (lean_wrapper.c) → Shared library
    - This file → OCaml Ctypes bindings → Ergonomic API
*)

open Ctypes
open Foreign

(** * Error Codes *)

type error_code =
  | ENOERR
  | EEXIST
  | ENOENT
  | EACCES
  | ENOTDIR
  | EISDIR
  | ENOTEMPTY

let error_code_of_int = function
  | 0 -> ENOERR
  | 17 -> EEXIST
  | 2 -> ENOENT
  | 13 -> EACCES
  | 20 -> ENOTDIR
  | 21 -> EISDIR
  | 39 -> ENOTEMPTY
  | n -> failwith (Printf.sprintf "Unknown error code: %d" n)

let error_code_to_unix = function
  | ENOERR -> None
  | EEXIST -> Some Unix.EEXIST
  | ENOENT -> Some Unix.ENOENT
  | EACCES -> Some Unix.EACCES
  | ENOTDIR -> Some Unix.ENOTDIR
  | EISDIR -> Some Unix.EISDIR
  | ENOTEMPTY -> Some Unix.ENOTEMPTY

(** * C Types *)

(* vsh_result_t struct *)
type vsh_result
let vsh_result : vsh_result structure typ = structure "vsh_result_t"
let vsh_result_success = field vsh_result "success" int
let vsh_result_error = field vsh_result "error" int
let () = seal vsh_result

(* vsh_filesystem_t opaque pointer *)
type vsh_filesystem
let vsh_filesystem_t : vsh_filesystem structure ptr typ =
  ptr (structure "vsh_filesystem")

(** * Foreign Function Declarations *)

(* Load shared library *)
let lib = Dl.dlopen ~filename:"liblean_vsh.so" ~flags:[Dl.RTLD_NOW]

(* vsh_filesystem_create *)
let vsh_filesystem_create =
  foreign ~from:lib "vsh_filesystem_create"
    (string @-> returning vsh_filesystem_t)

(* vsh_filesystem_destroy *)
let vsh_filesystem_destroy =
  foreign ~from:lib "vsh_filesystem_destroy"
    (vsh_filesystem_t @-> returning void)

(* vsh_safe_mkdir *)
let vsh_safe_mkdir_ffi =
  foreign ~from:lib "vsh_safe_mkdir"
    (vsh_filesystem_t @-> string @-> returning vsh_result)

(* vsh_safe_rmdir *)
let vsh_safe_rmdir_ffi =
  foreign ~from:lib "vsh_safe_rmdir"
    (vsh_filesystem_t @-> string @-> returning vsh_result)

(* vsh_safe_create_file *)
let vsh_safe_create_file_ffi =
  foreign ~from:lib "vsh_safe_create_file"
    (vsh_filesystem_t @-> string @-> returning vsh_result)

(* vsh_safe_delete_file *)
let vsh_safe_delete_file_ffi =
  foreign ~from:lib "vsh_safe_delete_file"
    (vsh_filesystem_t @-> string @-> returning vsh_result)

(* vsh_get_version *)
let vsh_get_version =
  foreign ~from:lib "vsh_get_version"
    (void @-> returning string)

(** * OCaml-Friendly API *)

(** Filesystem handle type *)
type filesystem = vsh_filesystem structure ptr

(** Create filesystem handle *)
let create_fs root = vsh_filesystem_create root

(** Destroy filesystem handle *)
let destroy_fs fs = vsh_filesystem_destroy fs

(** Convert C result to OCaml result *)
let result_of_vsh_result r =
  let success = getf r vsh_result_success in
  let error_int = getf r vsh_result_error in
  let error = error_code_of_int error_int in
  if success = 1 then Ok ()
  else match error_code_to_unix error with
       | Some unix_err -> Error unix_err
       | None -> Error Unix.EIO  (* Generic error *)

(** Safe mkdir - check preconditions only *)
let safe_mkdir fs path =
  let r = vsh_safe_mkdir_ffi fs path in
  result_of_vsh_result r

(** Safe rmdir - check preconditions only *)
let safe_rmdir fs path =
  let r = vsh_safe_rmdir_ffi fs path in
  result_of_vsh_result r

(** Safe file creation - check preconditions only *)
let safe_create_file fs path =
  let r = vsh_safe_create_file_ffi fs path in
  result_of_vsh_result r

(** Safe file deletion - check preconditions only *)
let safe_delete_file fs path =
  let r = vsh_safe_delete_file_ffi fs path in
  result_of_vsh_result r

(** Get library version *)
let version () = vsh_get_version ()

(** * Usage Example *)

(**
   {[
     (* Create filesystem handle *)
     let fs = ValenceLean.create_fs "/tmp/vsh_test" in

     (* Check if mkdir would succeed (Lean verification) *)
     match ValenceLean.safe_mkdir fs "/test_dir" with
     | Ok () ->
         (* Preconditions satisfied, do real mkdir *)
         (match FilesystemFFI.real_mkdir fs "/test_dir" with
          | Ok () -> print_endline "Directory created"
          | Error e -> Printf.printf "mkdir failed: %s\n" (Unix.error_message e))
     | Error e ->
         (* Preconditions not satisfied *)
         Printf.printf "mkdir would fail: %s\n" (Unix.error_message e);

     (* Clean up *)
     ValenceLean.destroy_fs fs
   ]}
*)

(** * Integration Notes *)

(**
   This module provides VERIFIED precondition checking.
   Combine with FilesystemFFI for complete verified operations:

   1. Check preconditions (this module, from Lean proofs)
   2. Execute operation (FilesystemFFI, real POSIX)

   Trust chain:
   - Lean 4 proofs → High trust (formally verified)
   - Lean → C compiler → Medium trust (standard compiler)
   - C → OCaml FFI → Medium trust (standard OCaml)
   - POSIX syscalls → Low trust (OS dependent)

   Result: Mathematical guarantee on preconditions,
           standard trust on execution.
*)
