(** Valence Shell - OCaml POSIX FFI Layer

    This module provides the FFI (Foreign Function Interface) layer
    that connects extracted Coq code to real POSIX filesystem operations.

    CRITICAL: This layer is NOT formally verified.
    It must be carefully reviewed and tested.

    Trust Boundary:
    - Coq proofs guarantee logical correctness
    - Extraction preserves semantics to OCaml
    - THIS FFI LAYER must correctly implement the model
    - POSIX itself is assumed correct (OS trust)
*)

(** * Path Conversion *)

(** Convert Coq path (list of strings) to Unix path string *)
let rec string_of_char_list chars =
  String.concat "" (List.map (String.make 1) chars)

let path_to_string path =
  let components = List.map string_of_char_list path in
  match components with
  | [] -> "/"
  | cs -> "/" ^ (String.concat "/" cs)

let string_to_char_list str =
  let rec explode i acc =
    if i < 0 then acc
    else explode (i - 1) (str.[i] :: acc)
  in
  explode (String.length str - 1) []

let string_to_path str =
  let components = String.split_on_char '/' str in
  let components = List.filter (fun s -> s <> "") components in
  List.map string_to_char_list components

(** * Filesystem State *)

(** In the pure Coq model, filesystem is a mathematical function.
    In reality, we use the actual POSIX filesystem state.

    This type represents a "handle" to the real filesystem. *)
type real_filesystem = {
  root: string;  (* Root path for sandboxing *)
  audit_log: out_channel option;  (* Optional audit trail *)
}

let create_fs ?(audit_path=None) root =
  let audit_log = match audit_path with
    | None -> None
    | Some path -> Some (open_out path)
  in
  { root; audit_log }

let log_operation fs op path =
  match fs.audit_log with
  | None -> ()
  | Some ch ->
      Printf.fprintf ch "[%f] %s %s\n"
        (Unix.gettimeofday ())
        op
        (path_to_string path);
      flush ch

(** * Safe Path Resolution *)

(** Ensure path is within sandbox root *)
let resolve_path fs path =
  let path_str = path_to_string path in
  let full_path = Filename.concat fs.root path_str in
  (* Security: Prevent .. escaping sandbox *)
  let canonical = (* Would use realpath in production *)
    full_path
  in
  if String.length canonical >= String.length fs.root &&
     String.sub canonical 0 (String.length fs.root) = fs.root
  then Ok canonical
  else Error Unix.EACCES

(** * POSIX Operations *)

(** Real mkdir implementation *)
let real_mkdir fs path =
  log_operation fs "mkdir" path;
  match resolve_path fs path with
  | Error e -> Error e
  | Ok path_str ->
      try
        Unix.mkdir path_str 0o755;
        Ok ()
      with
      | Unix.Unix_error(err, _, _) -> Error err

(** Real rmdir implementation *)
let real_rmdir fs path =
  log_operation fs "rmdir" path;
  match resolve_path fs path with
  | Error e -> Error e
  | Ok path_str ->
      try
        Unix.rmdir path_str;
        Ok ()
      with
      | Unix.Unix_error(err, _, _) -> Error err

(** Real file creation *)
let real_create_file fs path =
  log_operation fs "create_file" path;
  match resolve_path fs path with
  | Error e -> Error e
  | Ok path_str ->
      try
        let fd = Unix.openfile path_str
          [Unix.O_WRONLY; Unix.O_CREAT; Unix.O_EXCL]
          0o644
        in
        Unix.close fd;
        Ok ()
      with
      | Unix.Unix_error(err, _, _) -> Error err

(** Real file deletion *)
let real_delete_file fs path =
  log_operation fs "delete_file" path;
  match resolve_path fs path with
  | Error e -> Error e
  | Ok path_str ->
      try
        Unix.unlink path_str;
        Ok ()
      with
      | Unix.Unix_error(err, _, _) -> Error err

(** * Query Operations *)

let path_exists fs path =
  match resolve_path fs path with
  | Error _ -> false
  | Ok path_str ->
      try
        let _ = Unix.stat path_str in
        true
      with
      | Unix.Unix_error(Unix.ENOENT, _, _) -> false
      | _ -> false

let is_directory fs path =
  match resolve_path fs path with
  | Error _ -> false
  | Ok path_str ->
      try
        let stats = Unix.stat path_str in
        stats.Unix.st_kind = Unix.S_DIR
      with
      | _ -> false

let is_file fs path =
  match resolve_path fs path with
  | Error _ -> false
  | Ok path_str ->
      try
        let stats = Unix.stat path_str in
        stats.Unix.st_kind = Unix.S_REG
      with
      | _ -> false

(** * Integration with Extracted Code *)

(** This is where we'd connect the extracted Coq functions
    with the real POSIX operations.

    For full integration:

    1. Extracted code provides logical decisions
    2. FFI provides actual syscalls
    3. Combine: extract logic, execute FFI

    Example:

    let verified_mkdir path =
      (* Call extracted safe_mkdir to check preconditions *)
      match Filesystem.safe_mkdir path abstract_fs with
      | Ok _ -> real_mkdir real_fs path
      | Error e -> Error e

    This gives us:
    - Verified precondition checking (from Coq)
    - Real execution (from FFI)
    - Auditable operations (logged)
*)

(** * Test Harness *)

let run_tests () =
  let test_fs = create_fs "/tmp/vsh_test" in

  (* Test 1: Create directory *)
  let test_path = string_to_path "test_dir" in
  Printf.printf "Test 1: Creating directory...\n";
  (match real_mkdir test_fs test_path with
   | Ok () -> Printf.printf "  ✓ mkdir succeeded\n"
   | Error e -> Printf.printf "  ✗ mkdir failed: %s\n"
                  (Unix.error_message e));

  (* Test 2: Verify directory exists *)
  Printf.printf "Test 2: Checking directory exists...\n";
  if is_directory test_fs test_path
  then Printf.printf "  ✓ directory exists\n"
  else Printf.printf "  ✗ directory does not exist\n";

  (* Test 3: Remove directory *)
  Printf.printf "Test 3: Removing directory...\n";
  (match real_rmdir test_fs test_path with
   | Ok () -> Printf.printf "  ✓ rmdir succeeded\n"
   | Error e -> Printf.printf "  ✗ rmdir failed: %s\n"
                  (Unix.error_message e));

  (* Test 4: Verify directory removed *)
  Printf.printf "Test 4: Checking directory removed...\n";
  if not (path_exists test_fs test_path)
  then Printf.printf "  ✓ directory removed\n"
  else Printf.printf "  ✗ directory still exists\n";

  (* Test 5: File operations *)
  let file_path = string_to_path "test_file" in
  Printf.printf "Test 5: File create/delete cycle...\n";
  (match real_create_file test_fs file_path with
   | Ok () ->
       Printf.printf "  ✓ create_file succeeded\n";
       (match real_delete_file test_fs file_path with
        | Ok () -> Printf.printf "  ✓ delete_file succeeded\n"
        | Error e -> Printf.printf "  ✗ delete_file failed: %s\n"
                       (Unix.error_message e))
   | Error e -> Printf.printf "  ✗ create_file failed: %s\n"
                  (Unix.error_message e))

(** Entry point *)
let () =
  Printf.printf "Valence Shell - OCaml FFI Test Suite\n";
  Printf.printf "=====================================\n\n";
  run_tests ()

(** * Notes on Verification Gap *)

(** This FFI layer demonstrates the "verification gap":

    ✓ Coq proves: mkdir preconditions → successful mkdir → rmdir → original state
    ✓ Extraction: Coq logic → OCaml logic (trusted)
    ❌ FFI layer: OCaml logic → POSIX calls (NOT verified)

    To close this gap:

    1. Formal semantics of POSIX (huge effort - see seL4)
    2. Refinement proof: abstract model → POSIX semantics
    3. Verified compilation: OCaml → machine code

    OR:

    1. Extensive testing of FFI layer
    2. Runtime assertion checking
    3. Fuzzing and property-based testing
    4. Operational semantics review

    Current status: Research prototype with FFI template.
    Production use requires closing verification gap.
*)
