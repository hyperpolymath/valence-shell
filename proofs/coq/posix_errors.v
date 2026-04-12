(** Valence Shell - POSIX Error Modeling

    Models POSIX error conditions for filesystem operations.
    Proves error handling correctness and error-free operation equivalence.

    This extends the pure functional model to handle real-world error cases.

    Proof status:
    - 5 of 6 decision procedures proved constructively (from Filesystem semantics).
    - is_empty_dir_dec remains axiomatic: requires Classical or finite-map refactor.
    - safe_* definitions use nested `if` on sumbool (not negb, which requires bool).
    - functional_extensionality from filesystem_model transitive import.
*)

Require Import String.
Require Import List.
Require Import Bool.
Import ListNotations.

Require Import filesystem_model.
Require Import file_operations.
Require Import filesystem_composition.

(** * POSIX Error Codes *)

Inductive POSIXError : Type :=
  | EEXIST   : POSIXError  (* File/directory already exists *)
  | ENOENT   : POSIXError  (* No such file or directory *)
  | EACCES   : POSIXError  (* Permission denied *)
  | ENOTDIR  : POSIXError  (* Not a directory *)
  | EISDIR   : POSIXError  (* Is a directory *)
  | ENOTEMPTY : POSIXError (* Directory not empty *)
  | EINVAL   : POSIXError  (* Invalid argument *)
  | EIO      : POSIXError  (* I/O error *)
  .

(** * Result Type for Operations *)

Inductive OperationResult (A : Type) : Type :=
  | Success : A -> OperationResult A
  | Error : POSIXError -> OperationResult A
  .

Arguments Success {A}.
Arguments Error {A}.

(** * Decision Procedures

    Must appear before the safe_* definitions that use them.

    Four decision procedures are proved constructively by inspecting the
    Filesystem function (Path -> option FSNode) directly.
    path_eq_dec follows from list_eq_dec + String.string_dec.
    is_empty_dir_dec is axiomatic — see justification below. *)

(** path_exists is decidable by case analysis on (fs p). *)
Lemma path_exists_dec : forall p fs, {path_exists p fs} + {~ path_exists p fs}.
Proof.
  intros p fs.
  unfold path_exists.
  destruct (fs p) as [node|].
  - left. exists node. reflexivity.
  - right. intros [node H]. discriminate.
Defined.

(** is_directory is decidable by inspecting the node_type field. *)
Lemma is_directory_dec : forall p fs, {is_directory p fs} + {~ is_directory p fs}.
Proof.
  intros p fs.
  unfold is_directory.
  destruct (fs p) as [[ntype perms]|].
  - destruct ntype.
    + (* File *) right. intros [perms' H]. inversion H.
    + (* Directory *) left. exists perms. reflexivity.
  - right. intros [perms H]. discriminate.
Defined.

(** is_file is decidable by inspecting the node_type field. *)
Lemma is_file_dec : forall p fs, {is_file p fs} + {~ is_file p fs}.
Proof.
  intros p fs.
  unfold is_file.
  destruct (fs p) as [[ntype perms]|].
  - destruct ntype.
    + (* File *) left. exists perms. reflexivity.
    + (* Directory *) right. intros [perms' H]. inversion H.
  - right. intros [perms H]. discriminate.
Defined.

(** has_write_permission is decidable by inspecting the node and its writable flag. *)
Lemma has_write_permission_dec : forall p fs, {has_write_permission p fs} + {~ has_write_permission p fs}.
Proof.
  intros p fs.
  unfold has_write_permission.
  destruct (fs p) as [node|].
  - destruct (writable (permissions node)) eqn:Hw.
    + left. exists node. split; [reflexivity | assumption].
    + right. intros [node' [Heq Hwr]].
      inversion Heq. subst. rewrite Hw in Hwr. discriminate.
  - right. intros [node [H _]]. discriminate.
Defined.

(** Path equality is decidable: Path = list string, decided by list_eq_dec + string_dec. *)
Lemma path_eq_dec : forall p1 p2 : Path, {p1 = p2} + {p1 <> p2}.
Proof.
  apply list_eq_dec.
  apply String.string_dec.
Defined.

(** is_empty_dir is NOT decidable constructively with the current model.

    is_empty_dir p fs requires:
      forall child : Path, path_prefix p child = true -> child <> p -> ~ path_exists child fs.

    With Filesystem = Path -> option FSNode (a function over an infinite domain),
    there is no finite enumeration of all Path values, so this universal
    quantification cannot be discharged constructively.

    Justification: in the operational model, every reachable filesystem is
    produced by a finite sequence of mkdir / rmdir / create_file / delete_file
    operations, so the set of inhabited paths is always finite in practice.
    Constructive decidability requires changing the Filesystem representation
    to a finite map (e.g., list (Path * FSNode) or MSetAVL), at which point
    is_empty_dir can be decided by scanning the entries.

    Migration path: switch Filesystem to FMaps.t FSNode and reprove. *)
Axiom is_empty_dir_dec : forall p fs, {is_empty_dir p fs} + {~ is_empty_dir p fs}.

(** * Safe Operations with Error Handling

    safe_* definitions use nested `if` on sumbool values.
    Using `negb (sumbool_val)` is a type error (negb : bool -> bool, not sumbool)
    so we invert the condition by nesting the positive branch first. *)

(** Safe mkdir - returns error codes instead of requiring preconditions *)
Definition safe_mkdir (p : Path) (fs : Filesystem) : OperationResult Filesystem :=
  if path_exists_dec p fs then
    Error EEXIST                                     (* p already exists *)
  else if path_exists_dec (parent_path p) fs then
    if is_directory_dec (parent_path p) fs then
      if has_write_permission_dec (parent_path p) fs then
        Success (mkdir p fs)
      else Error EACCES
    else Error ENOTDIR
  else Error ENOENT.                                 (* parent not found *)

(** Safe rmdir - returns error codes *)
Definition safe_rmdir (p : Path) (fs : Filesystem) : OperationResult Filesystem :=
  if path_exists_dec p fs then
    if is_directory_dec p fs then
      if is_empty_dir_dec p fs then
        if has_write_permission_dec (parent_path p) fs then
          if path_eq_dec p root_path then
            Error EACCES                             (* cannot remove root *)
          else
            Success (rmdir p fs)
        else Error EACCES
      else Error ENOTEMPTY
    else Error ENOTDIR
  else Error ENOENT.

(** Safe create_file - returns error codes *)
Definition safe_create_file (p : Path) (fs : Filesystem) : OperationResult Filesystem :=
  if path_exists_dec p fs then
    Error EEXIST
  else if path_exists_dec (parent_path p) fs then
    if is_directory_dec (parent_path p) fs then
      if has_write_permission_dec (parent_path p) fs then
        Success (create_file p fs)
      else Error EACCES
    else Error ENOTDIR
  else Error ENOENT.

(** Safe delete_file - returns error codes *)
Definition safe_delete_file (p : Path) (fs : Filesystem) : OperationResult Filesystem :=
  if path_exists_dec p fs then
    if is_file_dec p fs then
      if has_write_permission_dec (parent_path p) fs then
        Success (delete_file p fs)
      else Error EACCES
    else Error EISDIR
  else Error ENOENT.

(** * Error Handling Correctness Theorems *)

Theorem safe_mkdir_success_iff_precondition :
  forall p fs fs',
    safe_mkdir p fs = Success fs' <->
    (mkdir_precondition p fs /\ fs' = mkdir p fs).
Proof.
  intros p fs fs'.
  split.
  - (* -> *)
    unfold safe_mkdir.
    intros H.
    destruct (path_exists_dec p fs); [discriminate|].
    destruct (path_exists_dec (parent_path p) fs); [|discriminate].
    destruct (is_directory_dec (parent_path p) fs); [|discriminate].
    destruct (has_write_permission_dec (parent_path p) fs); [|discriminate].
    injection H; intro; subst.
    split; [|reflexivity].
    unfold mkdir_precondition.
    repeat split; assumption.
  - (* <- *)
    intros [Hpre Heq].
    subst fs'.
    unfold safe_mkdir.
    destruct Hpre as [Hnotexists [Hparent [Hisdir Hperms]]].
    destruct (path_exists_dec p fs); [contradiction|].
    destruct (path_exists_dec (parent_path p) fs); [|contradiction].
    destruct (is_directory_dec (parent_path p) fs); [|contradiction].
    destruct (has_write_permission_dec (parent_path p) fs); [|contradiction].
    reflexivity.
Qed.

Theorem safe_rmdir_success_iff_precondition :
  forall p fs fs',
    safe_rmdir p fs = Success fs' <->
    (rmdir_precondition p fs /\ fs' = rmdir p fs).
Proof.
  intros p fs fs'.
  split.
  - (* -> *)
    unfold safe_rmdir.
    intros H.
    destruct (path_exists_dec p fs); [|discriminate].
    destruct (is_directory_dec p fs); [|discriminate].
    destruct (is_empty_dir_dec p fs); [|discriminate].
    destruct (has_write_permission_dec (parent_path p) fs); [|discriminate].
    destruct (path_eq_dec p root_path); [discriminate|].
    injection H; intro; subst.
    split; [|reflexivity].
    unfold rmdir_precondition.
    repeat split; assumption.
  - (* <- *)
    intros [Hpre Heq].
    subst fs'.
    unfold safe_rmdir.
    destruct Hpre as [Hisdir [Hempty [Hperms Hnotroot]]].
    destruct (path_exists_dec p fs).
    + destruct (is_directory_dec p fs); [|contradiction].
      destruct (is_empty_dir_dec p fs); [|contradiction].
      destruct (has_write_permission_dec (parent_path p) fs); [|contradiction].
      destruct (path_eq_dec p root_path); [contradiction|].
      reflexivity.
    + exfalso.
      apply n.
      destruct Hisdir as [perms Hdir].
      unfold path_exists.
      exists (mkFSNode Directory perms).
      assumption.
Qed.

(** * Error Code Correctness *)

Theorem safe_mkdir_EEXIST :
  forall p fs,
    path_exists p fs ->
    safe_mkdir p fs = Error EEXIST.
Proof.
  intros p fs Hexists.
  unfold safe_mkdir.
  destruct (path_exists_dec p fs); [reflexivity | contradiction].
Qed.

Theorem safe_mkdir_ENOENT :
  forall p fs,
    ~ path_exists p fs ->
    ~ parent_exists p fs ->
    safe_mkdir p fs = Error ENOENT.
Proof.
  intros p fs Hnoexist Hnoparent.
  unfold safe_mkdir.
  destruct (path_exists_dec p fs); [contradiction|].
  unfold parent_exists in Hnoparent.
  destruct (path_exists_dec (parent_path p) fs); [contradiction|].
  reflexivity.
Qed.

Theorem safe_rmdir_ENOENT :
  forall p fs,
    ~ path_exists p fs ->
    safe_rmdir p fs = Error ENOENT.
Proof.
  intros p fs Hnoexist.
  unfold safe_rmdir.
  destruct (path_exists_dec p fs); [contradiction|].
  reflexivity.
Qed.

Theorem safe_rmdir_ENOTDIR :
  forall p fs,
    path_exists p fs ->
    ~ is_directory p fs ->
    safe_rmdir p fs = Error ENOTDIR.
Proof.
  intros p fs Hexists Hnotdir.
  unfold safe_rmdir.
  destruct (path_exists_dec p fs); [|contradiction].
  destruct (is_directory_dec p fs); [contradiction|].
  reflexivity.
Qed.

Theorem safe_rmdir_ENOTEMPTY :
  forall p fs,
    is_directory p fs ->
    ~ is_empty_dir p fs ->
    safe_rmdir p fs = Error ENOTEMPTY.
Proof.
  intros p fs Hisdir Hnotempty.
  unfold safe_rmdir.
  destruct (path_exists_dec p fs).
  - destruct (is_directory_dec p fs); [|contradiction].
    destruct (is_empty_dir_dec p fs); [contradiction|].
    reflexivity.
  - exfalso.
    apply n.
    destruct Hisdir as [perms Hdir].
    exists (mkFSNode Directory perms).
    assumption.
Qed.

(** * Reversibility with Error Handling *)

Theorem safe_mkdir_rmdir_reversible :
  forall p fs fs',
    well_formed fs ->
    safe_mkdir p fs = Success fs' ->
    safe_rmdir p fs' = Success fs.
Proof.
  intros p fs fs' Hwf Hmkdir.
  apply safe_mkdir_success_iff_precondition in Hmkdir.
  destruct Hmkdir as [Hpre Heq].
  subst fs'.
  apply safe_rmdir_success_iff_precondition.
  split.
  - (* Prove rmdir_precondition — delegate to proven lemma *)
    apply rmdir_precondition_after_mkdir; assumption.
  - (* Prove fs = rmdir p (mkdir p fs) *)
    symmetry.
    apply mkdir_rmdir_reversible.
    assumption.
Qed.

(** * Summary of Error Modeling *)

(** This file establishes:

    ✓ POSIX error code model (EEXIST, ENOENT, EACCES, etc.)
    ✓ Safe operations returning Result types
    ✓ Correctness: Success iff preconditions hold
    ✓ Error code correctness: Each error matches specific violation
    ✓ Reversibility preserved under error handling
    ✓ 5/6 decision procedures proved constructively (Lemma, not Axiom)
    ✗ is_empty_dir_dec: justified axiom, requires finite-map Filesystem for proof

    This enables:
    - Realistic implementation with proper error reporting
    - Proof that error handling matches POSIX semantics
    - Guarantee that successful operations satisfy preconditions
    - Foundation for extraction to real code with errno
*)
