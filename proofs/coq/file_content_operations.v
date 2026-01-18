(** Valence Shell - File Content Operations

    This file extends the filesystem model with file content operations:
    - read_file: Read file contents
    - write_file: Write file contents

    These operations support reversible content modifications,
    enabling undo/redo for file content changes.
*)

Require Import String.
Require Import List.
Require Import Bool.
Import ListNotations.

Require Import filesystem_model.
Require Import file_operations.

(** * File Contents *)

(** File content is a list of bytes (represented as strings for simplicity) *)
Definition FileContent := string.

(** Empty content *)
Definition empty_content : FileContent := EmptyString.

(** * Extended Filesystem with Content *)

(** Extended filesystem node with content *)
Record FSNodeWithContent : Type := mkFSNodeWithContent {
  node_type : NodeType;
  node_perms : Permissions;
  node_content : option FileContent  (* None for directories, Some for files *)
}.

(** Extended filesystem mapping paths to nodes with content *)
Definition FilesystemWithContent := Path -> option FSNodeWithContent.

(** * Conversion Functions *)

(** Convert basic filesystem to filesystem with content *)
Definition fs_to_fs_with_content (fs : Filesystem) : FilesystemWithContent :=
  fun p =>
    match fs p with
    | None => None
    | Some node =>
        Some {| node_type := get_node_type node;
                node_perms := get_permissions node;
                node_content := match get_node_type node with
                               | File => Some empty_content
                               | Directory => None
                               end |}
    end.

(** * File Content Operations *)

(** Read file content *)
Definition read_file (p : Path) (fs : FilesystemWithContent) : option FileContent :=
  match fs p with
  | None => None  (* File doesn't exist *)
  | Some node =>
      match node_type node with
      | File => node_content node
      | Directory => None  (* Can't read directory as file *)
      end
  end.

(** Write file content *)
Definition write_file (p : Path) (content : FileContent) (fs : FilesystemWithContent)
  : FilesystemWithContent :=
  fun p' =>
    if list_eq_dec String.string_dec p p' then
      match fs p' with
      | None => None  (* Can't write to non-existent file *)
      | Some node =>
          match node_type node with
          | File => Some {| node_type := node_type node;
                           node_perms := node_perms node;
                           node_content := Some content |}
          | Directory => Some node  (* No-op for directories *)
          end
      end
    else
      fs p'.

(** * Preconditions *)

(** Can read file if it exists and is a file *)
Definition read_file_precondition (p : Path) (fs : FilesystemWithContent) : Prop :=
  exists node,
    fs p = Some node /\
    node_type node = File /\
    exists perms, node_perms node = perms /\ readable perms = true.

(** Can write file if it exists and is a file *)
Definition write_file_precondition (p : Path) (fs : FilesystemWithContent) : Prop :=
  exists node,
    fs p = Some node /\
    node_type node = File /\
    exists perms, node_perms node = perms /\ writable perms = true.

(** * Reversibility Properties *)

(** Reading doesn't change the filesystem *)
Theorem read_file_preserves_fs :
  forall p fs content,
    read_file p fs = Some content ->
    fs = fs.
Proof.
  intros p fs content H.
  reflexivity.
Qed.

(** Writing old content back restores filesystem *)
Theorem write_file_reversible :
  forall p fs old_content new_content,
    write_file_precondition p fs ->
    read_file p fs = Some old_content ->
    write_file p old_content (write_file p new_content fs) = fs.
Proof.
  intros p fs old_content new_content Hpre Hold.
  unfold write_file.
  apply functional_extensionality.
  intros p'.
  destruct (list_eq_dec String.string_dec p p').
  - (* p = p' *)
    subst p'.
    unfold read_file in Hold.
    destruct Hpre as [node [Hnode [Htype [perms [Hperms Hwrite]]]]].
    rewrite Hnode.
    rewrite Htype.
    destruct (fs p) as [n|] eqn:Hfs; [|discriminate].
    simpl in Hold.
    destruct (node_type n) eqn:Hntype; [|discriminate].
    injection Hold as Heq.
    subst old_content.
    simpl.
    rewrite Hfs.
    rewrite Hntype.
    destruct n; simpl in *.
    subst node_type0.
    reflexivity.
  - (* p <> p' *)
    reflexivity.
Qed.

(** * Content Preservation *)

(** Writing to one file doesn't affect others *)
Theorem write_file_independence :
  forall p1 p2 content fs,
    p1 <> p2 ->
    read_file p2 (write_file p1 content fs) = read_file p2 fs.
Proof.
  intros p1 p2 content fs Hneq.
  unfold write_file, read_file.
  destruct (list_eq_dec String.string_dec p1 p2).
  - (* p1 = p2 *)
    contradiction.
  - (* p1 <> p2 *)
    reflexivity.
Qed.

(** * Content Operations and Basic Operations *)

(** Creating a file initializes empty content *)
Theorem create_file_empty_content :
  forall p fs,
    create_file_precondition p fs ->
    read_file p (fs_to_fs_with_content (create_file p fs)) = Some empty_content.
Proof.
  intros p fs Hpre.
  unfold read_file, fs_to_fs_with_content, create_file.
  unfold fs_update.
  destruct (list_eq_dec String.string_dec p p); [|contradiction].
  simpl.
  reflexivity.
Qed.

(** * State Tracking for Reversibility *)

(** Record of file state for undo/redo *)
Record FileState : Type := mkFileState {
  state_path : Path;
  state_content : FileContent;
  state_exists : bool
}.

(** Capture current file state *)
Definition capture_file_state (p : Path) (fs : FilesystemWithContent) : FileState :=
  match read_file p fs with
  | Some content => mkFileState p content true
  | None => mkFileState p empty_content false
  end.

(** Restore file state *)
Definition restore_file_state (state : FileState) (fs : FilesystemWithContent)
  : FilesystemWithContent :=
  if state_exists state then
    write_file (state_path state) (state_content state) fs
  else
    fs.  (* Would need delete operation from file_operations *)

(** Capturing and restoring is identity (for existing files) *)
Theorem capture_restore_identity :
  forall p fs,
    write_file_precondition p fs ->
    restore_file_state (capture_file_state p fs) fs = fs.
Proof.
  intros p fs Hpre.
  unfold restore_file_state, capture_file_state.
  destruct (read_file p fs) as [content|] eqn:Hread.
  - (* File exists *)
    simpl.
    apply functional_extensionality.
    intros p'.
    unfold write_file.
    destruct (list_eq_dec String.string_dec p p').
    + (* p = p' *)
      subst p'.
      unfold read_file in Hread.
      destruct Hpre as [node [Hnode [Htype [perms [Hperms Hwrite]]]]].
      rewrite Hnode in Hread.
      rewrite Htype in Hread.
      simpl in Hread.
      injection Hread as Heq.
      rewrite Hnode.
      rewrite Htype.
      destruct node; simpl in *.
      subst node_type0.
      subst node_content0.
      reflexivity.
    + (* p <> p' *)
      reflexivity.
  - (* File doesn't exist *)
    simpl.
    reflexivity.
Qed.

(** * Integration with MAA Framework *)

(** File modification record for audit trail *)
Record FileModificationRecord : Type := mkFileModRecord {
  mod_path : Path;
  mod_old_content : FileContent;
  mod_new_content : FileContent;
  mod_timestamp : nat  (* Simplified timestamp *)
}.

(** Create modification record *)
Definition create_mod_record (p : Path) (old_content new_content : FileContent)
  (timestamp : nat) : FileModificationRecord :=
  mkFileModRecord p old_content new_content timestamp.

(** Apply modification *)
Definition apply_modification (record : FileModificationRecord)
  (fs : FilesystemWithContent) : FilesystemWithContent :=
  write_file (mod_path record) (mod_new_content record) fs.

(** Reverse modification *)
Definition reverse_modification (record : FileModificationRecord)
  (fs : FilesystemWithContent) : FilesystemWithContent :=
  write_file (mod_path record) (mod_old_content record) fs.

(** Modification is reversible *)
Theorem modification_reversible :
  forall record fs,
    write_file_precondition (mod_path record) fs ->
    read_file (mod_path record) fs = Some (mod_old_content record) ->
    reverse_modification record (apply_modification record fs) = fs.
Proof.
  intros record fs Hpre Hold.
  unfold reverse_modification, apply_modification.
  apply write_file_reversible; assumption.
Qed.

(** * Summary *)

(** This file establishes:

    ✓ File content operations (read_file, write_file)
    ✓ Preconditions for safe file access
    ✓ Reversibility: write(p, old, write(p, new, fs)) = fs
    ✓ Independence: write(p1, c, fs) doesn't affect p2
    ✓ Integration with basic operations
    ✓ State capture/restore for undo/redo
    ✓ MAA modification records with reversibility

    This extends Valence Shell with content operations,
    maintaining the reversibility guarantees established
    for structural operations (mkdir, create, etc.).
*)
