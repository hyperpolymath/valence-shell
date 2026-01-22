(** Valence Shell - Symlink Operations

    Abstract model of symbolic link creation and removal.
    In this model, a symlink is represented as a file node with default
    permissions; the target path is modeled externally.
*)

Require Import String.
Require Import List.
Import ListNotations.

Require Import filesystem_model.

(** * Symlink Operations *)

(** Preconditions for creating a symlink *)
Definition symlink_precondition (p : Path) (fs : Filesystem) : Prop :=
  ~ path_exists p fs /\
  parent_exists p fs /\
  is_directory (parent_path p) fs /\
  has_write_permission (parent_path p) fs.

(** Create a symlink at path p (modeled as a file node) *)
Definition symlink (p : Path) (fs : Filesystem) : Filesystem :=
  fs_update p (Some (mkFSNode File default_perms)) fs.

(** Remove a symlink at path p *)
Definition unlink (p : Path) (fs : Filesystem) : Filesystem :=
  fs_update p None fs.

(** * Postcondition Lemmas *)

Theorem symlink_creates_path :
  forall p fs,
    symlink_precondition p fs ->
    path_exists p (symlink p fs).
Proof.
  intros p fs Hpre.
  unfold path_exists, symlink, fs_update.
  exists (mkFSNode File default_perms).
  destruct (list_eq_dec String.string_dec p p); [reflexivity | contradiction].
Qed.

Theorem unlink_removes_path :
  forall p fs,
    path_exists p fs ->
    ~ path_exists p (unlink p fs).
Proof.
  intros p fs Hexists [node Hnode].
  unfold unlink, fs_update in Hnode.
  destruct (list_eq_dec String.string_dec p p); discriminate.
Qed.

(** * Reversibility Theorem *)

Theorem symlink_unlink_reversible :
  forall p fs,
    symlink_precondition p fs ->
    unlink p (symlink p fs) = fs.
Proof.
  intros p fs Hpre.
  unfold unlink, symlink, fs_update.
  apply functional_extensionality.
  intros p'.
  destruct (list_eq_dec String.string_dec p p').
  - subst p'.
    destruct Hpre as [Hnotexists _].
    destruct (fs p) as [node|] eqn:Hfs.
    + exfalso.
      apply Hnotexists.
      exists node; exact Hfs.
    + reflexivity.
  - reflexivity.
Qed.

(** * Summary *)

(** This file establishes:

    ✓ Symlink creation and removal operations
    ✓ Preconditions for safe symlink creation
    ✓ Reversibility: unlink(symlink(p, fs)) = fs
*)
