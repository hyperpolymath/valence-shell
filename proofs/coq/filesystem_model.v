(** Valence Shell - Filesystem Model

    A formal model of POSIX-like filesystem operations for proving
    MAA (Mutually Assured Accountability) properties.

    This model focuses on directory operations (mkdir/rmdir) with
    the goal of proving reversibility and correctness properties.
*)

Require Import String.
Require Import List.
Require Import Bool.
Require Import Arith.
Import ListNotations.

(** * Path Model *)

(** Paths are sequences of path components (directory/file names) *)
Definition PathComponent := string.
Definition Path := list PathComponent.

(** Root path *)
Definition root_path : Path := [].

(** Path operations *)
Definition parent_path (p : Path) : Path :=
  match rev p with
  | [] => []
  | _ :: rest => rev rest
  end.

Definition path_name (p : Path) : option PathComponent :=
  match rev p with
  | [] => None
  | name :: _ => Some name
  end.

Fixpoint path_prefix (p1 p2 : Path) : bool :=
  match p1, p2 with
  | [], _ => true
  | _, [] => false
  | x :: xs, y :: ys => if String.eqb x y then path_prefix xs ys else false
  end.

(** * Filesystem Nodes *)

(** File system nodes can be either files or directories *)
Inductive FSNodeType : Type :=
  | File : FSNodeType
  | Directory : FSNodeType.

(** Permissions model (simplified) *)
Record Permissions : Type := mkPermissions {
  readable : bool;
  writable : bool;
  executable : bool
}.

Definition default_perms : Permissions := mkPermissions true true true.

(** Filesystem node *)
Record FSNode : Type := mkFSNode {
  node_type : FSNodeType;
  permissions : Permissions
}.

(** * Filesystem State *)

(** A filesystem is a partial mapping from paths to nodes *)
Definition Filesystem := Path -> option FSNode.

(** Empty filesystem (only root exists) *)
Definition empty_fs : Filesystem :=
  fun p => match p with
           | [] => Some (mkFSNode Directory default_perms)
           | _ => None
           end.

(** * Filesystem Predicates *)

(** Path exists in filesystem *)
Definition path_exists (p : Path) (fs : Filesystem) : Prop :=
  exists node, fs p = Some node.

(** Path is a directory *)
Definition is_directory (p : Path) (fs : Filesystem) : Prop :=
  exists perms, fs p = Some (mkFSNode Directory perms).

(** Path is a file *)
Definition is_file (p : Path) (fs : Filesystem) : Prop :=
  exists perms, fs p = Some (mkFSNode File perms).

(** Parent directory exists *)
Definition parent_exists (p : Path) (fs : Filesystem) : Prop :=
  path_exists (parent_path p) fs.

(** Path has write permission *)
Definition has_write_permission (p : Path) (fs : Filesystem) : Prop :=
  exists node, fs p = Some node /\ writable (permissions node) = true.

(** Directory is empty (has no children) *)
Definition is_empty_dir (p : Path) (fs : Filesystem) : Prop :=
  is_directory p fs /\
  forall child : Path,
    path_prefix p child ->
    child <> p ->
    ~ path_exists child fs.

(** * Basic Lemmas *)

Lemma path_exists_empty_fs_root :
  path_exists root_path empty_fs.
Proof.
  unfold path_exists, empty_fs.
  exists (mkFSNode Directory default_perms).
  reflexivity.
Qed.

Lemma not_path_exists_empty_fs :
  forall p, p <> root_path -> ~ path_exists p empty_fs.
Proof.
  intros p Hneq [node Hexists].
  unfold empty_fs in Hexists.
  destruct p; [contradiction | discriminate].
Qed.

(** * Filesystem Operations *)

(** Update filesystem at a specific path *)
Definition fs_update (p : Path) (n : option FSNode) (fs : Filesystem) : Filesystem :=
  fun p' => if list_eq_dec String.string_dec p p' then n else fs p'.

(** mkdir: Create a directory
    Preconditions:
    - Path does not already exist
    - Parent directory exists
    - Parent has write permission
*)
Definition mkdir_precondition (p : Path) (fs : Filesystem) : Prop :=
  ~ path_exists p fs /\
  parent_exists p fs /\
  is_directory (parent_path p) fs /\
  has_write_permission (parent_path p) fs.

Definition mkdir (p : Path) (fs : Filesystem) : Filesystem :=
  fs_update p (Some (mkFSNode Directory default_perms)) fs.

(** rmdir: Remove a directory
    Preconditions:
    - Path exists and is a directory
    - Directory is empty
    - Parent has write permission
*)
Definition rmdir_precondition (p : Path) (fs : Filesystem) : Prop :=
  is_directory p fs /\
  is_empty_dir p fs /\
  has_write_permission (parent_path p) fs /\
  p <> root_path.  (* Cannot remove root *)

Definition rmdir (p : Path) (fs : Filesystem) : Filesystem :=
  fs_update p None fs.

(** * Postcondition Lemmas *)

Theorem mkdir_creates_directory :
  forall p fs,
    mkdir_precondition p fs ->
    is_directory p (mkdir p fs).
Proof.
  intros p fs [Hnotexists [Hparent [Hparentdir Hperms]]].
  unfold is_directory, mkdir, fs_update.
  exists default_perms.
  destruct (list_eq_dec String.string_dec p p); [reflexivity | contradiction].
Qed.

Theorem mkdir_path_exists :
  forall p fs,
    mkdir_precondition p fs ->
    path_exists p (mkdir p fs).
Proof.
  intros p fs Hpre.
  unfold path_exists.
  exists (mkFSNode Directory default_perms).
  unfold mkdir, fs_update.
  destruct (list_eq_dec String.string_dec p p); [reflexivity | contradiction].
Qed.

Theorem rmdir_removes_path :
  forall p fs,
    rmdir_precondition p fs ->
    ~ path_exists p (rmdir p fs).
Proof.
  intros p fs Hpre [node Hexists].
  unfold rmdir, fs_update in Hexists.
  destruct (list_eq_dec String.string_dec p p); discriminate.
Qed.

(** * The Main Reversibility Theorem *)

Theorem mkdir_rmdir_reversible :
  forall p fs,
    mkdir_precondition p fs ->
    rmdir (p) (mkdir p fs) = fs.
Proof.
  intros p fs Hpre.
  unfold rmdir, mkdir.
  unfold fs_update.
  apply functional_extensionality.
  intros p'.
  destruct (list_eq_dec String.string_dec p p').
  - (* p = p' *)
    subst.
    destruct (list_eq_dec String.string_dec p' p'); [|contradiction].
    destruct Hpre as [Hnotexists _].
    destruct Hnotexists.
    assumption.
  - (* p <> p' *)
    destruct (list_eq_dec String.string_dec p p'); [contradiction|].
    reflexivity.
Qed.

(** * Additional Theorems *)

Theorem mkdir_preserves_other_paths :
  forall p p' fs,
    p <> p' ->
    fs p' = (mkdir p fs) p'.
Proof.
  intros p p' fs Hneq.
  unfold mkdir, fs_update.
  destruct (list_eq_dec String.string_dec p p'); [contradiction | reflexivity].
Qed.

Theorem rmdir_preserves_other_paths :
  forall p p' fs,
    p <> p' ->
    fs p' = (rmdir p fs) p'.
Proof.
  intros p p' fs Hneq.
  unfold rmdir, fs_update.
  destruct (list_eq_dec String.string_dec p p'); [contradiction | reflexivity].
Qed.

Theorem mkdir_parent_still_exists :
  forall p fs,
    mkdir_precondition p fs ->
    path_exists (parent_path p) (mkdir p fs).
Proof.
  intros p fs [_ [Hparent _]].
  unfold path_exists in *.
  destruct Hparent as [node Hnode].
  exists node.
  unfold mkdir, fs_update.
  destruct (list_eq_dec String.string_dec p (parent_path p)).
  - (* This would mean p = parent p, impossible for non-root *)
    admit. (* Need to prove parent_path p <> p for non-root paths *)
  - assumption.
Admitted.

(** Helper axiom for functional extensionality
    In real development, import from Coq.Logic.FunctionalExtensionality *)
Axiom functional_extensionality : forall {A B : Type} (f g : A -> B),
  (forall x, f x = g x) -> f = g.
