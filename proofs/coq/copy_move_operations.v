(** Valence Shell - Copy and Move Operations

    This module formalizes copy and move (rename) operations
    with reversibility proofs for the MAA framework.

    Key Properties:
    - Copy creates an exact duplicate
    - Move is atomic rename (preserves data)
    - Both operations are reversible under preconditions
*)

Require Import String.
Require Import List.
Require Import Bool.
Require Import Arith.
Import ListNotations.

Require Import Coq.Logic.FunctionalExtensionality.

(* Import base filesystem model *)
Require Import filesystem_model.
Require Import file_operations.
Require Import file_content_operations.

(** * Copy Operation *)

(** Precondition for file copy *)
Definition copy_file_precondition (src dst : Path) (fs : Filesystem) : Prop :=
  (* Source must exist and be a file *)
  is_file src fs /\
  (* Destination must not exist *)
  ~ path_exists dst fs /\
  (* Destination parent must exist *)
  parent_exists dst fs /\
  (* Destination parent must be a directory *)
  is_directory (parent_path dst) fs /\
  (* Must have read permission on source *)
  has_read_permission src fs /\
  (* Must have write permission on destination parent *)
  has_write_permission (parent_path dst) fs.

(** Copy file operation *)
Definition copy_file (src dst : Path) (fs : Filesystem) : Filesystem :=
  match fs src with
  | Some node => fs_update dst (Some node) fs
  | None => fs  (* No-op if source doesn't exist *)
  end.

(** * Move Operation *)

(** Helper: check if path is prefix of another *)
Definition is_prefix (p1 p2 : Path) : Prop :=
  exists suffix, p2 = p1 ++ suffix.

(** Precondition for move/rename *)
Definition move_precondition (src dst : Path) (fs : Filesystem) : Prop :=
  (* Source must exist *)
  path_exists src fs /\
  (* Destination must not exist *)
  ~ path_exists dst fs /\
  (* Destination parent must exist *)
  parent_exists dst fs /\
  (* Source and destination must be different *)
  src <> dst /\
  (* Cannot move directory into itself *)
  ~ (is_directory src fs /\ is_prefix src dst) /\
  (* Must have write permission on source parent *)
  has_write_permission (parent_path src) fs /\
  (* Must have write permission on destination parent *)
  has_write_permission (parent_path dst) fs.

(** Move operation *)
Definition move (src dst : Path) (fs : Filesystem) : Filesystem :=
  match fs src with
  | Some node =>
      let fs' := fs_update dst (Some node) fs in
      fs_update src None fs'
  | None => fs
  end.

(** * Copy Operation Theorems *)

(** Theorem: copy creates a file at destination *)
Theorem copy_file_creates_destination :
  forall src dst fs,
    copy_file_precondition src dst fs ->
    path_exists dst (copy_file src dst fs).
Proof.
  intros src dst fs [Hsrc [Hnotdst _]].
  unfold path_exists, copy_file.
  destruct Hsrc as [perms Hfile].
  rewrite Hfile.
  exists (mkFSNode File perms).
  unfold fs_update.
  destruct (list_eq_dec string_dec dst dst); [reflexivity | contradiction].
Qed.

(** Theorem: copy preserves source *)
Theorem copy_file_preserves_source :
  forall src dst fs,
    copy_file_precondition src dst fs ->
    src <> dst ->
    fs src = (copy_file src dst fs) src.
Proof.
  intros src dst fs Hpre Hneq.
  unfold copy_file.
  destruct Hpre as [[perms Hfile] _].
  rewrite Hfile.
  unfold fs_update.
  destruct (list_eq_dec String.string_dec dst src) as [Heq | Hneq_dst].
  - (* dst = src — contradicts Hneq : src <> dst *)
    symmetry in Heq. contradiction.
  - (* dst <> src — both sides equal fs src *)
    symmetry. exact Hfile.
Qed.

(** Theorem: copy creates exact duplicate of content *)
Theorem copy_file_same_content :
  forall src dst fs,
    copy_file_precondition src dst fs ->
    fs src = (copy_file src dst fs) dst.
Proof.
  intros src dst fs Hpre.
  unfold copy_file.
  destruct Hpre as [[perms Hfile] _].
  rewrite Hfile.
  unfold fs_update.
  destruct (list_eq_dec string_dec dst dst); [reflexivity | contradiction].
Qed.

(** Theorem: copy is reversible by deleting destination *)
Theorem copy_file_reversible :
  forall src dst fs,
    copy_file_precondition src dst fs ->
    delete_file dst (copy_file src dst fs) = fs.
Proof.
  intros src dst fs [Hsrc [Hnotdst Hrest]].
  unfold delete_file, copy_file.
  destruct Hsrc as [perms Hfile].
  rewrite Hfile.
  unfold fs_update.
  apply functional_extensionality.
  intros p.
  destruct (list_eq_dec string_dec dst p).
  - (* dst = p *)
    subst.
    destruct (list_eq_dec string_dec p p); [|contradiction].
    (* Destination didn't exist before, so fs p = None *)
    destruct (fs p) eqn:Hfsp.
    + (* Some f — contradicts Hnotdst *)
      exfalso. apply Hnotdst. exists f. assumption.
    + (* None — both sides are None *)
      reflexivity.
  - (* dst <> p *)
    destruct (list_eq_dec string_dec dst p); [contradiction|reflexivity].
Qed.

(** * Move Operation Theorems *)

(** Theorem: move creates path at destination *)
Theorem move_creates_destination :
  forall src dst fs,
    move_precondition src dst fs ->
    path_exists dst (move src dst fs).
Proof.
  intros src dst fs [[node Hsrc] [Hnotdst [_ [Hneq _]]]].
  unfold path_exists, move.
  rewrite Hsrc.
  exists node.
  unfold fs_update.
  destruct (list_eq_dec String.string_dec src dst) as [Heq | _].
  - (* src = dst contradicts precondition Hneq *)
    contradiction.
  - destruct (list_eq_dec String.string_dec dst dst) as [_ | Hne]; [reflexivity | contradiction].
Qed.

(** Theorem: move removes source *)
Theorem move_removes_source :
  forall src dst fs,
    move_precondition src dst fs ->
    ~ path_exists src (move src dst fs).
Proof.
  intros src dst fs Hpre [node Hexists].
  destruct Hpre as [[orig_node Hsrc] [Hnotdst [_ [Hneq _]]]].
  unfold move in Hexists.
  rewrite Hsrc in Hexists.
  unfold fs_update in Hexists.
  destruct (list_eq_dec string_dec src src); [discriminate | contradiction].
Qed.

(** Theorem: move preserves content (node is same) *)
Theorem move_preserves_content :
  forall src dst fs,
    move_precondition src dst fs ->
    fs src = (move src dst fs) dst.
Proof.
  intros src dst fs [[node Hsrc] [_ [_ [Hneq _]]]].
  unfold move.
  rewrite Hsrc.
  unfold fs_update.
  destruct (list_eq_dec String.string_dec src dst) as [Heq | _].
  - (* src = dst contradicts Hneq *)
    contradiction.
  - destruct (list_eq_dec String.string_dec dst dst) as [_ | Hne]; [reflexivity | contradiction].
Qed.

(** Theorem: move is reversible *)
Theorem move_reversible :
  forall src dst fs,
    move_precondition src dst fs ->
    move dst src (move src dst fs) = fs.
Proof.
  intros src dst fs Hpre.
  destruct Hpre as [[node Hsrc] [Hnotdst [_ [Hneq _]]]].
  (* First compute the inner move: (move src dst fs) = fs_update src None (fs_update dst (Some node) fs) *)
  assert (Hinner : move src dst fs = fs_update src None (fs_update dst (Some node) fs)).
  { unfold move. rewrite Hsrc. reflexivity. }
  rewrite Hinner.
  (* Now: move dst src (fs_update src None (fs_update dst (Some node) fs)) = fs *)
  (* Need to show (fs_update src None (fs_update dst (Some node) fs)) dst = Some node *)
  assert (Hdstnode : (fs_update src None (fs_update dst (Some node) fs)) dst = Some node).
  { unfold fs_update.
    destruct (list_eq_dec String.string_dec src dst) as [Heq | _].
    - contradiction.
    - destruct (list_eq_dec String.string_dec dst dst) as [_ | Hne_dd]; [reflexivity | contradiction]. }
  unfold move at 1.
  rewrite Hdstnode.
  apply functional_extensionality.
  intros p.
  unfold fs_update.
  destruct (list_eq_dec String.string_dec dst p) as [Hdp | Hndp].
  - (* dst = p *)
    destruct (list_eq_dec String.string_dec src p) as [Hsp | Hnsp].
    + (* src = p, but dst = p too, so src = dst — contradicts Hneq *)
      subst. contradiction.
    + (* Goal: None = fs p. Use Hnotdst: dst=p so fs p must be None to avoid path_exists *)
      destruct (fs p) eqn:Hfsp.
      * exfalso. apply Hnotdst. exists f. rewrite Hdp. assumption.
      * reflexivity.
  - destruct (list_eq_dec String.string_dec src p) as [Hsp | Hnsp].
    + (* src = p *)
      subst.
      symmetry. assumption.
    + (* neither src nor dst at p *)
      reflexivity.
Qed.

(** * Preservation Theorems *)

(** Theorem: copy preserves unrelated paths *)
Theorem copy_preserves_other_paths :
  forall src dst p fs,
    p <> dst ->
    fs p = (copy_file src dst fs) p.
Proof.
  intros src dst p fs Hneq.
  unfold copy_file.
  destruct (fs src).
  - unfold fs_update.
    destruct (list_eq_dec String.string_dec dst p) as [Heq | _].
    + symmetry in Heq. contradiction.
    + reflexivity.
  - reflexivity.
Qed.

(** Theorem: move preserves unrelated paths *)
Theorem move_preserves_other_paths :
  forall src dst p fs,
    p <> src ->
    p <> dst ->
    fs p = (move src dst fs) p.
Proof.
  intros src dst p fs Hneq_src Hneq_dst.
  unfold move.
  destruct (fs src).
  - unfold fs_update.
    destruct (list_eq_dec String.string_dec src p) as [Heq | _].
    + symmetry in Heq. contradiction.
    + destruct (list_eq_dec String.string_dec dst p) as [Heq | _].
      * symmetry in Heq. contradiction.
      * reflexivity.
  - reflexivity.
Qed.

(** * Composition Theorems *)

(** Theorem: copy then move destination = move source *)
Theorem copy_then_move :
  forall src dst dst2 fs,
    copy_file_precondition src dst fs ->
    move_precondition dst dst2 (copy_file src dst fs) ->
    (move dst dst2 (copy_file src dst fs)) dst2 = fs src.
Proof.
  intros src dst dst2 fs Hcopy Hmove.
  rewrite <- (move_preserves_content dst dst2 (copy_file src dst fs) Hmove).
  symmetry. apply copy_file_same_content. assumption.
Qed.

(** * Summary of Proven Claims *)

(** This module establishes:

    Copy Operations:
    ✓ copy_file_creates_destination
    ✓ copy_file_preserves_source
    ✓ copy_file_same_content
    ✓ copy_file_reversible
    ✓ copy_preserves_other_paths

    Move Operations:
    ✓ move_creates_destination
    ✓ move_removes_source
    ✓ move_preserves_content
    ✓ move_reversible
    ✓ move_preserves_other_paths

    Composition:
    ✓ copy_then_move
*)
