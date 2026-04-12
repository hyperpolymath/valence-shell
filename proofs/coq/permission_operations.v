(* SPDX-License-Identifier: PMPL-1.0-or-later *)
(** Valence Shell - Permission Operations

    Formalizes chmod and chown as reversible operations.
    Proves that applying the old permission/ownership after a change
    restores the original filesystem state.
*)

Require Import String.
Require Import List.
Require Import Bool.
Require Import Arith.
Import ListNotations.

Require Import Coq.Logic.FunctionalExtensionality.

Require Import filesystem_model.

(** * Extended Types for Permission/Ownership *)

(** Unix permission mode (lower 12 bits of mode_t) *)
Definition Mode := nat.

(** Unix user/group IDs *)
Record Ownership : Type := mkOwnership {
  uid : nat;
  gid : nat
}.

(** Extended filesystem node with separate mode and ownership *)
Record FSNodeExt : Type := mkFSNodeExt {
  ext_nodeType : FSNodeType;
  ext_mode : Mode;
  ext_owner : Ownership
}.

(** Extended filesystem *)
Definition FilesystemExt := Path -> option FSNodeExt.

(** * chmod Operation *)

(** chmod precondition: path must exist *)
Definition chmod_precondition (p : Path) (fs : FilesystemExt) : Prop :=
  exists node, fs p = Some node.

(** Apply chmod: change mode bits of a file *)
Definition chmod (p : Path) (newMode : Mode) (fs : FilesystemExt) : FilesystemExt :=
  fun p' =>
    if list_eq_dec String.string_dec p p' then
      match fs p' with
      | None => None
      | Some node => Some (mkFSNodeExt (ext_nodeType node) newMode (ext_owner node))
      end
    else
      fs p'.

(** * chmod Theorems *)

(** chmod is reversible — restoring old mode restores fs *)
Theorem chmod_reversible :
  forall p fs oldMode newMode,
    (exists node, fs p = Some node /\ ext_mode node = oldMode) ->
    chmod p oldMode (chmod p newMode fs) = fs.
Proof.
  intros p fs oldMode newMode [node [Hnode Hmode]].
  apply functional_extensionality.
  intros p'.
  unfold chmod.
  destruct (list_eq_dec String.string_dec p p').
  - subst p'.
    rewrite Hnode. simpl.
    destruct (list_eq_dec String.string_dec p p); [| contradiction].
    simpl.
    destruct node as [nt m o].
    simpl in Hmode. subst m.
    reflexivity.
  - reflexivity.
Qed.

(** chmod to same mode is identity *)
Theorem chmod_same_mode :
  forall p fs m,
    (exists node, fs p = Some node /\ ext_mode node = m) ->
    chmod p m fs = fs.
Proof.
  intros p fs m [node [Hnode Hmode]].
  apply functional_extensionality.
  intros p'.
  unfold chmod.
  destruct (list_eq_dec String.string_dec p p').
  - subst p'.
    rewrite Hnode.
    destruct node as [nt md o].
    simpl in Hmode. subst md.
    reflexivity.
  - reflexivity.
Qed.

(** chmod at different paths commute *)
Theorem chmod_commute :
  forall p1 p2 fs m1 m2,
    p1 <> p2 ->
    chmod p1 m1 (chmod p2 m2 fs) = chmod p2 m2 (chmod p1 m1 fs).
Proof.
  intros p1 p2 fs m1 m2 Hneq.
  apply functional_extensionality.
  intros p'.
  unfold chmod.
  destruct (list_eq_dec String.string_dec p1 p') as [Heq1 | Hneq1];
  destruct (list_eq_dec String.string_dec p2 p') as [Heq2 | Hneq2].
  - (* p1 = p' = p2 → p1 = p2, contradicts Hneq *)
    exfalso. exact (Hneq (eq_trans Heq1 (eq_sym Heq2))).
  - (* p1 = p', p2 ≠ p' *) reflexivity.
  - (* p1 ≠ p', p2 = p' *) reflexivity.
  - (* p1 ≠ p', p2 ≠ p' *) reflexivity.
Qed.

(** chmod preserves other paths *)
Theorem chmod_preserves_other :
  forall p1 p2 fs m,
    p1 <> p2 ->
    (chmod p1 m fs) p2 = fs p2.
Proof.
  intros p1 p2 fs m Hneq.
  unfold chmod.
  destruct (list_eq_dec String.string_dec p1 p2); [contradiction | reflexivity].
Qed.

(** * chown Operation *)

(** chown precondition: path must exist *)
Definition chown_precondition (p : Path) (fs : FilesystemExt) : Prop :=
  exists node, fs p = Some node.

(** Apply chown: change ownership of a file *)
Definition chown (p : Path) (newOwner : Ownership) (fs : FilesystemExt) : FilesystemExt :=
  fun p' =>
    if list_eq_dec String.string_dec p p' then
      match fs p' with
      | None => None
      | Some node => Some (mkFSNodeExt (ext_nodeType node) (ext_mode node) newOwner)
      end
    else
      fs p'.

(** * chown Theorems *)

(** chown is reversible — restoring old owner restores fs *)
Theorem chown_reversible :
  forall p fs oldOwner newOwner,
    (exists node, fs p = Some node /\ ext_owner node = oldOwner) ->
    chown p oldOwner (chown p newOwner fs) = fs.
Proof.
  intros p fs oldOwner newOwner [node [Hnode Howner]].
  apply functional_extensionality.
  intros p'.
  unfold chown.
  destruct (list_eq_dec String.string_dec p p').
  - subst p'.
    rewrite Hnode. simpl.
    destruct (list_eq_dec String.string_dec p p) as [_ | Hnn]; [| exfalso; exact (Hnn eq_refl)].
    simpl.
    destruct node as [nt m o].
    simpl in Howner. subst o.
    reflexivity.
  - reflexivity.
Qed.

(** chown to same owner is identity *)
Theorem chown_same_owner :
  forall p fs o,
    (exists node, fs p = Some node /\ ext_owner node = o) ->
    chown p o fs = fs.
Proof.
  intros p fs o [node [Hnode Howner]].
  apply functional_extensionality.
  intros p'.
  unfold chown.
  destruct (list_eq_dec String.string_dec p p').
  - subst p'.
    rewrite Hnode.
    destruct node as [nt m ow].
    simpl in Howner. subst ow.
    reflexivity.
  - reflexivity.
Qed.

(** chmod and chown commute (they modify different fields) *)
Theorem chmod_chown_commute :
  forall p fs m o,
    chmod p m (chown p o fs) = chown p o (chmod p m fs).
Proof.
  intros p fs m o.
  apply functional_extensionality.
  intros p'.
  unfold chmod, chown.
  destruct (list_eq_dec String.string_dec p p').
  - subst p'.
    destruct (fs p) as [node|] eqn:Hfs; reflexivity.
  - reflexivity.
Qed.

(** chown preserves other paths *)
Theorem chown_preserves_other :
  forall p1 p2 fs o,
    p1 <> p2 ->
    (chown p1 o fs) p2 = fs p2.
Proof.
  intros p1 p2 fs o Hneq.
  unfold chown.
  destruct (list_eq_dec String.string_dec p1 p2); [contradiction | reflexivity].
Qed.

(** * Summary *)

(** This file establishes:

    ✓ chmod_reversible — chmod(old, chmod(new, fs)) = fs
    ✓ chmod_same_mode — chmod with same mode is identity
    ✓ chmod_commute — chmod at different paths commutes
    ✓ chmod_preserves_other — chmod preserves unrelated paths
    ✓ chown_reversible — chown(old, chown(new, fs)) = fs
    ✓ chown_same_owner — chown with same owner is identity
    ✓ chmod_chown_commute — chmod and chown at same path commute
    ✓ chown_preserves_other — chown preserves unrelated paths
*)
