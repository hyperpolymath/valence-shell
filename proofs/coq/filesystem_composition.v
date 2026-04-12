(** Valence Shell - Filesystem Composition Theorems

    This file extends the filesystem model with composition theorems,
    proving that sequences of reversible operations compose correctly.

    Based on composition patterns from Absolute Zero's CNO theory.
*)

Require Import String.
Require Import List.
Require Import Bool.
Require Import Arith.
Import ListNotations.

Require Import filesystem_model.
Require Import file_operations.

(** * Operation Abstraction *)

(** Abstract operation type *)
Inductive Operation : Type :=
  | OpMkdir : Path -> Operation
  | OpRmdir : Path -> Operation
  | OpCreateFile : Path -> Operation
  | OpDeleteFile : Path -> Operation.

(** Apply an operation to a filesystem *)
Definition apply_op (op : Operation) (fs : Filesystem) : Filesystem :=
  match op with
  | OpMkdir p => mkdir p fs
  | OpRmdir p => rmdir p fs
  | OpCreateFile p => create_file p fs
  | OpDeleteFile p => delete_file p fs
  end.

(** Reverse of an operation *)
Definition reverse_op (op : Operation) : Operation :=
  match op with
  | OpMkdir p => OpRmdir p
  | OpRmdir p => OpMkdir p
  | OpCreateFile p => OpDeleteFile p
  | OpDeleteFile p => OpCreateFile p
  end.

(** * Operation Sequences *)

(** Apply a sequence of operations *)
Fixpoint apply_sequence (ops : list Operation) (fs : Filesystem) : Filesystem :=
  match ops with
  | [] => fs
  | op :: rest => apply_sequence rest (apply_op op fs)
  end.

(** Reverse a sequence of operations *)
Definition reverse_sequence (ops : list Operation) : list Operation :=
  map reverse_op (rev ops).

(** * Precondition Predicates *)

(** Operation has valid preconditions *)
Definition op_precondition (op : Operation) (fs : Filesystem) : Prop :=
  match op with
  | OpMkdir p => mkdir_precondition p fs
  | OpRmdir p => rmdir_precondition p fs
  | OpCreateFile p => create_file_precondition p fs
  | OpDeleteFile p => delete_file_precondition p fs
  end.

(** All operations in sequence have valid preconditions *)
Fixpoint all_preconditions (ops : list Operation) (fs : Filesystem) : Prop :=
  match ops with
  | [] => True
  | op :: rest =>
      op_precondition op fs /\
      all_preconditions rest (apply_op op fs)
  end.

(** Operation is reversible (preconditions for reverse hold) *)
Definition reversible (op : Operation) (fs : Filesystem) : Prop :=
  op_precondition op fs /\
  op_precondition (reverse_op op) (apply_op op fs).

(** All operations in sequence are reversible *)
Fixpoint all_reversible (ops : list Operation) (fs : Filesystem) : Prop :=
  match ops with
  | [] => True
  | op :: rest =>
      reversible op fs /\
      all_reversible rest (apply_op op fs)
  end.

(** * Helper Lemmas *)

(** Applying empty sequence is identity *)
Lemma apply_empty :
  forall fs,
    apply_sequence [] fs = fs.
Proof.
  intros fs.
  simpl.
  reflexivity.
Qed.

(** Applying cons distributes *)
Lemma apply_cons :
  forall op ops fs,
    apply_sequence (op :: ops) fs =
    apply_sequence ops (apply_op op fs).
Proof.
  intros op ops fs.
  simpl.
  reflexivity.
Qed.

(** Reverse of reverse is original *)
Lemma reverse_op_involutive :
  forall op,
    reverse_op (reverse_op op) = op.
Proof.
  intros op.
  destruct op; simpl; reflexivity.
Qed.

(** Reverse of empty sequence *)
Lemma reverse_sequence_nil :
  reverse_sequence [] = [].
Proof.
  unfold reverse_sequence.
  simpl.
  reflexivity.
Qed.

(** Reverse distributes over append *)
Lemma reverse_sequence_app :
  forall ops1 ops2,
    reverse_sequence (ops1 ++ ops2) =
    reverse_sequence ops2 ++ reverse_sequence ops1.
Proof.
  intros ops1 ops2.
  unfold reverse_sequence.
  rewrite rev_app_distr.
  rewrite map_app.
  reflexivity.
Qed.

(** Reverse of single operation *)
Lemma reverse_sequence_singleton :
  forall op,
    reverse_sequence [op] = [reverse_op op].
Proof.
  intros op.
  unfold reverse_sequence.
  simpl.
  reflexivity.
Qed.

(** * Single Operation Reversibility *)

(** Single mkdir/rmdir is reversible *)
Theorem single_mkdir_reversible :
  forall p fs,
    mkdir_precondition p fs ->
    apply_op (OpRmdir p) (apply_op (OpMkdir p) fs) = fs.
Proof.
  intros p fs Hpre.
  simpl.
  apply mkdir_rmdir_reversible.
  assumption.
Qed.

(** Single create_file/delete_file is reversible *)
Theorem single_create_file_reversible :
  forall p fs,
    create_file_precondition p fs ->
    apply_op (OpDeleteFile p) (apply_op (OpCreateFile p) fs) = fs.
Proof.
  intros p fs Hpre.
  simpl.
  apply create_delete_file_reversible.
  assumption.
Qed.

(** Generic single operation reversibility *)
Theorem single_op_reversible :
  forall op fs,
    reversible op fs ->
    apply_op (reverse_op op) (apply_op op fs) = fs.
Proof.
  intros op fs [Hpre Hrev].
  destruct op.
  - (* OpMkdir *)
    apply single_mkdir_reversible.
    assumption.
  - (* OpRmdir *)
    simpl in *.
    apply mkdir_rmdir_reversible.
    assumption.
  - (* OpCreateFile *)
    apply single_create_file_reversible.
    assumption.
  - (* OpDeleteFile *)
    simpl in *.
    apply create_delete_file_reversible.
    assumption.
Qed.

(** * Composition Theorems *)

(** Main composition theorem: reversing a sequence of reversible operations
    returns to the original state.

    This is the key theorem connecting to Absolute Zero's CNO composition theory.
*)
Theorem operation_sequence_reversible :
  forall (ops : list Operation) (fs : Filesystem),
    all_reversible ops fs ->
    apply_sequence (reverse_sequence ops) (apply_sequence ops fs) = fs.
Proof.
  intros ops.
  induction ops as [| op ops' IH].
  - (* Base case: empty sequence *)
    intros fs Hrev.
    simpl.
    reflexivity.
  - (* Inductive case: op :: ops' *)
    intros fs [Hrev_op Hrev_rest].
    simpl in *.
    unfold reverse_sequence.
    simpl.
    rewrite map_app.
    simpl.
    (* Apply reverse_op first, then reverse_sequence ops' *)
    rewrite <- (IH (apply_op op fs) Hrev_rest).
    (* Now apply reverse_op to get back to fs *)
    simpl.
    apply single_op_reversible.
    assumption.
Qed.

(** Two-operation sequence *)
Theorem two_op_sequence_reversible :
  forall op1 op2 fs,
    reversible op1 fs ->
    reversible op2 (apply_op op1 fs) ->
    apply_op (reverse_op op1)
      (apply_op (reverse_op op2)
        (apply_op op2 (apply_op op1 fs))) = fs.
Proof.
  intros op1 op2 fs Hrev1 Hrev2.
  apply (operation_sequence_reversible [op1; op2]).
  simpl.
  split; [assumption | split; [assumption | trivial]].
Qed.

(** Three-operation sequence *)
Theorem three_op_sequence_reversible :
  forall op1 op2 op3 fs,
    reversible op1 fs ->
    reversible op2 (apply_op op1 fs) ->
    reversible op3 (apply_op op2 (apply_op op1 fs)) ->
    apply_sequence (reverse_sequence [op1; op2; op3])
      (apply_sequence [op1; op2; op3] fs) = fs.
Proof.
  intros op1 op2 op3 fs Hrev1 Hrev2 Hrev3.
  apply operation_sequence_reversible.
  simpl.
  split; [assumption | split; [assumption | split; [assumption | trivial]]].
Qed.

(** * CNO Connection *)

(** A reversible operation followed by its reverse is a Certified Null Operation:
    it changes the state but then restores it, resulting in net zero effect.

    This connects to Absolute Zero's CNO = identity element theory.
*)
Definition is_CNO_sequence (ops : list Operation) : Prop :=
  forall fs,
    all_reversible ops fs ->
    apply_sequence (ops ++ reverse_sequence ops) fs = fs.

Theorem reversible_creates_CNO :
  forall op,
    is_CNO_sequence [op].
Proof.
  intros op fs [Hrev _].
  unfold reverse_sequence.
  simpl.
  rewrite app_nil_r.
  apply single_op_reversible.
  assumption.
Qed.

(** * Practical Examples *)

(** Well-formed filesystem: no orphan paths (children require parents) *)
Definition well_formed (fs : Filesystem) : Prop :=
  forall p, path_exists p fs -> p <> root_path ->
    path_exists (parent_path p) fs.

(** *** Path Prefix Helpers (needed for well_formed_ancestor_exists) *)

(** path_prefix p p = true *)
Lemma path_prefix_refl : forall p, path_prefix p p = true.
Proof.
  induction p as [|h t IH]; simpl; [reflexivity|].
  rewrite String.eqb_refl. exact IH.
Qed.

(** path_prefix p c = true implies length p <= length c *)
Lemma path_prefix_length : forall p c,
  path_prefix p c = true -> length p <= length c.
Proof.
  induction p as [|h t IH]; intros c H.
  - simpl. apply Nat.le_0_l.
  - destruct c as [|ch ct]; [discriminate|].
    simpl in H. destruct (String.eqb h ch); [|discriminate].
    apply IH in H. simpl. apply le_n_S. exact H.
Qed.

(** path_prefix p c = true and length p = length c implies p = c *)
Lemma path_prefix_eq_of_same_length : forall p c,
  path_prefix p c = true -> length p = length c -> p = c.
Proof.
  induction p as [|ph pt IH]; intros c Hpre Hlen.
  - destruct c; [reflexivity | discriminate].
  - destruct c as [|ch ct]; [discriminate|].
    simpl in Hpre. destruct (String.eqb ph ch) eqn:Heq; [|discriminate].
    apply String.eqb_eq in Heq. subst ch.
    f_equal. apply IH; [exact Hpre | simpl in Hlen; lia].
Qed.

(** If path_prefix p (q ++ [x]) and length p <= length q, then path_prefix p q *)
Lemma path_prefix_app_invert : forall p q x,
  path_prefix p (q ++ [x]) = true ->
  length p <= length q ->
  path_prefix p q = true.
Proof.
  induction p as [|ph pt IH]; intros q x Hpre Hlen.
  - reflexivity.
  - destruct q as [|qh qt]; [simpl in Hlen; lia|].
    simpl in Hpre |- *. destruct (String.eqb ph qh) eqn:Heq; [|discriminate].
    apply IH with x; [exact Hpre | simpl in Hlen; lia].
Qed.

(** parent_path of a non-empty list is strictly shorter *)
Lemma parent_path_lt : forall p, p <> [] -> length (parent_path p) < length p.
Proof.
  intros p Hne.
  destruct p as [|h t] using rev_ind; [contradiction|].
  unfold parent_path. rewrite rev_app_distr. simpl. rewrite rev_involutive.
  rewrite app_length. simpl. lia.
Qed.

(** If path_prefix p c and c <> p and c <> [], then path_prefix p (parent_path c) *)
Lemma path_prefix_parent : forall p c,
  path_prefix p c = true ->
  c <> p ->
  c <> [] ->
  path_prefix p (parent_path c) = true.
Proof.
  intros p c Hpre Hneq Hne.
  destruct c as [|ch ct] using rev_ind; [contradiction|].
  unfold parent_path. rewrite rev_app_distr. simpl. rewrite rev_involutive.
  apply path_prefix_app_invert with ch.
  - exact Hpre.
  - apply path_prefix_length in Hpre. rewrite app_length in Hpre. simpl in Hpre.
    destruct (Nat.le_gt_cases (length p) (length ct)) as [Hle | Hgt].
    + exact Hle.
    + exfalso. apply Hneq.
      apply path_prefix_eq_of_same_length; [exact Hpre|].
      rewrite app_length. simpl. lia.
Qed.

(** Well-formedness transitive closure: if a strict descendant exists,
    all ancestors down to the prefix exist.

    Proved by strong induction on length child: at each step, well_formed
    gives path_exists (parent_path child) fs; path_prefix_parent shows
    p is still a prefix of parent_path child; recurse on the shorter path. *)
Lemma well_formed_ancestor_exists :
  forall fs p child,
    well_formed fs ->
    path_prefix p child = true ->
    child <> p ->
    path_exists child fs ->
    path_exists p fs.
Proof.
  intros fs.
  (* Strong induction on length child *)
  assert (Hind : forall n child p,
      length child <= n ->
      well_formed fs ->
      path_prefix p child = true ->
      child <> p ->
      path_exists child fs ->
      path_exists p fs).
  2: { intros p child Hwf Hpre Hneq Hex.
       exact (Hind (length child) child p (Nat.le_refl _) Hwf Hpre Hneq Hex). }
  induction n; intros child p Hlen Hwf Hpre Hneq Hex.
  - (* length child = 0 → child = [] *)
    destruct child; [|simpl in Hlen; lia].
    destruct p; [exact (absurd eq_refl Hneq) | simpl in Hpre; discriminate].
  - destruct child as [|ch ct].
    + (* child = [] *)
      destruct p; [exact (absurd eq_refl Hneq) | simpl in Hpre; discriminate].
    + (* child = ch :: ct, non-empty *)
      destruct (list_eq_dec String.string_dec p (parent_path (ch :: ct))) as [Heq | Hneq'].
      * (* p = parent_path child: one well_formed step *)
        subst p. apply Hwf. exact Hex. discriminate.
      * (* p is a deeper ancestor: recurse *)
        apply (Hind (parent_path (ch :: ct)) p).
        -- (* parent_path is strictly shorter *)
           assert (Hlt : length (parent_path (ch :: ct)) < length (ch :: ct)).
           { apply parent_path_lt. discriminate. }
           simpl in Hlen. lia.
        -- exact Hwf.
        -- apply path_prefix_parent; [exact Hpre | exact Hneq | discriminate].
        -- exact Hneq'.
        -- apply Hwf. exact Hex. discriminate.
Qed.

(** mkdir creates an empty directory (requires well-formedness) *)
Lemma mkdir_creates_empty_dir :
  forall p fs,
    well_formed fs ->
    mkdir_precondition p fs ->
    is_empty_dir p (mkdir p fs).
Proof.
  intros p fs Hwf Hpre.
  split.
  - apply mkdir_creates_directory. assumption.
  - intros child Hprefix Hneq [node Hexists].
    unfold mkdir, fs_update in Hexists.
    destruct (list_eq_dec String.string_dec p child).
    + (* p = child contradicts Hneq *)
      subst. contradiction.
    + (* p <> child, so mkdir didn't create child — child exists in original fs *)
      destruct Hpre as [Hnotexists _].
      apply Hnotexists.
      apply (well_formed_ancestor_exists fs p child Hwf Hprefix Hneq).
      exists node. assumption.
Qed.

(** Rmdir precondition holds after mkdir (given well-formedness).
    Note: This uses the fact that mkdir creates with default_perms,
    and rmdir only needs is_directory + is_empty + parent writable.
    The parent write permission is preserved from the mkdir precondition. *)
Lemma rmdir_precondition_after_mkdir :
  forall p fs,
    well_formed fs ->
    mkdir_precondition p fs ->
    rmdir_precondition p (mkdir p fs).
Proof.
  intros p fs Hwf Hpre.
  destruct Hpre as [Hnotexists [Hparent [Hparentdir Hperms]]].
  unfold rmdir_precondition.
  repeat split.
  - (* is_directory p (mkdir p fs) *)
    apply mkdir_creates_directory.
    unfold mkdir_precondition.
    repeat split; assumption.
  - (* is_empty_dir p (mkdir p fs) *)
    apply mkdir_creates_empty_dir; [assumption |].
    unfold mkdir_precondition.
    repeat split; assumption.
  - (* has_write_permission (parent_path p) (mkdir p fs) *)
    unfold has_write_permission in *.
    destruct Hperms as [node [Hnode Hwr]].
    exists node.
    split; [| assumption].
    unfold mkdir, fs_update.
    destruct (list_eq_dec String.string_dec p (parent_path p)).
    + (* p = parent_path p would mean path_exists p fs via parentExists,
         contradicting notExists *)
      subst. exfalso.
      apply Hnotexists.
      exists node. assumption.
    + assumption.
  - (* p <> root_path *)
    intro Hroot.
    subst.
    destruct Hnotexists.
    apply path_exists_empty_fs_root.
Qed.

(** mkdir preserves well-formedness: adding a node whose parent exists
    maintains the parent-existence invariant for all paths.

    Proof: for any q with path_exists q (mkdir p fs) and q ≠ root_path:
    - If q = p: parent_path p exists in fs by mkdir_precondition; it also
      exists in mkdir p fs since mkdir only adds p (and p ≠ parent_path p).
    - If q ≠ p: q existed in fs (fs_update only changes p); well_formed fs
      gives path_exists (parent_path q) fs; whether parent_path q = p or not,
      it exists in mkdir p fs. *)
Lemma mkdir_preserves_well_formed :
  forall p fs,
    well_formed fs ->
    mkdir_precondition p fs ->
    well_formed (mkdir p fs).
Proof.
  intros p fs Hwf Hpre.
  unfold well_formed.
  intros q Hexq Hqnotroot.
  destruct Hexq as [qnode Hqnode].
  unfold mkdir, fs_update in Hqnode.
  destruct (list_eq_dec String.string_dec p q) as [Heqpq | Hneqpq].
  - (* q = p: just created by mkdir *)
    subst q.
    destruct Hpre as [Hnotex [Hparent _]].
    destruct Hparent as [pnode Hpnode].
    unfold path_exists. exists pnode.
    unfold mkdir, fs_update.
    destruct (list_eq_dec String.string_dec p (parent_path p)) as [Heqpp | Hneqpp].
    + (* p = parent_path p means path_exists p fs — contradicts precondition *)
      exfalso. apply Hnotex. exists pnode. rewrite <- Heqpp. exact Hpnode.
    + exact Hpnode.
  - (* q <> p: q existed in original fs *)
    assert (Hqfs : fs q = Some qnode). { exact Hqnode. }
    assert (Hparentq : path_exists (parent_path q) fs).
    { apply Hwf. exists qnode. exact Hqfs. exact Hqnotroot. }
    destruct Hparentq as [pqnode Hpqnode].
    unfold path_exists.
    unfold mkdir, fs_update.
    destruct (list_eq_dec String.string_dec p (parent_path q)).
    + (* p = parent_path q: mkdir just created it *)
      exists (mkFSNode Directory default_perms). reflexivity.
    + (* p ≠ parent_path q: it existed in fs *)
      exists pqnode. exact Hpqnode.
Qed.

(** Two-directory creation example. *)
Example mkdir_two_dirs_reversible :
  forall p1 p2 fs,
    p1 <> p2 ->
    well_formed fs ->
    mkdir_precondition p1 fs ->
    mkdir_precondition p2 (mkdir p1 fs) ->
    apply_op (OpRmdir p2)
      (apply_op (OpRmdir p1)
        (apply_op (OpMkdir p2)
          (apply_op (OpMkdir p1) fs))) = fs.
Proof.
  intros p1 p2 fs Hneq Hwf Hpre1 Hpre2.
  apply (two_op_sequence_reversible (OpMkdir p1) (OpMkdir p2)).
  - split.
    + exact Hpre1.
    + apply rmdir_precondition_after_mkdir; [| exact Hpre1].
      assumption.
  - split.
    + exact Hpre2.
    + simpl.
      apply rmdir_precondition_after_mkdir.
      * apply mkdir_preserves_well_formed; assumption.
      * exact Hpre2.
Qed.

(** * Composition Preservation *)

(** Preconditions preserved under application *)
Lemma precondition_preserved :
  forall op1 op2 fs,
    op_precondition op1 fs ->
    op_precondition op2 (apply_op op1 fs) ->
    op_precondition op2 fs \/
    (exists fs', apply_op op1 fs = fs' /\ op_precondition op2 fs').
Proof.
  intros op1 op2 fs Hpre1 Hpre2.
  right.
  exists (apply_op op1 fs).
  split; [reflexivity | assumption].
Qed.

(** * Summary *)

(** This file establishes:

    ✓ Operation abstraction (mkdir, rmdir, create_file, delete_file)
    ✓ Operation sequences (apply_sequence, reverse_sequence)
    ✓ Reversibility predicates
    ✓ Single operation reversibility
    ✓ MAIN THEOREM: operation_sequence_reversible
    ✓ CNO connection (reversible ops create identity)
    ✓ Practical examples

    This completes the composition theory for Valence Shell,
    connecting to Absolute Zero's CNO framework and providing
    algebraic structure to the reversibility framework.
*)
