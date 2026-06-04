(** Valence Shell - Filesystem Composition Theorems

    This file extends the filesystem model with composition theorems,
    proving that sequences of reversible operations compose correctly.

    Based on composition patterns from Absolute Zero's CNO theory.
*)

Require Import String.
Require Import List.
Require Import Bool.
Require Import Arith.
Require Import Lia.
Require Import Coq.Logic.FunctionalExtensionality.
Import ListNotations.

Require Import filesystem_model.
Require Import file_operations.

(** * Operation Abstraction *)

(** Abstract operation type.

    The [OpMkdirWithPerms] and [OpCreateFileWithPerms] constructors carry
    the [Permissions] snapshot of the node being re-created.  They exist
    so that the inverse of an [OpRmdir]/[OpDeleteFile] can faithfully
    restore the original entry (closure path #2 from the model-gap design
    note below — see the [single_op_reversible] header docstring). *)
Inductive Operation : Type :=
  | OpMkdir : Path -> Operation
  | OpRmdir : Path -> Operation
  | OpCreateFile : Path -> Operation
  | OpDeleteFile : Path -> Operation
  | OpMkdirWithPerms : Path -> Permissions -> Operation
  | OpCreateFileWithPerms : Path -> Permissions -> Operation.

(** [mkdir_with] and [create_file_with]: write a node with the supplied
    [Permissions] rather than [default_perms].  These are used exclusively
    by the inverse-of-removal path. *)
Definition mkdir_with (p : Path) (pe : Permissions) (fs : Filesystem) : Filesystem :=
  fs_update p (Some (mkFSNode Directory pe)) fs.

Definition create_file_with (p : Path) (pe : Permissions) (fs : Filesystem) : Filesystem :=
  fs_update p (Some (mkFSNode File pe)) fs.

(** Apply an operation to a filesystem *)
Definition apply_op (op : Operation) (fs : Filesystem) : Filesystem :=
  match op with
  | OpMkdir p => mkdir p fs
  | OpRmdir p => rmdir p fs
  | OpCreateFile p => create_file p fs
  | OpDeleteFile p => delete_file p fs
  | OpMkdirWithPerms p pe => mkdir_with p pe fs
  | OpCreateFileWithPerms p pe => create_file_with p pe fs
  end.

(** Reverse of an operation given the pre-state.

    The pre-state [fs] is consulted only for the [OpRmdir] /
    [OpDeleteFile] cases, where the perms of the to-be-removed node are
    captured so the inverse can restore them exactly.  For all other
    constructors the reverse is independent of [fs].

    Design rationale: keeping [reverse_op] as a function of [op] alone
    would force us to pick a single [Permissions] value at definition
    time — the only honest choice would be [default_perms], which gives
    back the existing (provably-false-for-non-default-perms) statement.
    Threading [fs] is the minimal change that lets the inverse depend on
    runtime state and is consistent with the directive's closure path #2. *)
Definition reverse_op (op : Operation) (fs : Filesystem) : Operation :=
  match op with
  | OpMkdir p => OpRmdir p
  | OpRmdir p =>
      match fs p with
      | Some node => OpMkdirWithPerms p (permissions node)
      | None => OpMkdir p  (* unreachable when [op] has valid precondition *)
      end
  | OpCreateFile p => OpDeleteFile p
  | OpDeleteFile p =>
      match fs p with
      | Some node => OpCreateFileWithPerms p (permissions node)
      | None => OpCreateFile p  (* unreachable when [op] has valid precondition *)
      end
  | OpMkdirWithPerms p _ => OpRmdir p
  | OpCreateFileWithPerms p _ => OpDeleteFile p
  end.

(** * Operation Sequences *)

(** Apply a sequence of operations *)
Fixpoint apply_sequence (ops : list Operation) (fs : Filesystem) : Filesystem :=
  match ops with
  | [] => fs
  | op :: rest => apply_sequence rest (apply_op op fs)
  end.

(** Reverse a sequence of operations.

    Because [reverse_op] now consults the pre-state, the LIFO reversal
    must thread the running pre-state of each operation through.  Given
    [ops = [o1; o2; o3]] applied to [fs], the reversal sequence is
    [[reverse_op o3 (apply_sequence [o1;o2] fs);
       reverse_op o2 (apply_sequence [o1] fs);
       reverse_op o1 fs]]
    i.e. each operation's inverse is computed against the state in which
    that operation was originally applied. *)
Fixpoint reverse_sequence (ops : list Operation) (fs : Filesystem) : list Operation :=
  match ops with
  | [] => []
  | op :: rest =>
      reverse_sequence rest (apply_op op fs) ++ [reverse_op op fs]
  end.

(** * Precondition Predicates *)

(** Operation has valid preconditions *)
Definition op_precondition (op : Operation) (fs : Filesystem) : Prop :=
  match op with
  | OpMkdir p => mkdir_precondition p fs
  | OpRmdir p => rmdir_precondition p fs
  | OpCreateFile p => create_file_precondition p fs
  | OpDeleteFile p => delete_file_precondition p fs
  | OpMkdirWithPerms p _ =>
      (* same shape as mkdir_precondition — the perms argument is only
         used for the body of the node written *)
      mkdir_precondition p fs
  | OpCreateFileWithPerms p _ =>
      create_file_precondition p fs
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
  op_precondition (reverse_op op fs) (apply_op op fs).

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

(** Reverse of empty sequence *)
Lemma reverse_sequence_nil :
  forall fs, reverse_sequence [] fs = [].
Proof.
  intros fs.
  simpl.
  reflexivity.
Qed.

(** Reverse distributes over append.

    Threading the pre-state requires expressing the right argument's
    pre-state as the result of applying [ops1] to [fs]. *)
Lemma reverse_sequence_app :
  forall ops1 ops2 fs,
    reverse_sequence (ops1 ++ ops2) fs =
    reverse_sequence ops2 (apply_sequence ops1 fs) ++ reverse_sequence ops1 fs.
Proof.
  intros ops1.
  induction ops1 as [| op ops1' IH]; intros ops2 fs.
  - simpl. rewrite app_nil_r. reflexivity.
  - simpl. rewrite IH. rewrite app_assoc. reflexivity.
Qed.

(** Reverse of single operation *)
Lemma reverse_sequence_singleton :
  forall op fs,
    reverse_sequence [op] fs = [reverse_op op fs].
Proof.
  intros op fs.
  simpl.
  reflexivity.
Qed.

(** apply_sequence distributes over append *)
Lemma apply_sequence_app :
  forall ops1 ops2 fs,
    apply_sequence (ops1 ++ ops2) fs =
    apply_sequence ops2 (apply_sequence ops1 fs).
Proof.
  intros ops1.
  induction ops1 as [| op ops1' IH].
  - intros ops2 fs. simpl. reflexivity.
  - intros ops2 fs. simpl. apply IH.
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

(** Generic single operation reversibility.

    PROOF STATUS (2026-06-01, PR #N): Closed via closure path #2 — the
    [Operation] inductive now carries [OpMkdirWithPerms] and
    [OpCreateFileWithPerms] constructors, and [reverse_op] is threaded
    with the pre-state so the inverse of an [OpRmdir]/[OpDeleteFile] can
    capture the original node's permissions and faithfully restore them.

    Historical model gap (now resolved): [mkdir] / [create_file] write
    [default_perms], but the original entry being removed by [rmdir] /
    [delete_file] may have had non-default permissions, making the naive
    "[mkdir o rmdir = id]" claim false in general.  The fix routes the
    inverse of [OpRmdir]/[OpDeleteFile] through the
    [...WithPerms] variants that re-create the node with the captured
    perms.

    All four "natural" constructors plus the two [...WithPerms]
    constructors are now provably reversible from [reversible op fs]
    alone — no extra precondition is needed beyond what [reversible]
    already enforces. *)
Theorem single_op_reversible :
  forall op fs,
    reversible op fs ->
    apply_op (reverse_op op fs) (apply_op op fs) = fs.
Proof.
  intros op fs [Hpre Hrev].
  destruct op as [p | p | p | p | p pe | p pe].
  - (* OpMkdir *)
    simpl in *.
    apply mkdir_rmdir_reversible.
    assumption.
  - (* OpRmdir — closure via OpMkdirWithPerms *)
    simpl.
    (* [Hpre] is [rmdir_precondition p fs], which contains
       [is_directory p fs] — that is, [fs p = Some (mkFSNode Directory perms)]
       for some [perms].  Thus [match fs p with ...] reduces. *)
    destruct Hpre as [Hdir _].
    destruct Hdir as [perms Hpd].
    rewrite Hpd. simpl.
    (* Goal: mkdir_with p (permissions {| node_type := Directory;
                                          permissions := perms |})
                          (rmdir p fs) = fs *)
    unfold mkdir_with, rmdir, fs_update.
    apply functional_extensionality.
    intros p'.
    destruct (list_eq_dec String.string_dec p p') as [Heq | Hneq].
    + (* p = p': rebuild original node *)
      subst p'. simpl. rewrite Hpd. reflexivity.
    + reflexivity.
  - (* OpCreateFile *)
    simpl in *.
    apply create_delete_file_reversible.
    assumption.
  - (* OpDeleteFile — closure via OpCreateFileWithPerms *)
    simpl.
    destruct Hpre as [Hfile _].
    destruct Hfile as [perms Hpf].
    rewrite Hpf. simpl.
    unfold create_file_with, delete_file, fs_update.
    apply functional_extensionality.
    intros p'.
    destruct (list_eq_dec String.string_dec p p') as [Heq | Hneq].
    + subst p'. simpl. rewrite Hpf. reflexivity.
    + reflexivity.
  - (* OpMkdirWithPerms — inverse is OpRmdir, which deletes; restoring
       the pre-state requires that [fs p = None].  This is given by
       [mkdir_precondition], which contains [~ path_exists p fs]. *)
    simpl in *.
    unfold mkdir_with, rmdir, fs_update.
    apply functional_extensionality.
    intros p'.
    destruct (list_eq_dec String.string_dec p p') as [Heq | Hneq].
    + subst p'.
      destruct Hpre as [Hnotex _].
      destruct (fs p) as [node|] eqn:Hfp.
      * exfalso. apply Hnotex. exists node. exact Hfp.
      * reflexivity.
    + reflexivity.
  - (* OpCreateFileWithPerms — same as OpMkdirWithPerms shape *)
    simpl in *.
    unfold create_file_with, delete_file, fs_update.
    apply functional_extensionality.
    intros p'.
    destruct (list_eq_dec String.string_dec p p') as [Heq | Hneq].
    + subst p'.
      destruct Hpre as [Hnotex _].
      destruct (fs p) as [node|] eqn:Hfp.
      * exfalso. apply Hnotex. exists node. exact Hfp.
      * reflexivity.
    + reflexivity.
Qed.

(** * Composition Theorems *)

(** Main composition theorem: reversing a sequence of reversible operations
    returns to the original state.

    Because [reverse_sequence] now threads the pre-state of each
    operation, the second argument to the outer [apply_sequence] is
    [fs] (the global pre-state) rather than the post-state.

    This is the key theorem connecting to Absolute Zero's CNO composition theory.
*)
Theorem operation_sequence_reversible :
  forall (ops : list Operation) (fs : Filesystem),
    all_reversible ops fs ->
    apply_sequence (reverse_sequence ops fs) (apply_sequence ops fs) = fs.
Proof.
  intros ops.
  induction ops as [| op ops' IH].
  - (* Base case: empty sequence *)
    intros fs Hrev.
    simpl.
    reflexivity.
  - (* Inductive case: op :: ops' *)
    intros fs [Hrev_op Hrev_rest].
    simpl.
    (* Goal: apply_sequence
              (reverse_sequence ops' (apply_op op fs) ++ [reverse_op op fs])
              (apply_sequence ops' (apply_op op fs)) = fs *)
    rewrite apply_sequence_app.
    rewrite (IH (apply_op op fs) Hrev_rest).
    (* Goal: apply_sequence [reverse_op op fs] (apply_op op fs) = fs *)
    simpl.
    apply single_op_reversible.
    assumption.
Qed.

(** Two-operation sequence.

    The pre-state for [reverse_op op2] is [apply_op op1 fs] (the state in
    which [op2] was applied), and for [reverse_op op1] it is [fs]
    itself. *)
Theorem two_op_sequence_reversible :
  forall op1 op2 fs,
    reversible op1 fs ->
    reversible op2 (apply_op op1 fs) ->
    apply_op (reverse_op op1 fs)
      (apply_op (reverse_op op2 (apply_op op1 fs))
        (apply_op op2 (apply_op op1 fs))) = fs.
Proof.
  intros op1 op2 fs Hrev1 Hrev2.
  pose proof (operation_sequence_reversible [op1; op2] fs) as Hseq.
  simpl in Hseq.
  apply Hseq.
  split; [assumption | split; [assumption | trivial]].
Qed.

(** Three-operation sequence *)
Theorem three_op_sequence_reversible :
  forall op1 op2 op3 fs,
    reversible op1 fs ->
    reversible op2 (apply_op op1 fs) ->
    reversible op3 (apply_op op2 (apply_op op1 fs)) ->
    apply_sequence (reverse_sequence [op1; op2; op3] fs)
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
    apply_sequence (ops ++ reverse_sequence ops fs) fs = fs.

Theorem reversible_creates_CNO :
  forall op,
    is_CNO_sequence [op].
Proof.
  intros op fs [Hrev _].
  simpl.
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
  - assert (Hpre_path := Hpre).
    apply path_prefix_length in Hpre. rewrite app_length in Hpre. simpl in Hpre.
    destruct (Nat.le_gt_cases (Datatypes.length p) (Datatypes.length ct)) as [Hle | Hgt].
    + exact Hle.
    + exfalso. apply Hneq.
      symmetry.
      apply path_prefix_eq_of_same_length; [exact Hpre_path|].
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
    destruct p; [exfalso; apply Hneq; reflexivity | simpl in Hpre; discriminate].
  - destruct child as [|ch ct].
    + (* child = [] *)
      destruct p; [exfalso; apply Hneq; reflexivity | simpl in Hpre; discriminate].
    + (* child = ch :: ct, non-empty *)
      destruct (list_eq_dec String.string_dec p (parent_path (ch :: ct))) as [Heq | Hneq'].
      * (* p = parent_path child: one well_formed step *)
        subst p. apply Hwf. exact Hex. discriminate.
      * (* p is a deeper ancestor: recurse via IHn on parent_path *)
        apply (IHn (parent_path (ch :: ct)) p).
        -- (* parent_path is strictly shorter, so length parent <= n *)
           assert (Hlt : length (parent_path (ch :: ct)) < length (ch :: ct)).
           { apply parent_path_lt. discriminate. }
           lia.
        -- exact Hwf.
        -- apply path_prefix_parent; [exact Hpre | exact Hneq | discriminate].
        -- intros Heq. apply Hneq'. symmetry. exact Heq.
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
  split; [|split; [|split]].
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
    destruct (list_eq_dec String.string_dec p (parent_path p)) as [Heq | _].
    + (* p = parent_path p — contradicts Hnotexists: p already exists via Hnode *)
      exfalso. apply Hnotexists. exists node. rewrite Heq. exact Hnode.
    + assumption.
  - (* p <> root_path *)
    intro Hroot.
    subst.
    apply Hnotexists.
    unfold parent_exists in Hparent. simpl in Hparent.
    exact Hparent.
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
      exfalso. apply Hnotex. exists pnode. rewrite Heqpp. exact Hpnode.
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

(** Two-directory creation example — restated to LIFO sequence order.

    The earlier statement reversed [mkdir p1; mkdir p2] with [rmdir p1]
    applied BEFORE [rmdir p2] (FIFO order), which is not derivable from
    [two_op_sequence_reversible] (which proves the LIFO case). Restated
    here so the OUTER rmdir undoes the FIRST mkdir, matching the LIFO
    discipline that the general theorem establishes.

    Closes #56.  See [docs/PROOF-OPEN-FRONTIER.adoc] for context. *)
Example mkdir_two_dirs_reversible :
  forall p1 p2 fs,
    p1 <> p2 ->
    well_formed fs ->
    mkdir_precondition p1 fs ->
    mkdir_precondition p2 (mkdir p1 fs) ->
    apply_op (OpRmdir p1)
      (apply_op (OpRmdir p2)
        (apply_op (OpMkdir p2)
          (apply_op (OpMkdir p1) fs))) = fs.
Proof.
  intros p1 p2 fs Hneq Hwf Hpre1 Hpre2.
  pose proof (two_op_sequence_reversible (OpMkdir p1) (OpMkdir p2) fs) as Hseq.
  simpl in Hseq.
  apply Hseq.
  - (* reversible (OpMkdir p1) fs *)
    unfold reversible. split.
    + simpl. exact Hpre1.
    + simpl. apply rmdir_precondition_after_mkdir; assumption.
  - (* reversible (OpMkdir p2) (apply_op (OpMkdir p1) fs) *)
    unfold reversible. split.
    + simpl. exact Hpre2.
    + simpl.
      apply rmdir_precondition_after_mkdir;
        [apply mkdir_preserves_well_formed; assumption | exact Hpre2].
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

(** * Axiom Audit *)

(** [single_op_reversible] is the load-bearing leaf this PR closes.
    Print its assumptions so any axiom slippage shows up at compile
    time.  Expected output: only [functional_extensionality] (used to
    prove pointwise-equal filesystems are equal as functions). *)
Print Assumptions single_op_reversible.
Print Assumptions operation_sequence_reversible.
Print Assumptions reversible_creates_CNO.
