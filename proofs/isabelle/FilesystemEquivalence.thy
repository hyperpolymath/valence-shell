(*  Valence Shell - Filesystem Equivalence (Isabelle/HOL)

    Equivalence relations on filesystems and proofs that operations
    preserve equivalence. Establishes algebraic structure connecting
    to Absolute Zero's CNO = identity theory.
*)

theory FilesystemEquivalence
  imports FilesystemModel FileOperations FilesystemComposition
begin

(* Filesystem Equivalence *)

definition fs_equiv :: "filesystem \<Rightarrow> filesystem \<Rightarrow> bool" (infix "\<approx>" 50) where
  "fs1 \<approx> fs2 \<equiv> (\<forall>p. fs1 p = fs2 p)"

(* Equivalence is an Equivalence Relation *)

lemma fs_equiv_refl:
  "fs \<approx> fs"
  unfolding fs_equiv_def by simp

lemma fs_equiv_sym:
  assumes "fs1 \<approx> fs2"
  shows "fs2 \<approx> fs1"
  using assms unfolding fs_equiv_def by simp

lemma fs_equiv_trans:
  assumes "fs1 \<approx> fs2" "fs2 \<approx> fs3"
  shows "fs1 \<approx> fs3"
  using assms unfolding fs_equiv_def by simp

lemma fs_equiv_is_equivalence:
  "(\<forall>fs. fs \<approx> fs) \<and>
   (\<forall>fs1 fs2. fs1 \<approx> fs2 \<longrightarrow> fs2 \<approx> fs1) \<and>
   (\<forall>fs1 fs2 fs3. fs1 \<approx> fs2 \<longrightarrow> fs2 \<approx> fs3 \<longrightarrow> fs1 \<approx> fs3)"
  using fs_equiv_refl fs_equiv_sym fs_equiv_trans by blast

(* Operations Preserve Equivalence *)

lemma mkdir_preserves_equiv:
  assumes "fs1 \<approx> fs2"
      and "mkdir_precondition p fs1"
      and "mkdir_precondition p fs2"
  shows "mkdir p fs1 \<approx> mkdir p fs2"
  using assms
  unfolding fs_equiv_def mkdir_def fs_update_def
  by auto

lemma rmdir_preserves_equiv:
  assumes "fs1 \<approx> fs2"
      and "rmdir_precondition p fs1"
      and "rmdir_precondition p fs2"
  shows "rmdir p fs1 \<approx> rmdir p fs2"
  using assms
  unfolding fs_equiv_def rmdir_def fs_update_def
  by auto

lemma create_file_preserves_equiv:
  assumes "fs1 \<approx> fs2"
      and "create_file_precondition p fs1"
      and "create_file_precondition p fs2"
  shows "create_file p fs1 \<approx> create_file p fs2"
  using assms
  unfolding fs_equiv_def create_file_def fs_update_def
  by auto

lemma delete_file_preserves_equiv:
  assumes "fs1 \<approx> fs2"
      and "delete_file_precondition p fs1"
      and "delete_file_precondition p fs2"
  shows "delete_file p fs1 \<approx> delete_file p fs2"
  using assms
  unfolding fs_equiv_def delete_file_def fs_update_def
  by auto

lemma apply_op_preserves_equiv:
  assumes "fs1 \<approx> fs2"
      and "op_precondition op fs1"
      and "op_precondition op fs2"
  shows "apply_op op fs1 \<approx> apply_op op fs2"
  using assms
  by (cases op;
      auto simp add: mkdir_preserves_equiv rmdir_preserves_equiv
                     create_file_preserves_equiv delete_file_preserves_equiv)

(* Substitution Property *)

theorem equiv_substitution:
  assumes "fs1 \<approx> fs2"
      and "op_precondition op fs1"
      and "op_precondition op fs2"
  shows "apply_op op fs1 \<approx> apply_op op fs2"
  using assms apply_op_preserves_equiv by blast

(* Reversibility and Equivalence *)

theorem reversible_creates_equiv:
  assumes "reversible op fs"
  shows "apply_op (reverse_op op) (apply_op op fs) \<approx> fs"
proof -
  have "apply_op (reverse_op op) (apply_op op fs) = fs"
  proof (cases op)
    case (MkdirOp p)
    then have "mkdir_precondition p fs"
      using assms unfolding reversible_def by simp
    then show ?thesis using MkdirOp mkdir_rmdir_reversible by simp
  next
    case (RmdirOp p)
    then have pre: "rmdir_precondition p fs" "mkdir_precondition p (rmdir p fs)"
              and perm: "fs p = Some \<lparr> node_type = Directory, node_permissions = default_perms \<rparr>"
      using assms unfolding reversible_def by auto
    then show ?thesis using RmdirOp rmdir_mkdir_reversible by simp
  next
    case (CreateFileOp p)
    then have "create_file_precondition p fs"
      using assms unfolding reversible_def by simp
    then show ?thesis using CreateFileOp create_file_delete_file_reversible by simp
  next
    case (DeleteFileOp p)
    then have pre: "delete_file_precondition p fs" "create_file_precondition p (delete_file p fs)"
              and perm: "fs p = Some \<lparr> node_type = File, node_permissions = default_perms \<rparr>"
      using assms unfolding reversible_def by auto
    then show ?thesis using DeleteFileOp delete_file_create_file_reversible by simp
  qed
  thus ?thesis
    unfolding fs_equiv_def by simp
qed

theorem sequence_reversible_equiv:
  assumes "all_reversible ops fs"
  shows "apply_sequence (reverse_sequence ops) (apply_sequence ops fs) \<approx> fs"
  using assms operation_sequence_reversible
  unfolding fs_equiv_def by simp

(* CNO Connection via Equivalence *)

(* A reversible operation followed by its reverse is equivalent to identity.
   This is the CNO = identity element property from Absolute Zero. *)
theorem cno_identity_element:
  assumes "reversible op fs"
  shows "apply_op (reverse_op op) (apply_op op fs) \<approx> fs"
  using assms reversible_creates_equiv by blast

theorem sequence_cno_identity:
  assumes "all_reversible ops fs"
  shows "apply_sequence (reverse_sequence ops) (apply_sequence ops fs) \<approx> fs"
  using assms sequence_reversible_equiv by blast

(* Congruence Properties *)

theorem equiv_cong_apply_op:
  assumes "fs1 \<approx> fs2"
      and "op_precondition op fs1"
      and "op_precondition op fs2"
  shows "apply_op op fs1 \<approx> apply_op op fs2"
  using assms apply_op_preserves_equiv by blast

(* Operation Equivalence Classes *)

definition ops_equiv :: "operation \<Rightarrow> operation \<Rightarrow> bool" where
  "ops_equiv op1 op2 \<equiv>
    (\<forall>fs. op_precondition op1 fs \<longrightarrow>
          op_precondition op2 fs \<longrightarrow>
          apply_op op1 fs \<approx> apply_op op2 fs)"

lemma ops_equiv_refl:
  "ops_equiv op op"
  unfolding ops_equiv_def using fs_equiv_refl by blast

lemma ops_equiv_sym:
  assumes "ops_equiv op1 op2"
  shows "ops_equiv op2 op1"
  using assms unfolding ops_equiv_def
  using fs_equiv_sym by blast

(* Summary: Filesystem equivalence theory complete in Isabelle/HOL
   Establishes algebraic structure for reversible operations
   Connects to Absolute Zero's CNO = identity element theory *)

end
