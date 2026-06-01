-- SPDX-License-Identifier: MPL-2.0
-- Valence Shell — Crash-Consistency Keystone (Lean 4)
--
-- This file models the *atomicity-within-op* assumption that underlies
-- every higher-level crash-consistency theorem for valence-shell.
--
-- Companion design document: docs/THEORY-CRASH-CONSISTENCY.adoc
-- Closes the keystone slice of issue #45 (FS-theory gaps); the four
-- remaining frontiers (concurrency, POSIX 2024 edges, Idris2-via-WASM,
-- hardware-level) are deferred to separate Tier-S follow-ups.
--
-- L4 (dyadic-resource) note: A crash event is the canonical
-- linear-resource interruption.  Future cross-link to
-- echo-types `EchoOFSUnivF5` / the dyadic layer is intended.

import FilesystemModel

namespace ValenceShell.CrashConsistency

/-- A `CrashPoint` describes *when* an external interruption observes
    the operation.  The atomicity-within-op assumption is that the only
    two observable points are *before* applying the state mutation and
    *after* applying it — never in the middle. -/
inductive CrashPoint where
  | BeforeApply : CrashPoint
  | AfterApply  : CrashPoint
  deriving DecidableEq, Repr

/-- Operations valence-shell currently models at the proof layer.
    Only `mkdir` is needed for the keystone; the broader catalogue
    (`rmdir`, file ops, RMOs, …) reuses the same crash-point shape. -/
inductive Op where
  | mkdir : Path → Op
  deriving Repr

/-- Apply an `Op` to a `Filesystem`.  This is the *post-state* of the
    operation; pre-state is just the original `fs`. -/
def apply (fs : Filesystem) : Op → Filesystem
  | Op.mkdir p => mkdir p fs

/-- The crash-state function: given a starting filesystem, an op, and
    a crash point, the observable filesystem after the interruption is
    *either* the pre-state (BeforeApply) *or* the post-state (AfterApply).
    Nothing else is observable — that is the content of the keystone
    theorem below. -/
def crash_state (fs : Filesystem) (op : Op) : CrashPoint → Filesystem
  | CrashPoint.BeforeApply => fs
  | CrashPoint.AfterApply  => apply fs op

/-- **Keystone: crash atomicity within a single mkdir.**
    For any pre-state `fs`, any path `p`, and any crash point `cp`,
    the observable filesystem at the crash boundary is *either* the
    pre-state or the post-state — never a partial third state.

    This is trivial-by-cases on `cp` once the model is set up.  The
    value is in the modelling: it pins down the assumption that
    valence-shell's correctness story relies on (journal-data mode on
    ext4, COW on ZFS, atomic-rename idioms on metadata-only journals). -/
theorem crash_atomic_within_op_mkdir
    (fs : Filesystem) (p : Path) (cp : CrashPoint) :
    crash_state fs (Op.mkdir p) cp = fs
  ∨ crash_state fs (Op.mkdir p) cp = mkdir p fs := by
  cases cp with
  | BeforeApply =>
    left
    rfl
  | AfterApply  =>
    right
    rfl

/-- Corollary: the crash state is *never* a "third" filesystem
    distinct from both the pre- and post-states. -/
theorem crash_state_no_third_value
    (fs : Filesystem) (p : Path) (cp : CrashPoint)
    (g : Filesystem)
    (h1 : g ≠ fs)
    (h2 : g ≠ mkdir p fs) :
    crash_state fs (Op.mkdir p) cp ≠ g := by
  intro heq
  cases crash_atomic_within_op_mkdir fs p cp with
  | inl hpre  => rw [hpre]  at heq; exact h1 heq.symm
  | inr hpost => rw [hpost] at heq; exact h2 heq.symm

end ValenceShell.CrashConsistency

-- Axiom audit (Lean 4 equivalent of Coq's `Print Assumptions`).
-- Expected output: "'crash_atomic_within_op_mkdir' depends on axioms: [propext]"
-- or no axioms at all — both acceptable; the keystone introduces no
-- new axioms beyond what FilesystemModel.lean already uses.
#print axioms ValenceShell.CrashConsistency.crash_atomic_within_op_mkdir
