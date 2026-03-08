; SPDX-License-Identifier: PMPL-1.0-or-later
; Valence Shell - Permission Operations in Z3/SMT-LIB
;
; Formalizes chmod and chown as reversible operations.
; Proves that applying the old permission/ownership after a change
; restores the original filesystem state.

(set-logic ALL)
(set-option :produce-models true)

; ===== Sorts =====

(declare-sort Path 0)
(declare-sort FilesystemExt 0)
(declare-sort Mode 0)
(declare-sort Ownership 0)

; ===== Core Predicates/Functions =====

(declare-fun path-exists (Path FilesystemExt) Bool)
(declare-fun fs-get-mode (Path FilesystemExt) Mode)
(declare-fun fs-get-owner (Path FilesystemExt) Ownership)

; ===== chmod Operation =====

(declare-fun chmod (Path Mode FilesystemExt) FilesystemExt)

; chmod changes only the mode at the target path
(assert (forall ((p Path) (m Mode) (fs FilesystemExt))
  (=> (path-exists p fs)
      (path-exists p (chmod p m fs)))))

; chmod sets the mode at p to m
(assert (forall ((p Path) (m Mode) (fs FilesystemExt))
  (=> (path-exists p fs)
      (= (fs-get-mode p (chmod p m fs)) m))))

; chmod preserves ownership at p
(assert (forall ((p Path) (m Mode) (fs FilesystemExt))
  (=> (path-exists p fs)
      (= (fs-get-owner p (chmod p m fs)) (fs-get-owner p fs)))))

; chmod preserves other paths — mode
(assert (forall ((p1 Path) (p2 Path) (m Mode) (fs FilesystemExt))
  (=> (not (= p1 p2))
      (= (fs-get-mode p2 (chmod p1 m fs)) (fs-get-mode p2 fs)))))

; chmod preserves other paths — ownership
(assert (forall ((p1 Path) (p2 Path) (m Mode) (fs FilesystemExt))
  (=> (not (= p1 p2))
      (= (fs-get-owner p2 (chmod p1 m fs)) (fs-get-owner p2 fs)))))

; chmod preserves other paths — existence
(assert (forall ((p1 Path) (p2 Path) (m Mode) (fs FilesystemExt))
  (=> (not (= p1 p2))
      (= (path-exists p2 (chmod p1 m fs)) (path-exists p2 fs)))))

; ===== chown Operation =====

(declare-fun chown (Path Ownership FilesystemExt) FilesystemExt)

; chown changes only the ownership at the target path
(assert (forall ((p Path) (o Ownership) (fs FilesystemExt))
  (=> (path-exists p fs)
      (path-exists p (chown p o fs)))))

; chown sets the owner at p to o
(assert (forall ((p Path) (o Ownership) (fs FilesystemExt))
  (=> (path-exists p fs)
      (= (fs-get-owner p (chown p o fs)) o))))

; chown preserves mode at p
(assert (forall ((p Path) (o Ownership) (fs FilesystemExt))
  (=> (path-exists p fs)
      (= (fs-get-mode p (chown p o fs)) (fs-get-mode p fs)))))

; chown preserves other paths — mode
(assert (forall ((p1 Path) (p2 Path) (o Ownership) (fs FilesystemExt))
  (=> (not (= p1 p2))
      (= (fs-get-mode p2 (chown p1 o fs)) (fs-get-mode p2 fs)))))

; chown preserves other paths — ownership
(assert (forall ((p1 Path) (p2 Path) (o Ownership) (fs FilesystemExt))
  (=> (not (= p1 p2))
      (= (fs-get-owner p2 (chown p1 o fs)) (fs-get-owner p2 fs)))))

; chown preserves other paths — existence
(assert (forall ((p1 Path) (p2 Path) (o Ownership) (fs FilesystemExt))
  (=> (not (= p1 p2))
      (= (path-exists p2 (chown p1 o fs)) (path-exists p2 fs)))))

; ===== Extensional Equality Axiom =====
; Two extended filesystems are equal iff they agree on existence, mode, and owner at all paths

(declare-fun fs-ext-eq (FilesystemExt FilesystemExt) Bool)

(assert (forall ((fs1 FilesystemExt) (fs2 FilesystemExt))
  (= (fs-ext-eq fs1 fs2)
     (forall ((p Path))
       (and (= (path-exists p fs1) (path-exists p fs2))
            (= (fs-get-mode p fs1) (fs-get-mode p fs2))
            (= (fs-get-owner p fs1) (fs-get-owner p fs2)))))))

; ===== Reversibility Verification =====

; Verify: chmod(oldMode, chmod(newMode, fs)) = fs when oldMode was original
(push)
(declare-const p Path)
(declare-const fs FilesystemExt)
(declare-const oldMode Mode)
(declare-const newMode Mode)

; Preconditions
(assert (path-exists p fs))
(assert (= (fs-get-mode p fs) oldMode))

; Claim: chmod(p, oldMode, chmod(p, newMode, fs)) extensionally equals fs
(assert (not (fs-ext-eq (chmod p oldMode (chmod p newMode fs)) fs)))

(check-sat) ; Expected: unsat (proving the claim)
(pop)

; Verify: chown(oldOwner, chown(newOwner, fs)) = fs when oldOwner was original
(push)
(declare-const p Path)
(declare-const fs FilesystemExt)
(declare-const oldOwner Ownership)
(declare-const newOwner Ownership)

; Preconditions
(assert (path-exists p fs))
(assert (= (fs-get-owner p fs) oldOwner))

; Claim: chown(p, oldOwner, chown(p, newOwner, fs)) extensionally equals fs
(assert (not (fs-ext-eq (chown p oldOwner (chown p newOwner fs)) fs)))

(check-sat) ; Expected: unsat (proving the claim)
(pop)

; Verify: chmod and chown commute
(push)
(declare-const p Path)
(declare-const fs FilesystemExt)
(declare-const m Mode)
(declare-const o Ownership)

(assert (path-exists p fs))

; Claim: chmod(p, m, chown(p, o, fs)) = chown(p, o, chmod(p, m, fs))
(assert (not (fs-ext-eq (chmod p m (chown p o fs)) (chown p o (chmod p m fs)))))

(check-sat) ; Expected: unsat (proving commutativity)
(pop)

; Verify: chmod preserves other paths
(push)
(declare-const p1 Path)
(declare-const p2 Path)
(declare-const fs FilesystemExt)
(declare-const m Mode)

(assert (not (= p1 p2)))

; Claim: chmod at p1 doesn't change anything at p2
(assert (or (not (= (path-exists p2 (chmod p1 m fs)) (path-exists p2 fs)))
            (not (= (fs-get-mode p2 (chmod p1 m fs)) (fs-get-mode p2 fs)))
            (not (= (fs-get-owner p2 (chmod p1 m fs)) (fs-get-owner p2 fs)))))

(check-sat) ; Expected: unsat
(pop)

; Verify: chown preserves other paths
(push)
(declare-const p1 Path)
(declare-const p2 Path)
(declare-const fs FilesystemExt)
(declare-const o Ownership)

(assert (not (= p1 p2)))

; Claim: chown at p1 doesn't change anything at p2
(assert (or (not (= (path-exists p2 (chown p1 o fs)) (path-exists p2 fs)))
            (not (= (fs-get-mode p2 (chown p1 o fs)) (fs-get-mode p2 fs)))
            (not (= (fs-get-owner p2 (chown p1 o fs)) (fs-get-owner p2 fs)))))

(check-sat) ; Expected: unsat
(pop)
