; SPDX-License-Identifier: MPL-2.0
; Valence Shell - Z3 SMT encoding of symlink creation and removal
;
; PROOF-POLICY §4 exception note. Obligation: symlink/unlink reversibility and
; postconditions on a finite-map model. Tool: Z3 (theory of arrays +
; datatypes). Why: quantifier-free array identities an SMT solver decides
; automatically; the theory source of truth is proofs/agda/SymlinkOperations.agda.
; Status under §5: ASSUMED (no proof certificate).
;
; Rewritten 2026-11-09. The previous version had one `(check-sat)` that
; returned `sat` and never negated a goal, so it proved nothing; it also
; asserted `symlink p fs = fs-update p node fs` for *every* node, forcing all
; updates at a path to coincide. Here symlink and unlink are defined as
; `store`s, and each theorem query asserts the negated goal.
;
; As in the Agda model, a symlink is a file-typed node; the target is not
; modelled.
;
; Expected result sequence (scripts/verify-z3.sh): sat, unsat x 4

(set-logic ALL)

(declare-sort Path 0)
(declare-datatype NodeType ((File) (Directory)))
(declare-datatype Entry ((Absent) (Present (kind NodeType))))
(define-sort FS () (Array Path Entry))

(declare-fun parent (Path) Path)

(define-fun exists-at ((p Path) (fs FS)) Bool (not (= (select fs p) Absent)))
(define-fun is-dir ((p Path) (fs FS)) Bool (= (select fs p) (Present Directory)))

(define-fun symlink ((p Path) (fs FS)) FS (store fs p (Present File)))
(define-fun unlink ((p Path) (fs FS)) FS (store fs p Absent))

(define-fun symlink-pre ((p Path) (fs FS)) Bool
  (and (not (exists-at p fs)) (is-dir (parent p) fs)))

(declare-const p Path)
(declare-const q Path)
(declare-const fs FS)

; Non-vacuity: the precondition is satisfiable (expected: sat)
(push)
(assert (symlink-pre p fs))
(check-sat)
(pop)

; symlink then unlink restores the filesystem (expected: unsat)
(push)
(assert (symlink-pre p fs))
(assert (not (= (unlink p (symlink p fs)) fs)))
(check-sat)
(pop)

; symlink creates the path (expected: unsat)
(push)
(assert (not (exists-at p (symlink p fs))))
(check-sat)
(pop)

; unlink removes the path (expected: unsat)
(push)
(assert (exists-at p (unlink p fs)))
(check-sat)
(pop)

; symlink leaves other paths alone (expected: unsat)
(push)
(assert (not (= p q)))
(assert (not (= (select (symlink p fs) q) (select fs q))))
(check-sat)
(pop)
