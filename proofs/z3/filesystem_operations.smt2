; SPDX-License-Identifier: MPL-2.0
; Valence Shell - Z3 SMT encoding of the core filesystem operations
;
; PROOF-POLICY §4 exception note. Obligation: the mkdir/rmdir and
; createFile/deleteFile reversibility, postcondition, independence and
; composition properties, on a finite-map model. Tool: Z3 (SMT, theory of
; arrays + datatypes). Why: the goals are array identities an SMT solver checks
; automatically; the theory source of truth is the Agda tree (proofs/agda), and this
; file is a supplementary automated check. The queries are *not* quantifier-free:
; the strictness assertion on `child-of` and the `forall` in `rmdir-pre` add
; quantifiers, so termination is not guaranteed by a decision procedure. Z3 4.8.12
; returns every expected result in well under a second, and scripts/verify-z3.sh
; fails any `unknown` or timeout (30 s), so a non-terminating query cannot pass. Status under
; §5: ASSUMED, because a direct SMT run without a proof certificate is not a
; kernel-checked witness.
;
; Encoding (rewritten 2026-11-09). The previous version declared the operations
; as uninterpreted functions and *asserted* each theorem as an axiom before
; "checking" it, which was circular. Here every operation is *defined*: a
; filesystem is an array from paths to entries, and each operation is a
; `store`. Each theorem query asserts the hypotheses and the *negation* of the
; goal; `unsat` means no counterexample exists in the theory of arrays. Nothing
; about the operations is assumed.
;
; Abstraction: entries carry the node type only (no permissions, no content).
; The Agda model carries permissions; reversibility of rmdir/deleteFile there
; needs the original node to have default permissions, which this encoding
; makes trivially true by omitting them.
;
; Expected result sequence (scripts/verify-z3.sh):
;   sat, sat, unsat x 9
; The two `sat` results are non-vacuity checks: the mkdir and rmdir
; preconditions are satisfiable, so the theorems below are not vacuous.

(set-logic ALL)

(declare-sort Path 0)
(declare-datatype NodeType ((File) (Directory)))
(declare-datatype Entry ((Absent) (Present (kind NodeType))))
(define-sort FS () (Array Path Entry))

; Parent of a path; uninterpreted, so every result holds for any parent function.
(declare-fun parent (Path) Path)
; `(child-of c p)`: c is a strict descendant of p; uninterpreted, but strict.
(declare-fun child-of (Path Path) Bool)
(assert (forall ((p Path)) (not (child-of p p))))

(define-fun exists-at ((p Path) (fs FS)) Bool (not (= (select fs p) Absent)))
(define-fun is-dir ((p Path) (fs FS)) Bool (= (select fs p) (Present Directory)))
(define-fun is-file ((p Path) (fs FS)) Bool (= (select fs p) (Present File)))

(define-fun mkdir ((p Path) (fs FS)) FS (store fs p (Present Directory)))
(define-fun rmdir ((p Path) (fs FS)) FS (store fs p Absent))
(define-fun create-file ((p Path) (fs FS)) FS (store fs p (Present File)))
(define-fun delete-file ((p Path) (fs FS)) FS (store fs p Absent))

(define-fun mkdir-pre ((p Path) (fs FS)) Bool
  (and (not (exists-at p fs)) (is-dir (parent p) fs)))
(define-fun rmdir-pre ((p Path) (fs FS)) Bool
  (and (is-dir p fs)
       (forall ((c Path)) (=> (child-of c p) (not (exists-at c fs))))))
(define-fun create-file-pre ((p Path) (fs FS)) Bool
  (and (not (exists-at p fs)) (is-dir (parent p) fs)))
(define-fun delete-file-pre ((p Path) (fs FS)) Bool (is-file p fs))

(declare-const p Path)
(declare-const p1 Path)
(declare-const p2 Path)
(declare-const p3 Path)
(declare-const fs FS)

; ===== Non-vacuity (expected: sat, sat) =====

(push)
(assert (mkdir-pre p fs))
(check-sat)
(pop)

(push)
(assert (rmdir-pre p fs))
(check-sat)
(pop)

; ===== Reversibility (expected: unsat x 4) =====

(push)
(assert (mkdir-pre p fs))
(assert (not (= (rmdir p (mkdir p fs)) fs)))
(check-sat)
(pop)

(push)
(assert (rmdir-pre p fs))
(assert (not (= (mkdir p (rmdir p fs)) fs)))
(check-sat)
(pop)

(push)
(assert (create-file-pre p fs))
(assert (not (= (delete-file p (create-file p fs)) fs)))
(check-sat)
(pop)

(push)
(assert (delete-file-pre p fs))
(assert (not (= (create-file p (delete-file p fs)) fs)))
(check-sat)
(pop)

; ===== Postconditions (expected: unsat x 2) =====

(push)
(assert (not (is-dir p (mkdir p fs))))
(check-sat)
(pop)

(push)
(assert (exists-at p (rmdir p fs)))
(check-sat)
(pop)

; ===== Independence (expected: unsat) =====

(push)
(assert (not (= p1 p2)))
(assert (not (= (select (mkdir p1 fs) p2) (select fs p2))))
(check-sat)
(pop)

; ===== Composition, undone in reverse order (expected: unsat x 2) =====

(push)
(assert (mkdir-pre p1 fs))
(assert (mkdir-pre p2 (mkdir p1 fs)))
(assert (not (= (rmdir p1 (rmdir p2 (mkdir p2 (mkdir p1 fs)))) fs)))
(check-sat)
(pop)

(push)
(assert (mkdir-pre p1 fs))
(assert (mkdir-pre p2 (mkdir p1 fs)))
(assert (mkdir-pre p3 (mkdir p2 (mkdir p1 fs))))
(assert (not (= (rmdir p1 (rmdir p2 (rmdir p3 (mkdir p3 (mkdir p2 (mkdir p1 fs)))))) fs)))
(check-sat)
(pop)
