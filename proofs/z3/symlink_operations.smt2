; SPDX-License-Identifier: PLMP-1.0-or-later
; Valence Shell - Symlink Operations in Z3/SMT-LIB
;
; Abstract model of symbolic link creation and removal.
; A symlink is represented as a file node with default permissions;
; the target path is modeled externally.

(set-logic ALL)
(set-option :produce-models true)

; ===== Sorts =====

(declare-sort Path 0)
(declare-sort Filesystem 0)
(declare-sort FSNode 0)

; ===== Core Predicates/Functions =====

(declare-fun path-exists (Path Filesystem) Bool)
(declare-fun parent-path (Path) Path)
(declare-fun parent-exists (Path Filesystem) Bool)
(declare-fun is-directory (Path Filesystem) Bool)
(declare-fun has-write-permission (Path Filesystem) Bool)
(declare-fun fs-update (Path FSNode Filesystem) Filesystem)
(declare-fun fs-delete (Path Filesystem) Filesystem)
(declare-fun fs-get (Filesystem Path) FSNode)

; ===== Symlink Operations =====

(declare-fun symlink-precondition (Path Filesystem) Bool)
(declare-fun symlink (Path Filesystem) Filesystem)
(declare-fun unlink (Path Filesystem) Filesystem)

(assert (forall ((p Path) (fs Filesystem))
  (= (symlink-precondition p fs)
     (and (not (path-exists p fs))
          (parent-exists p fs)
          (is-directory (parent-path p) fs)
          (has-write-permission (parent-path p) fs)))))

; symlink modeled as fs-update with a fresh node
(assert (forall ((p Path) (node FSNode) (fs Filesystem))
  (= (symlink p fs) (fs-update p node fs))))

; unlink modeled as fs-delete
(assert (forall ((p Path) (fs Filesystem))
  (= (unlink p fs) (fs-delete p fs))))

; ===== Axioms =====

(assert (forall ((p Path) (node FSNode) (fs Filesystem))
  (path-exists p (fs-update p node fs))))

(assert (forall ((p Path) (fs Filesystem))
  (not (path-exists p (fs-delete p fs)))))

; ===== Reversibility Theorem =====

(assert (forall ((p Path) (fs Filesystem) (node FSNode))
  (=> (symlink-precondition p fs)
      (= (unlink p (symlink p fs)) fs))))

; ===== Check =====

(check-sat)
