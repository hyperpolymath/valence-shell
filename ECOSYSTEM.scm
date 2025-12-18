;; ECOSYSTEM.scm — Valence Shell Entry
;; For inclusion in /overview repository
;;
;; This file documents valence-shell's place in the broader ecosystem.
;; Copy/merge this into the main ECOSYSTEM.scm in /overview

;;; ===================================================================
;;; VALENCE SHELL — Layer 2 Application
;;; ===================================================================

(
  (name . "valence-shell")
  (display-name . "Valence Shell")
  (layer . 2)  ; Application layer
  (category . "shells-and-runtimes")

  (repository
    (primary . "gitlab.com/hyperpolymath/valence-shell")
    (location . "_maaf/5 shells and target runtimes/valence-shell/"))

  (status . active)
  (priority . 5)  ; Top 5 project
  (rsr-tier . rhodium)

  (purpose . "Reversible shell with transactional semantics — every command has an inverse")

  (languages . ("elixir" "coq"))
  (banned . ("python" "typescript"))

  ;; Relationships
  (depends-on
    ((project . svalinn)
     (relationship . "container-base")
     (layer . 0))

    ((project . cerro-torre)
     (relationship . "orchestration")
     (layer . 0)))

  (validated-by
    ((project . echidna)
     (relationship . "proof-verification")
     (layer . 3)))

  (part-of
    ((framework . "MAA")
     (primitives . ("RMR" "RMO"))))

  ;; MCP Integration (future)
  (mcp-parent . "poly-shell-mcp")  ; When created

  ;; Documentation
  (sacred-files . ("README.adoc" "STATE.adoc" "META.scm"))

  ;; Recovery note
  (notes . "README destroyed 2025-12-18, reconstructed from conversation fragments")
)

;;; ===================================================================
;;; RELATED ENTRIES (for context)
;;; ===================================================================

;; These should already exist in ECOSYSTEM.scm, shown here for reference:

#|
;; Layer 0 — Infrastructure (valence-shell depends on these)
(
  (name . "svalinn")
  (layer . 0)
  (category . "infrastructure")
  (purpose . "Container security standards and base images")
  (repository . "github.com/hyperpolymath/svalinn")
)

(
  (name . "cerro-torre")
  (layer . 0)
  (category . "infrastructure")
  (purpose . "Container orchestration patterns")
  (repository . "github.com/hyperpolymath/cerro-torre")
)

;; Layer 3 — Solving (validates valence-shell)
(
  (name . "echidna")
  (layer . 3)
  (category . "solving")
  (purpose . "Multi-solver proof verification (12+ solvers, neurosymbolic)")
  (repository . "github.com/hyperpolymath/echidna")
)
|#

;;; ===================================================================
;;; LAYER STRUCTURE REFERENCE
;;; ===================================================================

#|
Layer 0 — Infrastructure (underpins everything)
  └── svalinn, cerro-torre, conative-gating

Layer 1 — MCPs (tool coordination)
  └── poly-ssg-mcp, poly-db-mcp, poly-container-mcp, poly-shell-mcp (future)

Layer 2 — Applications (the actual tools)
  └── valence-shell, defiant, echomesh, etc.

Layer 3 — Solving (cross-cutting verification)
  └── echidna, echidnabot

Overview — The map
  └── /overview repository with ECOSYSTEM.scm
|#
