;; META.scm — Valence Shell Project Metadata
;; Machine-readable, human-inspectable
;; Last updated: 2025-12-18

(project
  (name . "valence-shell")
  (display-name . "Valence Shell")
  (tagline . "The Thermodynamic Shell — Every Command is Reversible")
  (version . "0.1.0-alpha")
  (status . planning)
  (phase . 1)  ; Hypervisor phase

  (repository
    (primary . "gitlab.com/hyperpolymath/valence-shell")
    (mirrors . ("github.com/hyperpolymath/valence-shell")))

  (author
    (name . "Jonathan D.A. Jewell")
    (email . "jonathan.jewell@open.ac.uk")
    (affiliation . "The Open University"))

  (licence . "AGPL-3.0-or-later WITH Palimpsest-overlay"))

(classification
  (rsr-tier . rhodium)  ; Highest standard
  (layer . 2)           ; Application layer
  (category . shell)
  (priority . 5)        ; Top 5 project

  (tags . ("shell" "reversible" "transactions" "saga" "elixir" "formal-verification")))

(technology
  (primary-language . elixir)
  (proof-language . coq)
  (container-base . svalinn)
  (orchestration . cerro-torre)

  (dependencies
    (runtime . ("elixir" "erlang/otp"))
    (build . ("mix" "coq"))
    (test . ("stream_data")))

  (banned . ("python" "typescript" "coffeescript" "go" "docker" "npm")))

(architecture
  (pattern . "OTP Supervision Tree + Saga Pattern")
  (core-abstraction . "Valence.Command behaviour")

  (components
    ((name . command-behaviour)
     (file . "lib/valence/command.ex")
     (purpose . "4-callback contract for reversible operations"))

    ((name . history-zipper)
     (file . "lib/valence/history/zipper.ex")
     (purpose . "O(1) in-memory undo/redo"))

    ((name . saga-orchestrator)
     (file . "lib/valence/saga.ex")
     (purpose . "Compensating transaction management"))

    ((name . idempotency-journal)
     (file . "lib/valence/history/journal.ex")
     (purpose . "Crash recovery via completion flags"))

    ((name . reversibility-proof)
     (file . "proofs/coq/rmr.v")
     (purpose . "Formal proof that F⁻¹(F(s)) = s"))))

(roadmap
  ((phase . 1)
   (name . "Hypervisor")
   (status . planning)
   (description . "Supervise /bin/sh, intercept reversible commands"))

  ((phase . 2)
   (name . "Hybrid Shim")
   (status . future)
   (description . "LD_PRELOAD syscall interception for any binary"))

  ((phase . 3)
   (name . "AST Transpiler")
   (status . future)
   (description . "Parse shell syntax → Elixir AST for static analysis")))

(integration
  (part-of . "MAA Framework (Mutually Assured Accountability)")

  (uses
    ((project . echidna)
     (purpose . "Multi-solver proof verification")
     (repo . "github.com/hyperpolymath/echidna"))

    ((project . svalinn)
     (purpose . "Container base images")
     (repo . "github.com/hyperpolymath/svalinn"))

    ((project . cerro-torre)
     (purpose . "Container orchestration")
     (repo . "github.com/hyperpolymath/cerro-torre")))

  (implements
    ((primitive . RMR)
     (description . "Reversible Mutation Record — every command has inverse"))

    ((primitive . RMO)
     (description . "Reversible Mutation Obliteration — secure deletion"))))

(sacred-files
  ;; These files must not be modified by AI without explicit confirmation
  ("README.adoc" . "Project vision — catastrophic if lost")
  ("STATE.adoc" . "Cross-conversation context — append only")
  ("ARCHITECTURE.md" . "Design decisions")
  ("META.scm" . "This file"))

(history
  ((date . "2025-12-18")
   (event . "README recovered after AI destruction")
   (notes . "Original content lost, reconstructed from conversation fragments"))

  ((date . "2025-12-07")
   (event . "Python contamination discovered")
   (notes . "~100 Oils shell Python files found, flagged for deletion")))
