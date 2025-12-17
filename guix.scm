;; valence-shell - Guix Package Definition
;; Run: guix shell -D -f guix.scm

(use-modules (guix packages)
             (guix gexp)
             (guix git-download)
             (guix build-system gnu)
             ((guix licenses) #:prefix license:)
             (gnu packages base))

(define-public valence_shell
  (package
    (name "valence-shell")
    (version "0.6.0")
    (source (local-file "." "valence-shell-checkout"
                        #:recursive? #t
                        #:select? (git-predicate ".")))
    (build-system gnu-build-system)
    (synopsis "Formally verified shell implementing MAA framework")
    (description "Valence Shell - Formally verified shell with ~294 proofs across 6 proof systems (Coq, Lean 4, Agda, Isabelle/HOL, Mizar, Z3). Implements MAA (Mutually Assured Accountability) framework with proven reversibility guarantees.")
    (home-page "https://github.com/hyperpolymath/valence-shell")
    (license license:agpl3+)))

;; Return package for guix shell
valence_shell
