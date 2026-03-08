;; SPDX-License-Identifier: PMPL-1.0-or-later
;; ECOSYSTEM.scm - Ecosystem Positioning
;; valence-shell
;;
;; Updated 2026-03-08 (P9 security audit)

(ecosystem
  (version . "0.9.0")
  (name . "valence-shell")
  (type . "application")
  (purpose . "Formally verified shell with proven reversibility guarantees and MAA framework")

  (position-in-ecosystem
   (category . "system-software")
   (layer . "user-interface"))

  (related-projects
   ((name . "absolute-zero")
    (relationship . "inspiration")
    (reason . "CNO (Certified Null Operation) composition theory"))
   ((name . "echidna")
    (relationship . "potential-consumer")
    (reason . "Could use verified filesystem operations"))
   ((name . "januskey")
    (relationship . "sibling-standard")
    (reason . "Both implement MAA framework primitives"))
   ((name . "proven-servers")
    (relationship . "sibling")
    (reason . "Shares formal verification approach and proof patterns")))

  (what-this-is
   "Formally verified shell with ~250+ theorems across 6 proof systems (4 proof gaps remain)"
   "Advanced research prototype with working shell features (v0.9.0, ~72% complete)"
   "Functional shell with pipelines, redirections, variables, control structures, job control"
   "Reversible builtins: mkdir/rmdir/touch/rm/cp/mv/ln/chmod/chown — all with proofs in 6 systems"
   "Implementation of MAA (Mutually Assured Accountability) framework"
   "602 tests passing, 14 ignored (0 failures)"
   "15,720 lines of Rust across 30 source files"
   "Incremental path toward full POSIX shell compliance with verification at each step")

  (what-this-is-not
   "NOT production-ready (extraction gap between proofs and implementation)"
   "NOT formally verified end-to-end (Lean → Rust correspondence ~95% confidence, not proven)"
   "NOT a full POSIX shell yet (functions and script execution missing)"
   "NOT a replacement for bash/zsh in current state")

  (maintenance-checks
   (satellite-sync . "Ensure parent and satellite ECOSYSTEM.scm files are consistent")
   (portfolio-review . "Verify all satellites are listed in parent repo")))
