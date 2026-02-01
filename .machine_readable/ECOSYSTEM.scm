;; SPDX-License-Identifier: PMPL-1.0-or-later
;; ECOSYSTEM.scm - Ecosystem Positioning
;; valence-shell
;;
;; IMPORTANT: Satellite relationships must be kept up to date.
;; When adding/removing satellites, update this file and the satellite's ECOSYSTEM.scm.

(ecosystem
  (version . "1.0.0")
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
    (reason . "Both implement MAA framework primitives")))

  (what-this-is
   "Formally verified shell with ~256 theorems across 6 proof systems"
   "Advanced research prototype with working shell features (v0.14.0, 82% complete)"
   "Functional shell with pipelines, redirections, variables, job control, process substitution"
   "Implementation of MAA (Mutually Assured Accountability) framework"
   "177 tests passing (131 unit + 27 integration + 19 property tests)"
   "Incremental path toward full POSIX shell compliance with verification at each step")

  (what-this-is-not
   "NOT production-ready (extraction gap between proofs and implementation)"
   "NOT formally verified end-to-end (Lean → Rust correspondence 85% confidence, not proven)"
   "NOT a full POSIX shell yet (missing glob expansion, quote processing)"
   "NOT a replacement for bash/zsh in current state (lacks some scripting features)"
   "NOT optimized for performance (verification prioritized over speed)")

  ;; Maintenance note: Review satellite relationships when:
  ;; - Adding new repos with similar suffix patterns (-ssg, -mcp, -scm, -ffi)
  ;; - Removing or archiving repos
  ;; - Changing the portfolio structure
  (maintenance-checks
   (satellite-sync . "Ensure parent and satellite ECOSYSTEM.scm files are consistent")
   (portfolio-review . "Verify all satellites are listed in parent repo")))
