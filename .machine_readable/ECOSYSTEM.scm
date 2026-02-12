;; SPDX-License-Identifier: PMPL-1.0-or-later
;; ECOSYSTEM.scm - Ecosystem Positioning
;; valence-shell
;;
;; IMPORTANT: Satellite relationships must be kept up to date.
;; When adding/removing satellites, update this file and the satellite's ECOSYSTEM.scm.

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
    (reason . "Both implement MAA framework primitives")))

  (what-this-is
   "Formally verified shell with ~200+ theorems across 6 proof systems (41 proof holes remain — see docs/PROOF_HOLES_AUDIT.md)"
   "Advanced research prototype with working shell features (v0.9.0, ~65% complete)"
   "Functional shell with pipelines, redirections, variables, job control, process substitution"
   "Implementation of MAA (Mutually Assured Accountability) framework"
   "525 tests passing, 15 ignored (0 failures)"
   "15,720 lines of Rust across 30 source files"
   "Incremental path toward full POSIX shell compliance with verification at each step")

  (what-this-is-not
   "NOT production-ready (extraction gap between proofs and implementation)"
   "NOT formally verified end-to-end (Lean → Rust correspondence ~85% confidence, not proven)"
   "NOT a full POSIX shell yet (many features missing per docs/POSIX_COMPLIANCE.md)"
   "NOT a replacement for bash/zsh in current state"
   "NOT v1.0.0 despite what Cargo.toml previously claimed (corrected to 0.9.0)")

  ;; Maintenance note: Review satellite relationships when:
  ;; - Adding new repos with similar suffix patterns (-ssg, -mcp, -scm, -ffi)
  ;; - Removing or archiving repos
  ;; - Changing the portfolio structure
  (maintenance-checks
   (satellite-sync . "Ensure parent and satellite ECOSYSTEM.scm files are consistent")
   (portfolio-review . "Verify all satellites are listed in parent repo")))
