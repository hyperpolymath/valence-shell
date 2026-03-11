;; SPDX-License-Identifier: PMPL-1.0-or-later
(bot-directive
  (bot "echidnabot")
  (scope "formal verification, proof correspondence, and property-based testing")
  (languages ("Rust" "Lean4" "Coq" "Agda" "Isabelle" "Mizar"))
  (targets
    ("impl/rust-cli/src/" "Rust shell implementation")
    ("proofs/" "Multi-prover formal proofs")
    ("impl/rust-cli/tests/" "Correspondence and property tests"))
  (allow ("analysis" "fuzzing" "proof checks" "property testing" "proof-hole auditing"))
  (deny ("write to core modules" "write to bindings" "modify proof axioms"))
  (scanning-rules
    (rust
      (ban ("unsafe" "transmute") (unless "// SAFETY: comment present"))
      (flag ("unwrap" "expect") (severity "medium")))
    (lean4
      (ban ("sorry") (severity "critical") (notes "proof holes must be closed"))
      (flag ("axiom") (severity "high")))
    (coq
      (ban ("Admitted") (severity "critical"))
      (flag ("Axiom") (severity "high")))
    (agda
      (ban ("postulate") (severity "critical"))))
  (notes "May open findings; code changes require explicit approval. Proof hole count must not increase."))
