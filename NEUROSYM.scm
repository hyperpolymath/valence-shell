;; NEUROSYM.scm — Neurosymbolic Integration Policy
;; SPDX-License-Identifier: AGPL-3.0-or-later
;; SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell
;;
;; Defines the integration between neural (LLM) and symbolic (formal proofs)
;; components in Valence Shell. NeSy = Neurosymbolic AI.
;;
;; Core principle: Neural systems propose, symbolic systems verify.

(neurosym
  (version . "0.1.0")
  (project . "valence-shell")
  (purpose . "Neural-symbolic integration for verified shell operations"))

;;; ===================================================================
;;; ARCHITECTURE OVERVIEW
;;; ===================================================================

(architecture

  ;; The hybrid stack
  (layers
    ((layer . "neural")
     (role . "intention parsing, plan generation, natural language")
     (components . ("LLM" "embeddings" "retrieval"))
     (trust . "low - must be verified"))

    ((layer . "symbolic")
     (role . "formal verification, proof checking, invariant enforcement")
     (components . ("Coq" "ECHIDNA" "type system"))
     (trust . "high - mathematical guarantees"))

    ((layer . "bridge")
     (role . "translation between neural and symbolic representations")
     (components . ("DSL parser" "proof sketch generator" "counterexample analyzer"))
     (trust . "medium - correctness depends on implementation")))

  ;; Data flow
  (flow
    "User intent (natural language)"
    "  → Neural: Parse to structured command"
    "  → Bridge: Translate to formal specification"
    "  → Symbolic: Check preconditions, generate proof obligations"
    "  → Bridge: Translate proof result to execution decision"
    "  → Execution: Run verified command"
    "  → Symbolic: Verify postconditions"
    "  → Neural: Generate human-readable summary"))

;;; ===================================================================
;;; NEURAL COMPONENT POLICY
;;; ===================================================================

(neural-policy

  ;; What neural components can do
  (capabilities
    ((capability . "intent-parsing")
     (description . "Convert natural language to structured command")
     (example . "'make a backup of config' → Valence.Commands.Copy{src: 'config', dst: 'config.bak'}"))

    ((capability . "plan-generation")
     (description . "Propose multi-step operation sequences")
     (constraint . "Plans must be validated symbolically before execution"))

    ((capability . "error-explanation")
     (description . "Translate symbolic errors to natural language")
     (example . "{:drift, :exists, :missing} → 'Expected file to exist but it was not found'"))

    ((capability . "compensation-suggestion")
     (description . "Propose recovery actions when compensation fails")
     (constraint . "Suggestions must be verified before execution")))

  ;; What neural components CANNOT do
  (limitations
    ("Cannot execute commands directly - must go through symbolic layer")
    ("Cannot bypass formal verification")
    ("Cannot modify proof obligations")
    ("Cannot override safety constraints")
    ("Cannot access files outside sandbox"))

  ;; Model requirements
  (model-requirements
    ((requirement . "structured-output")
     (description . "Must produce parseable command structures")
     (format . "JSON or S-expression"))

    ((requirement . "uncertainty-aware")
     (description . "Must express confidence levels")
     (threshold . "Operations only proceed if confidence > 0.8"))

    ((requirement . "explainable")
     (description . "Must provide reasoning chain")
     (use . "Audit trail and human review"))))

;;; ===================================================================
;;; SYMBOLIC COMPONENT POLICY
;;; ===================================================================

(symbolic-policy

  ;; Proof systems in use
  (proof-systems
    ((system . "coq")
     (role . "Primary verification - reversibility proofs")
     (location . "proofs/coq/")
     (trust . "highest"))

    ((system . "echidna")
     (role . "Multi-solver verification")
     (integration . "github.com/hyperpolymath/echidna")
     (solvers . ("coq" "lean4" "agda" "isabelle" "mizar" "z3")))

    ((system . "elixir-types")
     (role . "Runtime type checking via dialyzer")
     (trust . "medium")))

  ;; Verification requirements
  (verification-requirements
    ((operation-class . "reversible")
     (proof-required . "F⁻¹(F(s)) = s for operation F")
     (verified-in . ("coq" "lean4")))

    ((operation-class . "composition")
     (proof-required . "Sequence reversibility")
     (verified-in . ("coq" "agda")))

    ((operation-class . "independence")
     (proof-required . "Operations on different paths don't interfere")
     (verified-in . ("coq" "isabelle"))))

  ;; Proof obligation generation
  (proof-obligations
    ((trigger . "New command implementation")
     (obligations
       ("Reversibility theorem")
       ("Precondition characterization")
       ("Compensation correctness")))

    ((trigger . "Command composition")
     (obligations
       ("Sequence reversibility")
       ("Independence from other operations")))))

;;; ===================================================================
;;; BRIDGE LAYER
;;; ===================================================================

(bridge-layer

  ;; Neural → Symbolic translation
  (neural-to-symbolic
    ((input . "Structured command from LLM")
     (output . "Formal specification in proof language")
     (process
       ((step . 1)
        (action . "Parse command structure"))
       ((step . 2)
        (action . "Look up formal model for command type"))
       ((step . 3)
        (action . "Instantiate with concrete arguments"))
       ((step . 4)
        (action . "Generate proof obligations"))))

    ;; Example translation
    (example
      (neural-output . "{command: 'mkdir', args: {path: '/tmp/foo'}}")
      (symbolic-spec . "(mkdir '/tmp/foo' fs)")
      (proof-obligation . "rmdir '/tmp/foo' (mkdir '/tmp/foo' fs) = fs")))

  ;; Symbolic → Neural translation
  (symbolic-to-neural
    ((input . "Proof result or error")
     (output . "Natural language explanation")
     (templates
       ((pattern . "proof-success")
        (template . "Operation verified: {operation} is reversible"))

       ((pattern . "proof-failure")
        (template . "Verification failed: {reason}. The operation {operation} may not be reversible because {explanation}"))

       ((pattern . "precondition-violation")
        (template . "Cannot proceed: {precondition} is not satisfied"))

       ((pattern . "drift-detected")
        (template . "State mismatch: expected {expected}, found {actual}")))))

  ;; Counterexample analysis
  (counterexample-handling
    ((on-counterexample
      (action . "Translate to concrete scenario")
      (present . "Show user what would go wrong")
      (suggest . "Alternative approaches that satisfy constraints")))))

;;; ===================================================================
;;; VERIFICATION PIPELINE
;;; ===================================================================

(verification-pipeline

  ;; Fast path: already verified
  (fast-path
    (condition . "Command has cached proof certificate")
    (action . "Check certificate validity, execute"))

  ;; Standard path: verification required
  (standard-path
    ((phase . "pre-check")
     (actions
       ("Parse command")
       ("Load formal model")
       ("Check preconditions symbolically")))

    ((phase . "proof-check")
     (actions
       ("Retrieve or generate proof obligation")
       ("Verify with primary prover (Coq)")
       ("Optional: cross-validate with ECHIDNA")))

    ((phase . "execute")
     (condition . "Proof check passed")
     (actions
       ("Execute command")
       ("Record compensation")
       ("Verify postcondition")))

    ((phase . "reject")
     (condition . "Proof check failed")
     (actions
       ("Log failure reason")
       ("Translate to natural language")
       ("Suggest alternatives if possible"))))

  ;; Slow path: novel operation
  (slow-path
    (condition . "No existing proof for operation pattern")
    (actions
      ("Flag for human review")
      ("Optionally: attempt proof synthesis")
      ("Cache result for future use"))))

;;; ===================================================================
;;; ECHIDNA INTEGRATION
;;; ===================================================================

(echidna-integration

  ;; ECHIDNA: Multi-solver proof verification
  (purpose . "Cross-validate proofs across multiple proof systems")

  (configuration
    ((solvers . ("coq" "lean4" "agda" "isabelle" "mizar" "z3"))
     (mode . "consensus")
     (threshold . "majority (4/6)")
     (timeout . "60 seconds per solver")))

  ;; Verification workflow
  (workflow
    ((step . 1)
     (action . "Submit proof obligation to ECHIDNA"))
    ((step . 2)
     (action . "ECHIDNA distributes to configured solvers"))
    ((step . 3)
     (action . "Collect results with proofs/counterexamples"))
    ((step . 4)
     (action . "Aggregate: consensus, majority, or conflict"))
    ((step . 5)
     (action . "Return verdict with confidence level")))

  ;; Conflict resolution
  (conflict-resolution
    ((scenario . "Solvers disagree")
     (action . "Flag for human review")
     (data . "Provide all proofs and counterexamples"))

    ((scenario . "Timeout on some solvers")
     (action . "Proceed with available results if threshold met")
     (warning . "Mark as partially verified"))))

;;; ===================================================================
;;; LEARNING AND ADAPTATION
;;; ===================================================================

(learning

  ;; Proof caching
  (proof-cache
    (storage . "Local + distributed")
    (key . "(command-type, argument-patterns)")
    (value . "(proof-certificate, validation-timestamp)")
    (ttl . "Until proof system update"))

  ;; Pattern learning
  (pattern-learning
    (purpose . "Learn common operation sequences for faster verification")
    (input . "Successful operation sequences")
    (output . "Reusable composition proofs")
    (constraint . "Human approval for new patterns"))

  ;; Failure learning
  (failure-learning
    (purpose . "Learn from verification failures to improve suggestions")
    (input . "Failed proof attempts with counterexamples")
    (output . "Updated heuristics for neural planner")
    (constraint . "Does not affect symbolic verification")))

;;; ===================================================================
;;; TRUST AND AUDIT
;;; ===================================================================

(trust-model

  ;; Trust hierarchy
  (hierarchy
    ((level . 1)
     (component . "Formal proofs (Coq, etc.)")
     (trust . "Mathematical certainty"))

    ((level . 2)
     (component . "ECHIDNA cross-validation")
     (trust . "High - multiple independent verifications"))

    ((level . 3)
     (component . "Type system (Elixir/Dialyzer)")
     (trust . "Medium - compile-time guarantees"))

    ((level . 4)
     (component . "Neural components")
     (trust . "Low - must be verified symbolically")))

  ;; Audit trail
  (audit
    (events
      ("Neural interpretation generated")
      ("Proof obligation created")
      ("Verification attempted")
      ("Verification succeeded/failed")
      ("Execution approved/rejected")
      ("Compensation recorded"))

    (retention . "Indefinite for security-relevant operations")
    (format . "Structured log with cryptographic integrity")))

;;; ===================================================================
;;; RESEARCH DIRECTIONS
;;; ===================================================================

(research-directions

  ;; Future capabilities
  (planned
    ((name . "proof-synthesis")
     (description . "Neural-guided proof search")
     (status . "research")
     (constraint . "All synthesized proofs must be machine-checked"))

    ((name . "natural-language-proofs")
     (description . "Explain proofs in natural language")
     (status . "research")
     (use . "Education and debugging"))

    ((name . "adversarial-robustness")
     (description . "Detect attempts to bypass verification")
     (status . "planned")
     (importance . "critical for production")))

  ;; Open questions
  (open-questions
    ("How to handle probabilistic neural outputs in deterministic verification?")
    ("Can we verify neural component behavior formally?")
    ("What is the right balance between verification thoroughness and latency?")
    ("How to handle partial verification when full proof is intractable?")))
