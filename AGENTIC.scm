;; AGENTIC.scm — Agentic AI Augmentation Policy
;; SPDX-License-Identifier: AGPL-3.0-or-later
;; SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell
;;
;; Defines how AI agents interact with Valence Shell:
;; - Capabilities and constraints
;; - Delegation boundaries
;; - Verification requirements
;; - Human-in-the-loop policies

(agentic
  (version . "0.1.0")
  (project . "valence-shell")
  (purpose . "AI agent integration policy for reversible shell operations"))

;;; ===================================================================
;;; AGENT CAPABILITY MODEL
;;; ===================================================================

(capability-model

  ;; Capability tiers - what agents can do autonomously
  (tiers
    ((tier . 0)
     (name . "read-only")
     (description . "Observe state, no mutations")
     (allowed . ("ls" "cat" "pwd" "history" "verify"))
     (requires-approval . #f))

    ((tier . 1)
     (name . "safe-reversible")
     (description . "Operations with proven reversibility")
     (allowed . ("mkdir" "rmdir" "touch" "cp" "mv"))
     (requires-approval . #f)
     (constraint . "Only within sandbox path"))

    ((tier . 2)
     (name . "warn-reversible")
     (description . "Reversible but with side effects")
     (allowed . ("write" "chmod" "chown"))
     (requires-approval . "batch > 5 operations")
     (constraint . "Log all operations"))

    ((tier . 3)
     (name . "dangerous")
     (description . "Potentially irreversible")
     (allowed . ("rm" "rm -rf" "external API calls"))
     (requires-approval . #t)
     (constraint . "Explicit human confirmation per operation"))

    ((tier . 4)
     (name . "forbidden")
     (description . "Never allowed for agents")
     (forbidden . ("sudo" "su" "chroot" "mount" "format" "dd"))
     (constraint . "Hard block, no override")))

  ;; Default tier for unknown operations
  (default-tier . 3))

;;; ===================================================================
;;; DELEGATION POLICY
;;; ===================================================================

(delegation-policy

  ;; When can an agent act autonomously?
  (autonomous-conditions
    ((condition . "Operation tier <= agent's authorized tier")
     (check . "agent.tier >= operation.tier"))

    ((condition . "Operation within sandbox boundaries")
     (check . "path.starts_with?(agent.sandbox_root)"))

    ((condition . "Rate limit not exceeded")
     (check . "agent.ops_this_minute < agent.rate_limit"))

    ((condition . "No pending human review")
     (check . "agent.pending_approvals.empty?()")))

  ;; Escalation triggers
  (escalation-triggers
    ("Operation requires higher tier than authorized")
    ("Path outside sandbox")
    ("Rate limit exceeded")
    ("Compensation failed")
    ("Drift detected during verification")
    ("Batch size exceeds threshold")
    ("External system interaction"))

  ;; Escalation protocol
  (escalation-protocol
    ((step . 1)
     (action . "Pause agent execution"))
    ((step . 2)
     (action . "Generate human-readable summary of intended action"))
    ((step . 3)
     (action . "Present options: approve / reject / modify / delegate"))
    ((step . 4)
     (action . "On approve: execute with audit trail")
     (action . "On reject: log and return error to agent")
     (action . "On modify: agent re-plans with constraints")
     (action . "On delegate: escalate to higher authority"))))

;;; ===================================================================
;;; VERIFICATION REQUIREMENTS
;;; ===================================================================

(verification-requirements

  ;; Pre-execution verification
  (pre-execution
    ((name . "precondition-check")
     (description . "Verify preconditions before execution")
     (applies-to . "all operations")
     (action . "Call command.verify/1 on current state"))

    ((name . "dry-run")
     (description . "Simulate operation without mutation")
     (applies-to . "tier >= 2")
     (action . "Execute with :dry_run flag, return diff"))

    ((name . "impact-assessment")
     (description . "Estimate scope of changes")
     (applies-to . "batch operations")
     (output . "List of affected paths, estimated reversibility")))

  ;; Post-execution verification
  (post-execution
    ((name . "state-verification")
     (description . "Confirm operation achieved intended result")
     (action . "Call command.verify/1, compare expected vs actual"))

    ((name . "compensation-readiness")
     (description . "Verify compensation is executable")
     (action . "Validate compensation args, check preconditions"))

    ((name . "audit-log")
     (description . "Record operation for accountability")
     (fields . ("agent_id" "operation" "args" "result"
                "compensation" "timestamp" "session_id")))))

;;; ===================================================================
;;; AGENT IDENTITY AND TRUST
;;; ===================================================================

(agent-identity

  ;; Agent registration
  (registration
    ((field . "agent_id")
     (type . "UUID")
     (generated . "On first connection"))

    ((field . "agent_class")
     (type . "enum")
     (values . ("claude" "copilot" "custom" "human-proxied")))

    ((field . "authorized_tier")
     (type . "integer 0-3")
     (default . 1))

    ((field . "sandbox_root")
     (type . "path")
     (required . #t))

    ((field . "rate_limit")
     (type . "ops/minute")
     (default . 60)))

  ;; Trust levels
  (trust-levels
    ((level . "untrusted")
     (tier . 0)
     (description . "New agent, read-only until verified"))

    ((level . "basic")
     (tier . 1)
     (description . "Verified agent, safe reversible ops"))

    ((level . "elevated")
     (tier . 2)
     (description . "Trusted agent, warn-level ops"))

    ((level . "privileged")
     (tier . 3)
     (description . "Highly trusted, can request dangerous ops"))

    ((level . "human-equivalent")
     (tier . 4)
     (description . "Human-in-the-loop, full access with confirmation"))))

;;; ===================================================================
;;; HUMAN-IN-THE-LOOP POLICIES
;;; ===================================================================

(human-in-the-loop

  ;; When human must be involved
  (mandatory-human
    ("First operation in new sandbox")
    ("Any tier-3 (dangerous) operation")
    ("Compensation failure")
    ("Rate limit exceeded 3x")
    ("Agent requests tier elevation")
    ("External system interaction")
    ("Session running > 4 hours without check-in"))

  ;; Human override capabilities
  (human-overrides
    ((name . "force-execute")
     (description . "Execute operation bypassing agent tier")
     (audit . "Full operation logged with human ID"))

    ((name . "force-compensate")
     (description . "Manually trigger compensation")
     (audit . "Compensation logged with reason"))

    ((name . "revoke-agent")
     (description . "Immediately terminate agent session")
     (action . "Compensate all pending, clear state"))

    ((name . "elevate-tier")
     (description . "Temporarily increase agent capabilities")
     (duration . "Single operation or time-limited")))

  ;; Notification channels
  (notifications
    ((channel . "terminal")
     (for . "Interactive sessions")
     (format . "Inline prompt"))

    ((channel . "webhook")
     (for . "Headless/daemon mode")
     (format . "JSON payload"))

    ((channel . "queue")
     (for . "Async approval workflows")
     (format . "Persistent message"))))

;;; ===================================================================
;;; CONATIVE GATING INTEGRATION
;;; ===================================================================

(conative-gating

  ;; Integration with github.com/hyperpolymath/conative-gating
  (integration
    (enabled . #t)
    (purpose . "AI enforcement layer for agent behavior"))

  ;; Gating rules
  (rules
    ((rule . "no-sacred-file-modification")
     (condition . "path in SACRED_FILES")
     (action . "block")
     (message . "Sacred files require human modification"))

    ((rule . "no-language-contamination")
     (condition . "file.extension in BANNED_EXTENSIONS")
     (action . "block")
     (message . "Banned language file creation blocked"))

    ((rule . "sandbox-enforcement")
     (condition . "NOT path.starts_with?(agent.sandbox)")
     (action . "block")
     (message . "Operation outside agent sandbox"))

    ((rule . "rate-limit-enforcement")
     (condition . "agent.ops_this_minute >= agent.rate_limit")
     (action . "pause")
     (message . "Rate limit reached, pausing agent")))

  ;; Banned extensions (RSR policy)
  (banned-extensions . (".py" ".ts" ".coffee" ".go")))

;;; ===================================================================
;;; AGENT SESSION LIFECYCLE
;;; ===================================================================

(session-lifecycle

  ;; Session initialization
  (on-connect
    ("Authenticate agent")
    ("Assign sandbox root")
    ("Set initial tier based on trust level")
    ("Initialize rate limiter")
    ("Create session journal"))

  ;; Session maintenance
  (heartbeat
    (interval . "60 seconds")
    (on-miss . "Pause agent, require re-authentication"))

  ;; Session termination
  (on-disconnect
    ((graceful . #t)
     (actions . ("Complete pending operations"
                 "Verify all compensations stored"
                 "Archive session journal"
                 "Release sandbox lock")))

    ((graceful . #f)
     (actions . ("Mark session as crashed"
                 "Flag pending operations for recovery"
                 "Notify human of unclean shutdown")))))

;;; ===================================================================
;;; METRICS AND OBSERVABILITY
;;; ===================================================================

(observability

  ;; Metrics to track
  (metrics
    ("agent.operations.total" . "counter")
    ("agent.operations.by_tier" . "counter")
    ("agent.escalations" . "counter")
    ("agent.compensations" . "counter")
    ("agent.drift_detected" . "counter")
    ("agent.session_duration" . "histogram"))

  ;; Audit events
  (audit-events
    ("agent.connected")
    ("agent.operation.requested")
    ("agent.operation.approved")
    ("agent.operation.rejected")
    ("agent.operation.executed")
    ("agent.escalation.triggered")
    ("agent.human.override")
    ("agent.disconnected")))
