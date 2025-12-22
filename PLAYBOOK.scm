;; PLAYBOOK.scm — Valence Shell Operational Playbooks
;; SPDX-License-Identifier: AGPL-3.0-or-later
;; SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell
;;
;; Defines operational patterns, recovery procedures, and standard workflows.
;; Machine-readable runbooks for both humans and AI agents.

(playbook
  (version . "0.1.0")
  (project . "valence-shell")
  (purpose . "Operational patterns for reversible shell operations"))

;;; ===================================================================
;;; RECOVERY PLAYBOOKS
;;; ===================================================================

(recovery-playbooks

  ;; Crash recovery: pending transactions
  ((name . "recover-pending-transactions")
   (trigger . "Application restart with pending journal entries")
   (steps
     ((step . 1)
      (action . "Query journal for :pending entries")
      (command . "Valence.Journal.pending_entries()"))
     ((step . 2)
      (action . "For each pending entry, verify state")
      (command . "entry.command.verify(entry.args)"))
     ((step . 3)
      (action . "If :ok, mark completed; if :drift, compensate")
      (decision
        (on-ok . "Journal.complete(key, :recovered, nil)")
        (on-drift . "Journal.fail(key, :incomplete)"))))
   (postcondition . "No pending entries remain"))

  ;; Undo cascade failure
  ((name . "undo-cascade-recovery")
   (trigger . "Compensation fails during undo")
   (steps
     ((step . 1)
      (action . "Log failure with full context")
      (data . "(command, args, compensation, error)"))
     ((step . 2)
      (action . "Attempt idempotent retry (max 3)")
      (retry-policy . ((max-attempts . 3) (backoff . exponential))))
     ((step . 3)
      (action . "If still failing, escalate to human")
      (escalation . "Create recovery ticket with state snapshot")))
   (postcondition . "Either compensated or human notified"))

  ;; Two Generals drift detection
  ((name . "drift-reconciliation")
   (trigger . "verify/1 returns {:drift, expected, actual}")
   (steps
     ((step . 1)
      (action . "Log drift event with full state"))
     ((step . 2)
      (action . "Determine if reconcilable")
      (decision
        (reconcilable . "Apply corrective operation")
        (not-reconcilable . "Escalate with snapshot")))
     ((step . 3)
      (action . "Update journal with reconciliation result")))
   (postcondition . "State matches expected or human notified")))

;;; ===================================================================
;;; OPERATIONAL PATTERNS
;;; ===================================================================

(operational-patterns

  ;; Standard command execution flow
  ((name . "execute-command")
   (pattern . "saga")
   (flow
     ((phase . "pre-flight")
      (actions . ("Generate idempotency key"
                  "Check journal for prior execution"
                  "Assess risk level via describe/1")))
     ((phase . "execution")
      (actions . ("Call execute/2"
                  "Capture compensation"
                  "Record in journal as :pending")))
     ((phase . "commit")
      (actions . ("Mark journal :completed"
                  "Push to history zipper"
                  "Return result")))
     ((phase . "rollback")
      (trigger . "execution failure")
      (actions . ("Mark journal :failed"
                  "No compensation needed (nothing changed)")))))

  ;; Batch operation pattern
  ((name . "batch-execute")
   (pattern . "saga-sequence")
   (description . "Execute multiple commands as atomic unit")
   (flow
     ((phase . "collect")
      (action . "Gather all commands with args"))
     ((phase . "validate")
      (action . "Pre-check all preconditions"))
     ((phase . "execute")
      (action . "Execute in order, collecting compensations"))
     ((phase . "commit-or-rollback")
      (on-success . "Commit all to history as single entry")
      (on-failure . "Compensate in reverse order"))))

  ;; Interactive session pattern
  ((name . "interactive-session")
   (pattern . "repl-with-history")
   (features
     ("Undo last command: Ctrl+Z or 'undo'")
     ("Redo undone command: Ctrl+Y or 'redo'")
     ("Show history: 'history'")
     ("Jump to point: 'history goto N'"))))

;;; ===================================================================
;;; DANGER ZONE PLAYBOOKS
;;; ===================================================================

(danger-playbooks

  ;; Handling :danger operations
  ((name . "danger-confirmation")
   (trigger . "describe/1 returns :danger")
   (steps
     ((step . 1)
      (action . "Display warning with impact assessment"))
     ((step . 2)
      (action . "Require explicit confirmation")
      (prompt . "This operation may be irreversible. Proceed? [y/N]"))
     ((step . 3)
      (action . "If confirmed, capture maximum state for compensation")
      (capture . "Full file content, permissions, ownership, timestamps")))
   (note . "Danger ops get extra state capture for best-effort recovery"))

  ;; External system compensation
  ((name . "external-compensation")
   (trigger . "Operation affects external system (API, DB, network)")
   (steps
     ((step . 1)
      (action . "Generate compensating transaction BEFORE execution")
      (example . "DELETE /api/resource/123 → POST /api/resource with saved body"))
     ((step . 2)
      (action . "Store compensation with TTL")
      (ttl . "24 hours default, configurable"))
     ((step . 3)
      (action . "On undo, execute compensation")
      (warning . "External state may have changed - verify first")))
   (limitation . "Cannot guarantee external system reversibility")))

;;; ===================================================================
;;; MAINTENANCE PLAYBOOKS
;;; ===================================================================

(maintenance-playbooks

  ;; Journal compaction
  ((name . "compact-journal")
   (trigger . "Journal size exceeds threshold OR weekly schedule")
   (steps
     ((step . 1)
      (action . "Archive completed entries older than retention period"))
     ((step . 2)
      (action . "Verify no pending entries in archive range"))
     ((step . 3)
      (action . "Write archive to persistent storage"))
     ((step . 4)
      (action . "Truncate active journal")))
   (retention . "7 days default, configurable"))

  ;; History pruning
  ((name . "prune-history")
   (trigger . "History depth exceeds limit")
   (steps
     ((step . 1)
      (action . "Identify oldest entries beyond limit"))
     ((step . 2)
      (action . "Archive to persistent storage (optional)"))
     ((step . 3)
      (action . "Remove from in-memory zipper")))
   (limit . "1000 entries default, configurable")))

;;; ===================================================================
;;; EMERGENCY PROCEDURES
;;; ===================================================================

(emergency-procedures

  ((name . "full-rollback")
   (description . "Roll back all operations to session start")
   (danger-level . :critical)
   (steps
     ((step . 1)
      (action . "Confirm with user - this cannot be undone"))
     ((step . 2)
      (action . "Execute compensations from newest to oldest"))
     ((step . 3)
      (action . "Clear history zipper"))
     ((step . 4)
      (action . "Log full session for audit"))))

  ((name . "state-snapshot")
   (description . "Capture complete system state for debugging")
   (output . "Tarball with journal, history, and filesystem state")))
