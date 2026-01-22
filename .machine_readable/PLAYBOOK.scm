;; SPDX-License-Identifier: PLMP-1.0-or-later
;; PLAYBOOK.scm - Operational runbook for valence-shell

(define playbook
  `((version . "1.0.0")
    (procedures
      ((deploy . (("build" . "just build")
                  ("test" . "just test")
                  ("release" . "just release")))
       (rollback . ())
       (debug . ())))
    (alerts . ())
    (contacts . ())))
