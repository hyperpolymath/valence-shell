; SPDX-License-Identifier: PMPL-1.0-or-later
;; guix.scm — GNU Guix package definition for valence-shell
;; Usage: guix shell -f guix.scm

(use-modules (guix packages)
             (guix build-system gnu)
             (guix licenses))

(package
  (name "valence-shell")
  (version "0.1.0")
  (source #f)
  (build-system gnu-build-system)
  (synopsis "valence-shell")
  (description "valence-shell — part of the hyperpolymath ecosystem.")
  (home-page "https://github.com/hyperpolymath/valence-shell")
  (license ((@@ (guix licenses) license) "PMPL-1.0-or-later"
             "https://github.com/hyperpolymath/palimpsest-license")))
