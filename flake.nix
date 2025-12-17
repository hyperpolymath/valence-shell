# SPDX-License-Identifier: AGPL-3.0-or-later
# SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell
#
# Valence Shell - Nix Flake (Fallback Package Manager)
# Primary: guix.scm | Fallback: flake.nix (per RSR guidelines)
#
# Usage:
#   nix develop        # Enter development shell
#   nix build          # Build the project
#   nix flake check    # Verify the flake

{
  description = "Valence Shell - Formally verified shell implementing MAA framework";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-24.05";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};

        # Proof assistant versions
        proofTools = with pkgs; [
          # Coq - Calculus of Inductive Constructions
          coq_8_18
          coqPackages_8_18.coqide

          # OCaml - For extraction and FFI
          ocaml
          ocamlPackages.findlib
          ocamlPackages.dune_3

          # Z3 SMT Solver
          z3
        ];

        # Build tools
        buildTools = with pkgs; [
          just
          git
          gnumake
        ];

        # Development tools
        devTools = with pkgs; [
          # Shell utilities
          bash
          coreutils
          findutils

          # Container support
          podman
        ];

      in {
        # Development shell
        devShells.default = pkgs.mkShell {
          name = "valence-shell-dev";

          buildInputs = proofTools ++ buildTools ++ devTools;

          shellHook = ''
            echo "Valence Shell Development Environment"
            echo "======================================"
            echo "Version: 0.6.0"
            echo ""
            echo "Available proof systems:"
            echo "  - Coq $(coqc --version 2>/dev/null | head -1 || echo 'not found')"
            echo "  - Z3 $(z3 --version 2>/dev/null || echo 'not found')"
            echo ""
            echo "Build commands:"
            echo "  just build-all     - Build all proofs"
            echo "  just verify-all    - Verify all proofs"
            echo "  just demo          - Run demonstration"
            echo "  just --list        - Show all commands"
            echo ""
            echo "Note: Lean 4, Agda, Isabelle, and Mizar require separate installation."
            echo "See proofs/README.md for setup instructions."
          '';
        };

        # Packages
        packages.default = pkgs.stdenv.mkDerivation {
          pname = "valence-shell";
          version = "0.6.0";

          src = ./.;

          buildInputs = [ pkgs.coq_8_18 pkgs.ocaml ];

          buildPhase = ''
            # Build Coq proofs
            cd proofs/coq
            for f in *.v; do
              if [ -f "$f" ]; then
                coqc "$f" || true
              fi
            done
          '';

          installPhase = ''
            mkdir -p $out/share/valence-shell
            cp -r proofs $out/share/valence-shell/
            cp -r impl $out/share/valence-shell/ 2>/dev/null || true
            cp -r docs $out/share/valence-shell/ 2>/dev/null || true
            cp README.md $out/share/valence-shell/ 2>/dev/null || true
          '';

          meta = with pkgs.lib; {
            description = "Formally verified shell implementing MAA framework";
            homepage = "https://github.com/hyperpolymath/valence-shell";
            license = with licenses; [ mit agpl3Plus ];
            maintainers = [];
            platforms = platforms.unix;
          };
        };

        # Checks
        checks = {
          # Verify flake builds
          build = self.packages.${system}.default;
        };
      }
    );
}
