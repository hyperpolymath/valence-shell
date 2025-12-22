# justfile — Valence Shell Task Automation
# https://github.com/casey/just

# Default recipe: show help
default:
    @just --list

# === SETUP ===

# Fetch all dependencies
deps:
    mix deps.get

# Install git hooks (sacred file protection, contamination blocking)
install-hooks:
    @./scripts/install-hooks.sh

# Full setup: deps + hooks
setup: deps install-hooks
    @echo "✅ Valence Shell ready for development"

# Create database (if using Ecto with backing store)
db-setup:
    mix ecto.create
    mix ecto.migrate

# === BUILD ===

# Compile the project
build:
    mix compile

# Clean build artifacts
clean:
    mix clean
    rm -rf _build deps

# Deep clean (including generated files)
clean-all: clean
    rm -rf proofs/coq/extracted/
    find proofs -name "*.vo" -delete 2>/dev/null || true
    find proofs -name "*.vok" -delete 2>/dev/null || true
    find proofs -name "*.vos" -delete 2>/dev/null || true
    find proofs -name "*.glob" -delete 2>/dev/null || true

# === TEST ===

# Run all tests
test:
    mix test

# Run tests with coverage
test-cover:
    mix test --cover

# Run property-based tests only
test-props:
    mix test test/property/

# Run tests continuously on file change
test-watch:
    mix test.watch

# === VERIFICATION ===

# Full verification: format + lint + test + typecheck
verify: format-check lint test typecheck

# Check code formatting
format-check:
    mix format --check-formatted

# Format all code
format:
    mix format

# Run Credo linter
lint:
    mix credo --strict

# Run Dialyzer type checking
typecheck:
    mix dialyzer

# === PROOFS ===

# Run Coq proofs (requires coqc)
prove:
    @echo "Running Coq proofs..."
    cd proofs/coq && coqc rmr.v
    @echo "✅ Reversibility axiom verified"

# Check proofs with ECHIDNA (if available)
prove-echidna:
    @echo "Verifying with ECHIDNA multi-solver..."
    echidna verify proofs/coq/rmr.v --solvers=all

# Build all proof systems (legacy proofs)
build-proofs:
    @echo "Building proof systems..."
    @if [ -f proofs/coq/filesystem_model.v ]; then \
        cd proofs/coq && coqc filesystem_model.v; \
    fi
    @echo "✅ Proofs built"

# === RUN ===

# Start the shell (interactive)
run:
    iex -S mix

# Start with Phoenix endpoint (if GUI enabled)
run-web:
    mix phx.server

# Start in production mode
run-prod:
    MIX_ENV=prod mix run --no-halt

# === DEVELOPMENT ===

# Open IEx with project loaded
console:
    iex -S mix

# Generate documentation
docs:
    mix docs

# Show outdated dependencies
outdated:
    mix hex.outdated

# Update dependencies
update:
    mix deps.update --all

# === CONTAINER ===

# Build container image (Podman)
container-build:
    podman build -t valence-shell:latest .

# Run in container
container-run:
    podman run -it --rm valence-shell:latest

# Push to registry
container-push registry:
    podman push valence-shell:latest {{registry}}/valence-shell:latest

# === RELEASE ===

# Build release
release:
    MIX_ENV=prod mix release

# === SAFETY ===

# Check for Python contamination (should find nothing)
check-contamination:
    @echo "Checking for banned languages..."
    @if find . -name "*.py" -not -path "./_build/*" -not -path "./deps/*" | grep -q .; then \
        echo "❌ PYTHON CONTAMINATION DETECTED:"; \
        find . -name "*.py" -not -path "./_build/*" -not -path "./deps/*"; \
        exit 1; \
    else \
        echo "✅ No Python files found"; \
    fi
    @if find . -name "*.ts" -not -path "./node_modules/*" | grep -q .; then \
        echo "❌ TYPESCRIPT CONTAMINATION DETECTED:"; \
        find . -name "*.ts" -not -path "./node_modules/*"; \
        exit 1; \
    else \
        echo "✅ No TypeScript files found"; \
    fi
    @echo "✅ Repository clean"

# Verify sacred files haven't been tampered with
check-sacred:
    @echo "Verifying sacred files..."
    @git diff --name-only HEAD~1 | grep -E "README.adoc|STATE.adoc|ARCHITECTURE.md|META.scm" && \
        echo "⚠️  SACRED FILE MODIFIED - verify this was intentional" || \
        echo "✅ Sacred files unchanged"

# === CI ===

# Full CI pipeline
ci: check-contamination verify prove
    @echo "✅ CI pipeline passed"

# === STATS ===

# Project statistics
stats:
    @echo "=== Valence Shell Statistics ==="
    @echo ""
    @echo "Elixir Code:"
    @find lib -name "*.ex" 2>/dev/null | xargs wc -l 2>/dev/null | tail -1 || echo "  (not scaffolded yet)"
    @echo ""
    @echo "Proof Code:"
    @find proofs -name "*.v" 2>/dev/null | xargs wc -l 2>/dev/null | tail -1 || echo "  (not written yet)"
    @echo ""
    @echo "Tests:"
    @find test -name "*.exs" 2>/dev/null | xargs wc -l 2>/dev/null | tail -1 || echo "  (not written yet)"

# === HELP ===

# Show detailed help
help:
    @echo "Valence Shell - The Thermodynamic Shell"
    @echo ""
    @echo "Phase 1: Hypervisor (current)"
    @echo "  Supervise /bin/sh, intercept reversible commands"
    @echo ""
    @echo "Common commands:"
    @echo "  just deps            - Fetch dependencies"
    @echo "  just build           - Compile project"
    @echo "  just test            - Run tests"
    @echo "  just verify          - Full verification"
    @echo "  just prove           - Run Coq proofs"
    @echo "  just run             - Start the shell"
    @echo ""
    @echo "Safety:"
    @echo "  just check-contamination - Verify no Python/TS"
    @echo "  just check-sacred        - Verify sacred files"
    @echo ""
    @echo "For full list: just --list"
