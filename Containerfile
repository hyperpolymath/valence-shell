# Valence Shell - Reproducible Verification Container
# Based on Fedora with all proof assistants installed
# Use with Podman or Docker

FROM fedora:39

LABEL org.opencontainers.image.title="Valence Shell"
LABEL org.opencontainers.image.description="Formally verified shell operations"
LABEL org.opencontainers.image.version="0.3.0"

# Install system dependencies
RUN dnf update -y && dnf install -y \
    git \
    gcc \
    g++ \
    make \
    cmake \
    curl \
    wget \
    just \
    ocaml \
    opam \
    coq \
    z3 \
    bash-completion \
    vim \
    && dnf clean all

# Install Lean 4 via elan
RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y --default-toolchain leanprover/lean4:stable
ENV PATH="/root/.elan/bin:${PATH}"

# Install Agda (if available in repos)
RUN dnf install -y agda || echo "Agda not available in dnf, skipping"

# Create workspace
WORKDIR /workspace/valence-shell

# Copy project files
COPY . .

# Verify proof directory structure
RUN ls -la proofs/

# Run verification on build (optional - comment out for faster builds)
# RUN ./scripts/verify-proofs.sh || echo "Some provers not available"

# Set up entrypoint
COPY <<'EOF' /entrypoint.sh
#!/bin/bash
echo "=================================================="
echo "Valence Shell - Verification Container"
echo "=================================================="
echo ""
echo "Available commands:"
echo "  just verify-all    - Verify all proofs"
echo "  just build-all     - Build all proofs"
echo "  just demo          - Run demonstration"
echo "  just ci            - Run CI pipeline"
echo ""
echo "Proof systems installed:"
command -v coqc && echo "  ✓ Coq $(coqc --version | head -1)"
command -v lean && echo "  ✓ Lean $(lean --version)"
command -v agda && echo "  ✓ Agda $(agda --version | head -1)" || echo "  ✗ Agda (not installed)"
command -v isabelle && echo "  ✓ Isabelle" || echo "  ✗ Isabelle (not installed)"
command -v z3 && echo "  ✓ Z3 $(z3 --version)"
echo ""
exec "$@"
EOF

RUN chmod +x /entrypoint.sh
ENTRYPOINT ["/entrypoint.sh"]
CMD ["/bin/bash"]

# Usage:
#   podman build -t valence-shell -f Containerfile .
#   podman run -it valence-shell
#   # Inside container:
#   just verify-all
