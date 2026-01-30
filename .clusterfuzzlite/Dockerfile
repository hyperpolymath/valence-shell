# SPDX-License-Identifier: PLMP-1.0-or-later
# ClusterFuzzLite Docker build for Rust fuzzing

FROM gcr.io/oss-fuzz-base/base-builder-rust

# Install Rust nightly (required for cargo-fuzz)
RUN rustup default nightly

# Copy project files
COPY . $SRC/valence-shell
WORKDIR $SRC/valence-shell

# Build script will be run by ClusterFuzzLite
COPY .clusterfuzzlite/build.sh $SRC/
