# SPDX-License-Identifier: MPL-2.0
# ClusterFuzzLite Docker build for Rust fuzzing

FROM gcr.io/oss-fuzz-base/base-builder-rust

# Install Rust nightly and its source tree, both required by cargo-fuzz's
# sanitizer builds.
RUN rustup default nightly && \
    rustup component add rust-src --toolchain nightly

# Copy project files
COPY . $SRC/valence-shell
WORKDIR $SRC/valence-shell

# Build script will be run by ClusterFuzzLite
COPY .clusterfuzzlite/build.sh $SRC/
