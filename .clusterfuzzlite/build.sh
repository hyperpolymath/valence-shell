#!/bin/bash
# SPDX-License-Identifier: PLMP-1.0-or-later
# ClusterFuzzLite build script for Rust fuzz targets

set -euo pipefail

cd "$SRC"/valence-shell/impl/rust-cli

# Install cargo-fuzz if not present
cargo install cargo-fuzz --force

# Build all fuzz targets
cargo +nightly fuzz build

# Copy fuzz targets to $OUT
for target in fuzz/target/*/release/fuzz_*; do
    if [ -f "$target" ]; then
        cp "$target" $OUT/
    fi
done

# Copy corpus (if exists)
if [ -d "fuzz/corpus" ]; then
    for corpus_dir in fuzz/corpus/*; do
        if [ -d "$corpus_dir" ]; then
            target_name=$(basename "$corpus_dir")
            mkdir -p $OUT/${target_name}_seed_corpus
            cp -r $corpus_dir/* $OUT/${target_name}_seed_corpus/
        fi
    done
fi

echo "Built fuzz targets:"
ls -lh $OUT/fuzz_*
