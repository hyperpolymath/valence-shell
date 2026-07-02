#!/bin/bash
# SPDX-License-Identifier: MPL-2.0
# ClusterFuzzLite build script for Rust fuzz targets

set -euo pipefail

cd "$SRC"/valence-shell/impl/rust-cli

# The OSS-Fuzz base-builder-rust image already ships cargo-fuzz. Reinstalling it
# with `cargo install --force` rebuilds cargo-fuzz and its dependencies —
# including the proc-macro crate `thiserror_impl` — under the image's sanitizer
# RUSTFLAGS, which breaks the host build with:
#   error[E0463]: can't find crate for `thiserror_impl`
# So prefer the pre-installed cargo-fuzz, and only fall back to a clean install
# (RUSTFLAGS cleared) if it is genuinely missing.
if ! command -v cargo-fuzz >/dev/null 2>&1; then
    RUSTFLAGS="" cargo install cargo-fuzz --locked
fi

# Build all fuzz targets. cargo-fuzz only supports the address sanitizer for
# Rust; honour $SANITIZER when set (OSS-Fuzz exports it) but default to address.
cargo +nightly fuzz build --sanitizer "${SANITIZER:-address}"

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
