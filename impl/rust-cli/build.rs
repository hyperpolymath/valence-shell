// SPDX-License-Identifier: PLMP-1.0-or-later
//! Build script for Valence Shell
//!
//! Handles linking to external libraries:
//! - Lean 4 runtime via Zig wrapper (when lean-runtime-checks feature enabled)

use std::path::PathBuf;

fn main() {
    // Link to Lean runtime library if feature enabled
    // Note: In build.rs, features are available as environment variables
    if std::env::var("CARGO_FEATURE_LEAN_RUNTIME_CHECKS").is_ok() {
        println!("cargo:rerun-if-changed=../../impl/zig/zig-out/lib/liblean_vsh.so");

        // Get Lean installation path
        let lean_prefix = std::process::Command::new("lean")
            .arg("--print-prefix")
            .output()
            .expect("Failed to run 'lean --print-prefix' - is Lean 4 installed?")
            .stdout;

        let lean_prefix = String::from_utf8(lean_prefix)
            .expect("Invalid UTF-8 from lean")
            .trim()
            .to_string();

        let lean_lib = PathBuf::from(&lean_prefix).join("lib/lean");

        // Link our Zig wrapper library (must come before leanshared)
        let manifest_dir = PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").unwrap());
        let wrapper_lib = manifest_dir.parent().unwrap().join("zig/zig-out/lib");
        let wrapper_lib_abs = wrapper_lib.canonicalize()
            .unwrap_or_else(|_| wrapper_lib.clone());

        println!("cargo:warning=Wrapper lib path: {}", wrapper_lib_abs.display());
        let lib_full_path = wrapper_lib_abs.join("liblean_vsh.so");
        println!("cargo:rustc-link-arg={}", lib_full_path.display());
        println!("cargo:rustc-link-arg=-Wl,-rpath,{}", wrapper_lib_abs.display());

        // Link Lean runtime
        println!("cargo:rustc-link-search=native={}", lean_lib.display());
        println!("cargo:rustc-link-lib=dylib=leanshared");
        println!("cargo:rustc-link-arg=-Wl,-rpath,{}", lean_lib.display());

        println!("cargo:warning=Lean runtime checks ENABLED - preconditions will be verified");
    } else {
        println!("cargo:warning=Lean runtime checks DISABLED - no formal verification at runtime");
    }
}
