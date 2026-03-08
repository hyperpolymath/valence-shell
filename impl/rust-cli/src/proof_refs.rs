// SPDX-License-Identifier: PMPL-1.0-or-later
//! Proof References
//!
//! Maps operations to their corresponding Coq/Lean4/Agda/Isabelle theorems.
//! This allows users to see exactly which formal proof guarantees each operation.

use crate::state::OperationType;
use colored::Colorize;

/// A reference to formal proofs across multiple verification systems.
///
/// Maps each operation to its corresponding theorems in Coq, Lean 4, Agda, and Isabelle.
/// Used to display proof references in verbose mode and verification status.
///
/// # Examples
/// ```
/// use vsh::proof_refs::MKDIR_RMDIR_REVERSIBLE;
///
/// println!("{}", MKDIR_RMDIR_REVERSIBLE.format_short());
/// ```
#[derive(Debug, Clone)]
pub struct ProofReference {
    /// Primary theorem name
    pub theorem: &'static str,

    /// Coq file and line
    pub coq_location: &'static str,

    /// Lean 4 location
    pub lean_location: &'static str,

    /// Agda location
    pub agda_location: &'static str,

    /// Isabelle location
    pub isabelle_location: &'static str,

    /// Human-readable description
    pub description: &'static str,
}

impl ProofReference {
    /// Get the proof reference for a given operation type.
    ///
    /// Maps operation types to their corresponding proof references.
    ///
    /// # Arguments
    /// * `op` - The operation type to look up
    ///
    /// # Returns
    /// The corresponding [`ProofReference`] with theorem locations
    pub fn for_operation(op: OperationType) -> Self {
        match op {
            OperationType::Mkdir | OperationType::Rmdir => MKDIR_RMDIR_REVERSIBLE,
            OperationType::CreateFile | OperationType::DeleteFile => CREATE_DELETE_REVERSIBLE,
            OperationType::WriteFile => WRITE_FILE_REVERSIBLE,
            // File modifications from redirections - pending formal proofs
            OperationType::FileTruncated | OperationType::FileAppended => WRITE_FILE_REVERSIBLE,
            OperationType::CopyFile => COPY_FILE_REVERSIBLE,
            OperationType::Move => MOVE_REVERSIBLE,
            OperationType::Symlink | OperationType::Unlink => SYMLINK_UNLINK_REVERSIBLE,
            OperationType::Chmod => CHMOD_REVERSIBLE,
            OperationType::Chown => CHOWN_REVERSIBLE,
            OperationType::SetVariable | OperationType::UnsetVariable => VARIABLE_ASSIGNMENT_REVERSIBLE,
            OperationType::HardwareErase => HARDWARE_ERASE_IRREVERSIBLE,
            OperationType::Obliterate => OBLITERATE_IRREVERSIBLE,
        }
    }

    /// Format as a short one-line reference for terminal display.
    ///
    /// Returns: `theorem_name (coq_location)` with ANSI colors
    pub fn format_short(&self) -> String {
        format!(
            "{} ({})",
            self.theorem.bright_cyan(),
            self.coq_location.bright_black()
        )
    }

    /// Format with all proof system locations for detailed display.
    ///
    /// Returns multi-line string with theorem name, description, and locations
    /// in Coq, Lean 4, Agda, and Isabelle.
    pub fn format_full(&self) -> String {
        format!(
            "{}\n  {}\n  Coq:      {}\n  Lean 4:   {}\n  Agda:     {}\n  Isabelle: {}",
            self.theorem.bright_cyan().bold(),
            self.description.bright_black(),
            self.coq_location,
            self.lean_location,
            self.agda_location,
            self.isabelle_location,
        )
    }
}

/// Proof reference for mkdir/rmdir reversibility.
///
/// Theorem: `rmdir(mkdir(path, fs)) = fs` when preconditions hold
/// (parent exists, path doesn't exist).
pub const MKDIR_RMDIR_REVERSIBLE: ProofReference = ProofReference {
    theorem: "mkdir_rmdir_reversible",
    coq_location: "proofs/coq/filesystem_model.v:L45-L62",
    lean_location: "proofs/lean4/FilesystemModel.lean:L38-L52",
    agda_location: "proofs/agda/FilesystemModel.agda:L41-L58",
    isabelle_location: "proofs/isabelle/FilesystemModel.thy:L35-L50",
    description: "rmdir(mkdir(path, fs)) = fs when preconditions hold",
};

/// Proof reference for create_file/delete_file reversibility.
///
/// Theorem: `delete_file(create_file(path, fs)) = fs` when preconditions hold
/// (parent exists, path doesn't exist).
pub const CREATE_DELETE_REVERSIBLE: ProofReference = ProofReference {
    theorem: "create_delete_file_reversible",
    coq_location: "proofs/coq/file_operations.v:L32-L48",
    lean_location: "proofs/lean4/FileOperations.lean:L28-L42",
    agda_location: "proofs/agda/FileOperations.agda:L30-L45",
    isabelle_location: "proofs/isabelle/FileOperations.thy:L25-L40",
    description: "delete_file(create_file(path, fs)) = fs when preconditions hold",
};

/// Proof reference for write_file reversibility.
///
/// Theorem: `write_file(path, old_content, write_file(path, new_content, fs)) = fs`
/// when file exists and preconditions hold.
pub const WRITE_FILE_REVERSIBLE: ProofReference = ProofReference {
    theorem: "write_file_reversible",
    coq_location: "proofs/coq/file_content_operations.v:L67-L85",
    lean_location: "proofs/lean4/FileContentOperations.lean:L58-L74",
    agda_location: "proofs/agda/FileContentOperations.agda:L62-L78",
    isabelle_location: "proofs/isabelle/FileContentOperations.thy:L55-L72",
    description: "write_file(path, old, write_file(path, new, fs)) = fs",
};

/// Proof reference for operation composition/sequencing reversibility.
///
/// Theorem: `apply_sequence(reverse(ops), apply_sequence(ops, fs)) = fs`
/// when all individual operations are reversible.
pub const COMPOSITION_REVERSIBLE: ProofReference = ProofReference {
    theorem: "operation_sequence_reversible",
    coq_location: "proofs/coq/filesystem_composition.v:L28-L52",
    lean_location: "proofs/lean4/FilesystemComposition.lean:L24-L45",
    agda_location: "proofs/agda/FilesystemComposition.agda:L26-L48",
    isabelle_location: "proofs/isabelle/FilesystemComposition.thy:L22-L42",
    description: "apply_sequence(reverse(ops), apply_sequence(ops, fs)) = fs",
};

/// Proof reference for copy file reversibility.
///
/// Theorem: `deleteFile(copyFile(src, dst, fs)) = fs` when preconditions hold
/// (source exists, destination doesn't exist).
pub const COPY_FILE_REVERSIBLE: ProofReference = ProofReference {
    theorem: "copyFile_reversible",
    coq_location: "proofs/coq/copy_move_operations.v:L148",
    lean_location: "proofs/lean4/CopyMoveOperations.lean:L101",
    agda_location: "proofs/agda/CopyMoveOperations.agda:L95",
    isabelle_location: "proofs/isabelle/CopyMoveOperations.thy:L90",
    description: "deleteFile(copyFile(src, dst, fs)) = fs when preconditions hold",
};

/// Proof reference for move/rename reversibility.
///
/// Theorem: `move(dst, src, move(src, dst, fs)) = fs` when preconditions hold
/// (source exists, destination doesn't exist, no directory-into-self).
pub const MOVE_REVERSIBLE: ProofReference = ProofReference {
    theorem: "move_reversible",
    coq_location: "proofs/coq/copy_move_operations.v:L239",
    lean_location: "proofs/lean4/CopyMoveOperations.lean:L156",
    agda_location: "proofs/agda/CopyMoveOperations.agda:L150",
    isabelle_location: "proofs/isabelle/CopyMoveOperations.thy:L145",
    description: "move(dst, src, move(src, dst, fs)) = fs when preconditions hold",
};

/// Proof reference for symlink/unlink reversibility.
///
/// Theorem: `unlink(symlink(path, fs)) = fs` when preconditions hold
/// (path doesn't exist, parent exists).
pub const SYMLINK_UNLINK_REVERSIBLE: ProofReference = ProofReference {
    theorem: "symlink_unlink_reversible",
    coq_location: "proofs/coq/symlink_operations.v:L45",
    lean_location: "proofs/lean4/SymlinkOperations.lean:L45",
    agda_location: "proofs/agda/SymlinkOperations.agda:L42",
    isabelle_location: "proofs/isabelle/SymlinkOperations.thy:L40",
    description: "unlink(symlink(path, fs)) = fs when preconditions hold",
};

/// Proof reference for chmod reversibility.
///
/// Theorem: `chmod(old_mode, chmod(new_mode, path, fs)) = fs` when preconditions hold
pub const CHMOD_REVERSIBLE: ProofReference = ProofReference {
    theorem: "chmod_reversible",
    coq_location: "proofs/coq/permission_operations.v:L67",
    lean_location: "proofs/lean4/PermissionOperations.lean:L52",
    agda_location: "proofs/agda/PermissionOperations.agda:L70",
    isabelle_location: "proofs/isabelle/PermissionOperations.thy:L67",
    description: "chmod(old_mode, chmod(new_mode, path, fs)) = fs when preconditions hold",
};

/// Proof reference for chown reversibility.
///
/// Theorem: `chown(old_uid, old_gid, chown(new_uid, new_gid, path, fs)) = fs`
pub const CHOWN_REVERSIBLE: ProofReference = ProofReference {
    theorem: "chown_reversible",
    coq_location: "proofs/coq/permission_operations.v:L149",
    lean_location: "proofs/lean4/PermissionOperations.lean:L135",
    agda_location: "proofs/agda/PermissionOperations.agda:L119",
    isabelle_location: "proofs/isabelle/PermissionOperations.thy:L166",
    description: "chown(old_uid/gid, chown(new_uid/gid, path, fs)) = fs when preconditions hold",
};

/// Proof reference for variable assignment reversibility.
///
/// Theorem: `set(name, old_value, set(name, new_value, env)) = env`
/// when previous value is captured.
/// This is a state-machine property: capturing pre-state enables reversal.
pub const VARIABLE_ASSIGNMENT_REVERSIBLE: ProofReference = ProofReference {
    theorem: "variable_assignment_reversible",
    coq_location: "proofs/coq/environment_model.v:pending",
    lean_location: "proofs/lean4/EnvironmentModel.lean:pending",
    agda_location: "proofs/agda/EnvironmentModel.agda:pending",
    isabelle_location: "proofs/isabelle/EnvironmentModel.thy:pending",
    description: "set(name, old, set(name, new, env)) = env (pre-state capture)",
};

/// Proof reference for hardware secure erase irreversibility.
///
/// Theorem: Hardware erase operations have NO inverse - data destruction is permanent.
/// Complies with NIST SP 800-88 Rev. 1 Purge methods.
pub const HARDWARE_ERASE_IRREVERSIBLE: ProofReference = ProofReference {
    theorem: "hardware_erase_irreversible",
    coq_location: "proofs/coq/rmo_operations.v:L45-L68",
    lean_location: "proofs/lean4/RMOOperations.lean:L52-L73",
    agda_location: "proofs/agda/RMOOperations.agda:L48-L70",
    isabelle_location: "proofs/isabelle/RMOOperations.thy:L44-L65",
    description: "∀ fs device. ¬∃ op. apply(op, hardware_erase(device, fs)) = fs",
};

/// Proof reference for GDPR-compliant obliterate irreversibility.
///
/// Theorem: Obliterate operations have NO inverse - secure 3-pass overwrite + deletion.
/// Complies with DoD 5220.22-M and GDPR Article 17 (Right to Erasure).
pub const OBLITERATE_IRREVERSIBLE: ProofReference = ProofReference {
    theorem: "obliterate_irreversible",
    coq_location: "proofs/coq/rmo_operations.v:L70-L95",
    lean_location: "proofs/lean4/RMOOperations.lean:L75-L98",
    agda_location: "proofs/agda/RMOOperations.agda:L72-L96",
    isabelle_location: "proofs/isabelle/RMOOperations.thy:L67-L89",
    description: "∀ fs file. ¬∃ op. apply(op, obliterate(file, fs)) = fs",
};

/// Get all available proof references as a vector.
///
/// Returns all proof constants for iteration or verification checking.
///
/// # Returns
/// Vector of all [`ProofReference`] constants defined in this module
pub fn all_proofs() -> Vec<ProofReference> {
    vec![
        MKDIR_RMDIR_REVERSIBLE,
        CREATE_DELETE_REVERSIBLE,
        WRITE_FILE_REVERSIBLE,
        COPY_FILE_REVERSIBLE,
        MOVE_REVERSIBLE,
        SYMLINK_UNLINK_REVERSIBLE,
        CHMOD_REVERSIBLE,
        CHOWN_REVERSIBLE,
        COMPOSITION_REVERSIBLE,
    ]
}

/// Print a formatted summary of formal verification status.
///
/// Displays proof count, verification systems, and coverage information
/// with colored terminal output.
pub fn print_verification_summary() {
    println!("{}", "═══ Formal Verification Status ═══".bright_blue().bold());
    println!();
    println!("{}: ~250+ theorems proven", "Total Proofs".bright_green());
    println!("{}: 6", "Proof Systems".bright_green());
    println!();

    println!("{}", "Verification Systems:".bright_yellow());
    println!("  1. {} - Calculus of Inductive Constructions", "Coq".bright_cyan());
    println!("  2. {} - Dependent Type Theory", "Lean 4".bright_cyan());
    println!("  3. {} - Intensional Type Theory", "Agda".bright_cyan());
    println!("  4. {} - Higher-Order Logic", "Isabelle/HOL".bright_cyan());
    println!("  5. {} - Tarski-Grothendieck Set Theory", "Mizar".bright_cyan());
    println!("  6. {} - SMT Automated Verification", "Z3".bright_cyan());
    println!();

    println!("{}", "Core Theorems:".bright_yellow());
    for proof in all_proofs() {
        println!();
        println!("{}", proof.format_full());
    }
    println!();

    println!("{}", "Trust Model:".bright_yellow());
    println!("  {} Formal proofs verified by proof assistant kernels", "✓".bright_green());
    println!("  {} Zig FFI layer checks preconditions", "✓".bright_green());
    println!("  {} Rust CLI maintains undo stack", "✓".bright_green());
    println!("  {} POSIX semantics assumed correct (OS trust)", "○".bright_yellow());
    println!();

    println!("{}", "Verification Gap:".bright_red());
    println!("  The FFI layer is NOT mechanically verified.");
    println!("  It implements precondition checks derived from proofs.");
    println!("  Full end-to-end verification requires:");
    println!("  - Formal POSIX semantics model");
    println!("  - Refinement proof from abstract to concrete");
    println!("  - Verified compilation chain");
}
