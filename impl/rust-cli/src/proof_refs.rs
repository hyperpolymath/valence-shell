// SPDX-License-Identifier: MPL-2.0
// Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//! Proof References
//!
//! Maps operations to their corresponding Coq/Lean4/Agda/Isabelle theorems.
//! This allows users to see exactly which formal proof guarantees each operation.

use crate::state::OperationType;
use colored::Colorize;

/// What the theorem shown for an operation claims about it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Claim {
    /// The operation can be reversed, and the theorem is about it.
    Reversal,
    /// The operation can be reversed. The theorem shown is about a write of
    /// a whole file: none is stated for a redirection, which is reported
    /// under it.
    ReversalOfAWrite,
    /// The operation can be reversed: the shell does it from its own
    /// record. No proof file states a theorem about it.
    ReversalNotStated,
    /// The operation cannot be reversed, and the theorem says that it is
    /// not injective in the model.
    Irreversible,
    /// The operation cannot be reversed. No proof file states a theorem
    /// about it.
    IrreversibleNotStated,
}

/// Shown in place of a theorem name where no proof file states one.
pub const NO_THEOREM: &str = "none stated";

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
    /// What the theorem that [`Self::for_operation`] gives claims about an
    /// operation of type `op`. See [`Claim`].
    pub fn claim_for(op: OperationType) -> Claim {
        let stated = Self::for_operation(op).is_stated();
        match (op.inverse().is_some(), stated) {
            (true, true) => match op {
                OperationType::FileTruncated | OperationType::FileAppended => {
                    Claim::ReversalOfAWrite
                }
                _ => Claim::Reversal,
            },
            (true, false) => Claim::ReversalNotStated,
            (false, true) => Claim::Irreversible,
            (false, false) => Claim::IrreversibleNotStated,
        }
    }

    /// Whether a proof file states a theorem for this entry. An entry for
    /// which none does has [`NO_THEOREM`] in place of a name.
    pub fn is_stated(&self) -> bool {
        self.theorem != NO_THEOREM
    }

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
            OperationType::SetVariable | OperationType::UnsetVariable => VARIABLE_CHANGE_NO_THEOREM,
            OperationType::HardwareErase => HARDWARE_ERASE_IRREVERSIBLE,
            OperationType::Obliterate => OBLITERATE_IRREVERSIBLE,
        }
    }

    /// Format as a short one-line reference for terminal display.
    ///
    /// Returns: `theorem_name (coq_location)` with ANSI colors, or
    /// [`NO_THEOREM`] alone for an entry that has no theorem.
    pub fn format_short(&self) -> String {
        if !self.is_stated() {
            return self.theorem.bright_cyan().to_string();
        }
        format!(
            "{} ({})",
            self.theorem.bright_cyan(),
            self.coq_location.bright_black()
        )
    }

    /// Format with all proof system locations for detailed display.
    ///
    /// Returns multi-line string with theorem name, description, and locations
    /// in Coq, Lean 4, Agda, and Isabelle, marking Isabelle as archived and unchecked.
    pub fn format_full(&self) -> String {
        format!(
            "{}\n  {}\n  Coq:      {}\n  Lean 4:   {}\n  Agda:     {}\n  Isabelle: {} (archived, unchecked)",
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
    isabelle_location: "archive/proofs/isabelle/FilesystemModel.thy:L35-L50",
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
    isabelle_location: "archive/proofs/isabelle/FileOperations.thy:L25-L40",
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
    isabelle_location: "archive/proofs/isabelle/FileContentOperations.thy:L55-L72",
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
    isabelle_location: "archive/proofs/isabelle/FilesystemComposition.thy:L22-L42",
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
    isabelle_location: "archive/proofs/isabelle/CopyMoveOperations.thy:L90",
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
    isabelle_location: "archive/proofs/isabelle/CopyMoveOperations.thy:L145",
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
    isabelle_location: "archive/proofs/isabelle/SymlinkOperations.thy:L40",
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
    isabelle_location: "archive/proofs/isabelle/PermissionOperations.thy:L67",
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
    isabelle_location: "archive/proofs/isabelle/PermissionOperations.thy:L166",
    description: "chown(old_uid/gid, chown(new_uid/gid, path, fs)) = fs when preconditions hold",
};

/// Entry for a change to a shell variable.
///
/// No proof file states a theorem about it. The entry used to name
/// `variable_assignment_reversible` and three files that do not exist. The
/// shell reverses the change from its own record of the earlier value.
pub const VARIABLE_CHANGE_NO_THEOREM: ProofReference = ProofReference {
    theorem: NO_THEOREM,
    coq_location: "none",
    lean_location: "none",
    agda_location: "none",
    isabelle_location: "none (no Isabelle theory was written before the archive)",
    description: "no proof file states a theorem about a change to a variable; \
                  the shell restores the earlier value from its own record",
};

/// Proof reference for a hardware erase.
///
/// The theorem is stated in the Idris2 layer only, where a hardware erase
/// is a function that gives the empty filesystem from every start. It says
/// that any two starts give the same result, so the erase is not injective
/// and nothing can recover the start. Coq, Lean and Agda state nothing
/// about a hardware erase. The theorem is about that model: it does not
/// prove that a device was erased, nor compliance with NIST SP 800-88.
pub const HARDWARE_ERASE_IRREVERSIBLE: ProofReference = ProofReference {
    theorem: "hardwareEraseIrreversible",
    coq_location: "none (Idris2 only: proofs/idris2/src/Filesystem/RMO.idr:L238)",
    lean_location: "none (Idris2 only: proofs/idris2/src/Filesystem/RMO.idr:L238)",
    agda_location: "none (Idris2 only: proofs/idris2/src/Filesystem/RMO.idr:L238)",
    isabelle_location: "none (the archived RMO_Operations.thy has no hardware-erase theorem)",
    description: "∀ fs1 fs2. hardware_erase(fs1) = hardware_erase(fs2): the erase is not injective",
};

/// Proof reference for an obliteration.
///
/// The theorem is about the model: two stores that differ only in the data
/// of the blocks of the file give the same result once the file is
/// obliterated with at least one overwrite pattern. The operation is
/// therefore not injective, and nothing can recover the start. It does not
/// prove physical-media erasure, correspondence with the Rust I/O sequence,
/// or compliance with a legal regime. Agda states no such theorem.
pub const OBLITERATE_IRREVERSIBLE: ProofReference = ProofReference {
    theorem: "obliterate_not_injective",
    coq_location: "proofs/coq/rmo_operations.v:L530",
    lean_location: "proofs/lean4/RMOOperations.lean:L301",
    agda_location: "none (RMOOperations.agda states no theorem of non-injectivity)",
    isabelle_location: "archive/proofs/isabelle/RMO_Operations.thy:L158",
    description: "stores that differ only in the block data of the file give the same \
                  result: obliterate is not injective",
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
/// Displays the proof ledger reference, verification systems, core theorem
/// references, and trust limitations with coloured terminal output.
pub fn print_verification_summary() {
    println!(
        "{}",
        "═══ Formal Verification Status ═══".bright_blue().bold()
    );
    println!();
    println!(
        "{}: per obligation in EXPLAINME.adoc#proof-ledger (no total is claimed)",
        "Proof status".bright_green()
    );
    println!(
        "{}: Agda (theory source); Lean 4 and Coq (recheck legs); Z3 (supplementary)",
        "Checked systems".bright_green()
    );
    println!();

    println!("{}", "Verification Systems:".bright_yellow());
    println!(
        "  1. {} - Calculus of Inductive Constructions",
        "Coq".bright_cyan()
    );
    println!("  2. {} - Dependent Type Theory", "Lean 4".bright_cyan());
    println!("  3. {} - Intensional Type Theory", "Agda".bright_cyan());
    println!(
        "  4. {} - Higher-Order Logic (archived 2026-11-09, unchecked)",
        "Isabelle/HOL".bright_cyan()
    );
    println!(
        "  5. {} - Tarski-Grothendieck Set Theory (archived 2026-11-09, unchecked)",
        "Mizar".bright_cyan()
    );
    println!("  6. {} - SMT Automated Verification", "Z3".bright_cyan());
    println!();

    println!("{}", "Core Theorems:".bright_yellow());
    for proof in all_proofs() {
        println!();
        println!("{}", proof.format_full());
    }
    println!();

    println!("{}", "Trust Model:".bright_yellow());
    println!(
        "  {} Theorems about the model are checked by proof assistants",
        "✓".bright_green()
    );
    println!(
        "  {} The link from the model to this Rust code is tested, not proved",
        "○".bright_yellow()
    );
    println!(
        "  {} The Zig FFI layer is not connected to this shell",
        "○".bright_yellow()
    );
    println!(
        "  {} The shell keeps the operation history that undo uses",
        "✓".bright_green()
    );
    println!(
        "  {} POSIX semantics assumed correct (OS trust)",
        "○".bright_yellow()
    );
    println!();

    println!("{}", "Verification Gap:".bright_red());
    println!("  No proof connects the model to the code that runs.");
    println!("  Closing that gap requires:");
    println!("  - Formal POSIX semantics model");
    println!("  - Refinement proof from abstract to concrete");
    println!("  - Verified compilation chain");
}

#[cfg(test)]
mod tests {
    use super::*;

    /// An operation is said to be irreversible exactly when it has no
    /// inverse, so the two tables cannot drift apart.
    #[test]
    fn test_a_claim_of_irreversibility_matches_the_inverse_table() {
        let all = [
            OperationType::Mkdir,
            OperationType::Rmdir,
            OperationType::CreateFile,
            OperationType::DeleteFile,
            OperationType::WriteFile,
            OperationType::FileTruncated,
            OperationType::FileAppended,
            OperationType::CopyFile,
            OperationType::Move,
            OperationType::Symlink,
            OperationType::Unlink,
            OperationType::SetVariable,
            OperationType::UnsetVariable,
            OperationType::Chmod,
            OperationType::Chown,
            OperationType::HardwareErase,
            OperationType::Obliterate,
        ];
        for op in all {
            let claim = ProofReference::claim_for(op);
            assert_eq!(
                matches!(claim, Claim::Irreversible | Claim::IrreversibleNotStated),
                op.inverse().is_none(),
                "{op:?}"
            );
            assert_eq!(
                matches!(
                    claim,
                    Claim::ReversalNotStated | Claim::IrreversibleNotStated
                ),
                !ProofReference::for_operation(op).is_stated(),
                "{op:?}"
            );
        }
    }

    /// What a replay may claim for each kind of operation. A change to a
    /// variable was shown under a reversal theorem that no proof file
    /// states.
    #[test]
    fn test_the_claim_for_each_kind_of_operation() {
        let claim = ProofReference::claim_for;
        assert_eq!(claim(OperationType::Mkdir), Claim::Reversal);
        assert_eq!(claim(OperationType::Move), Claim::Reversal);
        assert_eq!(claim(OperationType::FileTruncated), Claim::ReversalOfAWrite);
        assert_eq!(claim(OperationType::FileAppended), Claim::ReversalOfAWrite);
        assert_eq!(claim(OperationType::SetVariable), Claim::ReversalNotStated);
        assert_eq!(
            claim(OperationType::UnsetVariable),
            Claim::ReversalNotStated
        );
        assert_eq!(claim(OperationType::Obliterate), Claim::Irreversible);
        assert_eq!(claim(OperationType::HardwareErase), Claim::Irreversible);
    }

    /// An entry with no theorem shows that, and no location beside it.
    #[test]
    fn test_an_entry_with_no_theorem_shows_no_location() {
        let short = VARIABLE_CHANGE_NO_THEOREM.format_short();
        assert!(short.contains(NO_THEOREM), "{short}");
        assert!(!short.contains('('), "{short}");

        let stated = OBLITERATE_IRREVERSIBLE.format_short();
        assert!(stated.contains("obliterate_not_injective"), "{stated}");
        assert!(
            stated.contains("proofs/coq/rmo_operations.v:L530"),
            "{stated}"
        );
    }

    /// The path of the proof file that a location names, if it names one.
    fn named_file(location: &str) -> Option<&str> {
        let rest = &location[location.find("proofs/")?..];
        let end = rest.find([':', ')', ' ']).unwrap_or(rest.len());
        Some(&rest[..end])
    }

    /// Whether `text` declares something called `theorem`: after `Theorem`,
    /// `Lemma`, `theorem` or `lemma` (Coq and Lean), or at the start of a
    /// line before a colon (Idris2, and Agda with hyphens for underscores).
    fn declares(text: &str, theorem: &str) -> bool {
        let hyphenated = theorem.replace('_', "-");
        text.lines().any(|line| {
            let mut words = line.split_whitespace();
            match (words.next(), words.next()) {
                (Some("Theorem" | "Lemma" | "theorem" | "lemma"), Some(name)) => {
                    name.trim_end_matches(':') == theorem
                }
                (Some(name), Some(":")) => name == theorem || name == hyphenated,
                _ => false,
            }
        })
    }

    /// Every theorem name the shell shows is declared in a proof file that
    /// its entry names, and an entry with no theorem names no file. Three
    /// entries failed this: the names shown for a change to a variable, for
    /// a hardware erase and for an obliteration were declared in no file.
    ///
    /// The check is of names against files. It does not check the line
    /// numbers in the entries, nor that each of Coq, Lean and Agda uses the
    /// name shown.
    #[test]
    fn test_a_shown_theorem_is_declared_in_a_file_its_entry_names() {
        let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
        let mut entries = all_proofs();
        entries.extend([
            VARIABLE_CHANGE_NO_THEOREM,
            HARDWARE_ERASE_IRREVERSIBLE,
            OBLITERATE_IRREVERSIBLE,
        ]);
        assert_eq!(entries.len(), 12);
        for entry in entries {
            let files: Vec<&str> = [entry.coq_location, entry.lean_location, entry.agda_location]
                .into_iter()
                .filter_map(named_file)
                .collect();
            let declared = files.iter().any(|file| {
                let text = std::fs::read_to_string(root.join(file))
                    .unwrap_or_else(|e| panic!("{file} cannot be read: {e}"));
                declares(&text, entry.theorem)
            });
            assert_eq!(
                entry.is_stated(),
                declared,
                "{} in {files:?}",
                entry.theorem
            );
            if !entry.is_stated() {
                assert!(files.is_empty(), "{files:?}");
            }
        }
    }
}
