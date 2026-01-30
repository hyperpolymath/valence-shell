// SPDX-License-Identifier: PLMP-1.0-or-later
//! 3-Tier Help System
//!
//! Provides comprehensive help at three levels:
//! - Tier 1: Quick reference (`help cmd` - one-liners)
//! - Tier 2: Detailed help (`help -v cmd` - full documentation)
//! - Tier 3: Man pages (`man vsh-cmd` - comprehensive reference)
//!
//! Fish-style: Shows examples, related commands, and proof references.

use anyhow::{bail, Result};
use colored::Colorize;

use crate::pager;
use crate::proof_refs;
use crate::state::OperationType;

/// Help tier level
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HelpTier {
    /// Quick one-liner
    Quick,
    /// Detailed multi-line with examples
    Verbose,
    /// Full man page
    ManPage,
}

/// Help entry for a command
#[derive(Debug, Clone)]
pub struct HelpEntry {
    /// Command name
    pub name: &'static str,

    /// One-line summary
    pub summary: &'static str,

    /// Usage pattern
    pub usage: &'static str,

    /// Full description
    pub description: &'static str,

    /// Examples
    pub examples: &'static [Example],

    /// Related commands
    pub related: &'static [&'static str],

    /// Proof reference (if reversible operation)
    pub proof_operation: Option<OperationType>,
}

/// Example command usage
#[derive(Debug, Clone)]
pub struct Example {
    /// Description of what the example does
    pub description: &'static str,

    /// The command to run
    pub command: &'static str,
}

impl HelpEntry {
    /// Display help at specified tier
    pub fn display(&self, tier: HelpTier) -> Result<()> {
        match tier {
            HelpTier::Quick => self.display_quick(),
            HelpTier::Verbose => self.display_verbose(),
            HelpTier::ManPage => self.display_manpage(),
        }
    }

    /// Tier 1: Quick one-liner
    fn display_quick(&self) -> Result<()> {
        println!(
            "{} - {}",
            self.name.bright_green().bold(),
            self.summary
        );
        println!("Usage: {}", self.usage.bright_cyan());
        println!("Run {} for details", format!("help -v {}", self.name).bright_yellow());
        Ok(())
    }

    /// Tier 2: Verbose with examples
    fn display_verbose(&self) -> Result<()> {
        let mut output = String::new();

        // Header
        output.push_str(&format!("{}\n", format!("=== {} ===", self.name.to_uppercase()).bright_blue().bold()));
        output.push('\n');

        // Summary
        output.push_str(&format!("{}\n", self.summary));
        output.push('\n');

        // Usage
        output.push_str(&format!("{}\n", "USAGE:".bright_yellow().bold()));
        output.push_str(&format!("  {}\n", self.usage.bright_cyan()));
        output.push('\n');

        // Description
        output.push_str(&format!("{}\n", "DESCRIPTION:".bright_yellow().bold()));
        for line in self.description.lines() {
            output.push_str(&format!("  {}\n", line));
        }
        output.push('\n');

        // Examples
        if !self.examples.is_empty() {
            output.push_str(&format!("{}\n", "EXAMPLES:".bright_yellow().bold()));
            for (i, example) in self.examples.iter().enumerate() {
                output.push_str(&format!("  {}. {}\n", i + 1, example.description));
                output.push_str(&format!("     {}\n", format!("$ {}", example.command).bright_cyan()));
                output.push('\n');
            }
        }

        // Related commands
        if !self.related.is_empty() {
            output.push_str(&format!("{}\n", "SEE ALSO:".bright_yellow().bold()));
            output.push_str(&format!("  {}\n", self.related.join(", ")));
            output.push('\n');
        }

        // Proof reference
        if let Some(op_type) = self.proof_operation {
            output.push_str(&format!("{}\n", "FORMAL VERIFICATION:".bright_yellow().bold()));
            let proof_ref = proof_refs::ProofReference::for_operation(op_type);
            output.push_str(&format!("  {}\n", proof_ref.format_short()));
            output.push_str(&format!("  Run {} for proof details\n", "proof".bright_cyan()));
            output.push('\n');
        }

        // Footer
        output.push_str(&format!("Run {} for comprehensive documentation\n",
            format!("man vsh-{}", self.name).bright_yellow()));

        // Page if output is long
        pager::page(&output)?;
        Ok(())
    }

    /// Tier 3: Full man page (formatted)
    fn display_manpage(&self) -> Result<()> {
        let mut output = String::new();

        // Man page header
        output.push_str(&format!("VSH-{}(1)          Valence Shell Manual          VSH-{}(1)\n\n", self.name.to_uppercase(), self.name.to_uppercase()));

        // NAME
        output.push_str("NAME\n");
        output.push_str(&format!("       {} - {}\n\n", self.name, self.summary));

        // SYNOPSIS
        output.push_str("SYNOPSIS\n");
        output.push_str(&format!("       {}\n\n", self.usage));

        // DESCRIPTION
        output.push_str("DESCRIPTION\n");
        for line in self.description.lines() {
            output.push_str(&format!("       {}\n", line));
        }
        output.push('\n');

        // EXAMPLES
        if !self.examples.is_empty() {
            output.push_str("EXAMPLES\n");
            for example in self.examples.iter() {
                output.push_str(&format!("       {}\n", example.description));
                output.push_str(&format!("              $ {}\n\n", example.command));
            }
        }

        // FORMAL VERIFICATION
        if let Some(op_type) = self.proof_operation {
            output.push_str("FORMAL VERIFICATION\n");
            let proof_ref = proof_refs::ProofReference::for_operation(op_type);
            output.push_str(&format!("       This operation is formally verified for correctness.\n\n"));
            output.push_str(&format!("       Theorem: {}\n", proof_ref.theorem));
            output.push_str(&format!("       Description: {}\n\n", proof_ref.description));
            output.push_str(&format!("       Proof locations:\n"));
            output.push_str(&format!("         Coq:      {}\n", proof_ref.coq_location));
            output.push_str(&format!("         Lean 4:   {}\n", proof_ref.lean_location));
            output.push_str(&format!("         Agda:     {}\n", proof_ref.agda_location));
            output.push_str(&format!("         Isabelle: {}\n\n", proof_ref.isabelle_location));
        }

        // SEE ALSO
        if !self.related.is_empty() {
            output.push_str("SEE ALSO\n");
            output.push_str(&format!("       {}\n\n",
                self.related.iter().map(|cmd| format!("vsh-{}(1)", cmd)).collect::<Vec<_>>().join(", ")));
        }

        // Footer
        output.push_str(&format!("Valence Shell 0.14.0                {}               VSH-{}(1)\n",
            chrono::Utc::now().format("%Y-%m-%d"),
            self.name.to_uppercase()));

        // Page the output
        pager::page(&output)?;
        Ok(())
    }
}

/// Get help entry for a command
pub fn get_help(command: &str) -> Option<&'static HelpEntry> {
    HELP_DATABASE.iter().find(|entry| entry.name == command)
}

/// Display help for a command
///
/// # Arguments
/// * `command` - Command to show help for (None = list all commands)
/// * `tier` - Help detail level
pub fn display_help(command: Option<&str>, tier: HelpTier) -> Result<()> {
    match command {
        Some(cmd) => {
            if let Some(entry) = get_help(cmd) {
                entry.display(tier)?;
            } else {
                bail!("No help available for '{}'. Run 'help' to see all commands.", cmd);
            }
        }
        None => {
            // List all commands
            display_command_list()?;
        }
    }
    Ok(())
}

/// Display list of all available commands
fn display_command_list() -> Result<()> {
    println!("{}", "Available commands:".bright_blue().bold());
    println!();

    // Group by category
    let categories = vec![
        ("Navigation", vec!["cd", "pwd"]),
        ("File Operations", vec!["mkdir", "rmdir", "touch", "rm"]),
        ("History & Undo", vec!["undo", "redo", "history"]),
        ("Transactions", vec!["begin", "commit", "rollback"]),
        ("Utilities", vec!["help", "exit"]),
    ];

    for (category, commands) in categories {
        println!("{}", category.bright_yellow());
        for cmd in commands {
            if let Some(entry) = get_help(cmd) {
                println!("  {} - {}", cmd.bright_green(), entry.summary);
            }
        }
        println!();
    }

    println!("Run {} for command details", "help <command>".bright_cyan());
    println!("Run {} for detailed help with examples", "help -v <command>".bright_cyan());
    println!("Run {} for full manual page", "man vsh-<command>".bright_cyan());

    Ok(())
}

/// Help database (static)
static HELP_DATABASE: &[HelpEntry] = &[
    // mkdir
    HelpEntry {
        name: "mkdir",
        summary: "Create a directory",
        usage: "mkdir <path>",
        description: "Creates a new directory at the specified path.\n\
                      This operation is reversible via 'undo'.",
        examples: &[
            Example {
                description: "Create a directory",
                command: "mkdir project",
            },
            Example {
                description: "Undo directory creation",
                command: "mkdir test && undo",
            },
        ],
        related: &["rmdir", "undo", "touch"],
        proof_operation: Some(OperationType::Mkdir),
    },

    // rmdir
    HelpEntry {
        name: "rmdir",
        summary: "Remove an empty directory",
        usage: "rmdir <path>",
        description: "Removes an empty directory at the specified path.\n\
                      Directory must be empty (use 'rm -r' for non-empty directories).\n\
                      This operation is reversible via 'undo'.",
        examples: &[
            Example {
                description: "Remove empty directory",
                command: "rmdir old_project",
            },
            Example {
                description: "Create and remove directory",
                command: "mkdir temp && rmdir temp",
            },
        ],
        related: &["mkdir", "undo", "rm"],
        proof_operation: Some(OperationType::Rmdir),
    },

    // touch
    HelpEntry {
        name: "touch",
        summary: "Create an empty file",
        usage: "touch <path>",
        description: "Creates a new empty file at the specified path.\n\
                      This operation is reversible via 'undo'.",
        examples: &[
            Example {
                description: "Create empty file",
                command: "touch README.md",
            },
            Example {
                description: "Create multiple files",
                command: "touch file1.txt && touch file2.txt",
            },
        ],
        related: &["rm", "mkdir", "undo"],
        proof_operation: Some(OperationType::CreateFile),
    },

    // rm
    HelpEntry {
        name: "rm",
        summary: "Remove a file",
        usage: "rm <path>",
        description: "Removes a file at the specified path.\n\
                      File contents are preserved in undo history for restoration.\n\
                      This operation is reversible via 'undo'.\n\n\
                      For GDPR-compliant secure deletion, use 'obliterate'.",
        examples: &[
            Example {
                description: "Remove file",
                command: "rm old_file.txt",
            },
            Example {
                description: "Remove and restore file",
                command: "rm file.txt && undo",
            },
        ],
        related: &["touch", "rmdir", "undo", "obliterate"],
        proof_operation: Some(OperationType::DeleteFile),
    },

    // undo
    HelpEntry {
        name: "undo",
        summary: "Undo the last operation(s)",
        usage: "undo [count]",
        description: "Reverses the last N operations (default: 1).\n\
                      Operations are undone in reverse order.\n\
                      Each undo is itself recorded and can be undone with 'redo'.",
        examples: &[
            Example {
                description: "Undo last operation",
                command: "mkdir test && undo",
            },
            Example {
                description: "Undo last 3 operations",
                command: "undo 3",
            },
        ],
        related: &["redo", "history"],
        proof_operation: None,
    },

    // redo
    HelpEntry {
        name: "redo",
        summary: "Redo previously undone operation(s)",
        usage: "redo [count]",
        description: "Re-applies the last N undone operations (default: 1).\n\
                      Only works if operations were undone and not yet overwritten.",
        examples: &[
            Example {
                description: "Undo and redo",
                command: "mkdir test && undo && redo",
            },
        ],
        related: &["undo", "history"],
        proof_operation: None,
    },

    // cd
    HelpEntry {
        name: "cd",
        summary: "Change current directory",
        usage: "cd <path>",
        description: "Changes the current working directory to the specified path.\n\
                      Use 'cd -' to return to previous directory.",
        examples: &[
            Example {
                description: "Change to subdirectory",
                command: "cd project/src",
            },
            Example {
                description: "Return to previous directory",
                command: "cd -",
            },
        ],
        related: &["pwd", "pushd", "popd"],
        proof_operation: None,
    },

    // help
    HelpEntry {
        name: "help",
        summary: "Display help information",
        usage: "help [command] [-v]",
        description: "Shows help at three levels:\n\
                      - help           : List all commands\n\
                      - help <cmd>     : Quick reference\n\
                      - help -v <cmd>  : Detailed help with examples\n\
                      - man vsh-<cmd>  : Full manual page",
        examples: &[
            Example {
                description: "List all commands",
                command: "help",
            },
            Example {
                description: "Quick help for mkdir",
                command: "help mkdir",
            },
            Example {
                description: "Detailed help with examples",
                command: "help -v mkdir",
            },
        ],
        related: &[],
        proof_operation: None,
    },
];

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_get_help() {
        assert!(get_help("mkdir").is_some());
        assert!(get_help("rm").is_some());
        assert!(get_help("nonexistent").is_none());
    }

    #[test]
    fn test_help_entries_complete() {
        // Verify all entries have required fields
        for entry in HELP_DATABASE.iter() {
            assert!(!entry.name.is_empty());
            assert!(!entry.summary.is_empty());
            assert!(!entry.usage.is_empty());
            assert!(!entry.description.is_empty());
        }
    }
}
