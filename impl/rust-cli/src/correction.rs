// SPDX-License-Identifier: PLMP-1.0-or-later
//! Command Correction (zsh-style "Did you mean?")
//!
//! Suggests corrections for misspelled commands using Levenshtein distance.
//! Searches both built-in commands and executables in PATH.

use std::env;
use std::fs;
use std::path::PathBuf;

/// Calculate Levenshtein distance between two strings
///
/// This is the minimum number of single-character edits (insertions, deletions,
/// or substitutions) required to change one string into the other.
///
/// # Examples
///
/// ```
/// use vsh::correction::levenshtein_distance;
///
/// assert_eq!(levenshtein_distance("kitten", "sitting"), 3);
/// assert_eq!(levenshtein_distance("sl", "ls"), 2); // swap 2 chars
/// ```
pub fn levenshtein_distance(a: &str, b: &str) -> usize {
    let len_a = a.chars().count();
    let len_b = b.chars().count();

    if len_a == 0 {
        return len_b;
    }
    if len_b == 0 {
        return len_a;
    }

    // Create distance matrix
    let mut matrix = vec![vec![0; len_b + 1]; len_a + 1];

    // Initialize first row and column
    for i in 0..=len_a {
        matrix[i][0] = i;
    }
    for j in 0..=len_b {
        matrix[0][j] = j;
    }

    let chars_a: Vec<char> = a.chars().collect();
    let chars_b: Vec<char> = b.chars().collect();

    // Fill matrix
    for i in 1..=len_a {
        for j in 1..=len_b {
            let cost = if chars_a[i - 1] == chars_b[j - 1] {
                0
            } else {
                1
            };

            matrix[i][j] = std::cmp::min(
                std::cmp::min(
                    matrix[i - 1][j] + 1,      // Deletion
                    matrix[i][j - 1] + 1,      // Insertion
                ),
                matrix[i - 1][j - 1] + cost,  // Substitution
            );
        }
    }

    matrix[len_a][len_b]
}

/// Get list of all available commands (built-ins + PATH)
fn get_all_commands() -> Vec<String> {
    let mut commands = Vec::new();

    // Built-in commands
    let builtins: Vec<String> = vec![
        "cd", "exit", "undo", "redo", "history", "help",
        "mkdir", "rmdir", "touch", "rm",
        "test", "[",
        "pwd", "echo", "export", "unset", "set",
        "jobs", "fg", "bg", "kill",
    ].iter().map(|s| s.to_string()).collect();

    commands.extend(builtins);

    // Commands from PATH
    if let Ok(path_var) = env::var("PATH") {
        for dir in path_var.split(':') {
            if let Ok(entries) = fs::read_dir(dir) {
                for entry in entries.flatten() {
                    if let Ok(file_type) = entry.file_type() {
                        if file_type.is_file() || file_type.is_symlink() {
                            if let Some(name) = entry.file_name().to_str() {
                                // Check if executable (Unix only)
                                #[cfg(unix)]
                                {
                                    use std::os::unix::fs::PermissionsExt;
                                    if let Ok(metadata) = entry.metadata() {
                                        let permissions = metadata.permissions();
                                        if permissions.mode() & 0o111 != 0 {
                                            commands.push(name.to_string());
                                        }
                                    }
                                }

                                #[cfg(not(unix))]
                                commands.push(name.to_string());
                            }
                        }
                    }
                }
            }
        }
    }

    // Remove duplicates
    commands.sort();
    commands.dedup();

    commands
}

/// Suggest a correction for a misspelled command
///
/// Returns the best match if one is found within a reasonable edit distance (≤2).
/// Searches both built-in commands and executables in PATH.
///
/// # Examples
///
/// ```
/// use vsh::correction::suggest_correction;
///
/// // Typical typo
/// assert_eq!(suggest_correction("sl"), Some("ls".to_string()));
///
/// // Command not found, no good match
/// assert_eq!(suggest_correction("xyzabc"), None);
/// ```
pub fn suggest_correction(cmd: &str) -> Option<String> {
    let known_commands = get_all_commands();
    let mut best_match = None;
    let mut min_distance = usize::MAX;

    for known in known_commands {
        let distance = levenshtein_distance(cmd, &known);

        // Only suggest if:
        // 1. Distance ≤ 2 (reasonable typo)
        // 2. Better than current best
        // 3. Not too different in length (avoid "a" → "cat" suggestions)
        let len_diff = (cmd.len() as i32 - known.len() as i32).abs();
        if distance <= 2 && distance < min_distance && len_diff <= 3 {
            min_distance = distance;
            best_match = Some(known);
        }
    }

    best_match
}

/// Suggest multiple possible corrections (up to N)
///
/// Returns up to `limit` suggestions, ordered by edit distance.
///
/// # Examples
///
/// ```
/// use vsh::correction::suggest_corrections;
///
/// let suggestions = suggest_corrections("gti", 3);
/// assert!(suggestions.contains(&"git".to_string()));
/// ```
pub fn suggest_corrections(cmd: &str, limit: usize) -> Vec<String> {
    let known_commands = get_all_commands();
    let mut matches: Vec<(usize, String)> = Vec::new();

    for known in known_commands {
        let distance = levenshtein_distance(cmd, &known);

        let len_diff = (cmd.len() as i32 - known.len() as i32).abs();
        if distance <= 2 && len_diff <= 3 {
            matches.push((distance, known));
        }
    }

    // Sort by distance (ascending)
    matches.sort_by_key(|(dist, _)| *dist);

    // Take top N, return just the commands
    matches.into_iter()
        .take(limit)
        .map(|(_, cmd)| cmd)
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_levenshtein_distance() {
        assert_eq!(levenshtein_distance("", ""), 0);
        assert_eq!(levenshtein_distance("abc", "abc"), 0);
        assert_eq!(levenshtein_distance("", "abc"), 3);
        assert_eq!(levenshtein_distance("abc", ""), 3);

        // Classic example
        assert_eq!(levenshtein_distance("kitten", "sitting"), 3);

        // Common typos
        assert_eq!(levenshtein_distance("sl", "ls"), 2); // Swap
        assert_eq!(levenshtein_distance("gti", "git"), 2); // Transpose = delete + insert
        assert_eq!(levenshtein_distance("mkdr", "mkdir"), 1); // One insertion
    }

    #[test]
    fn test_suggest_correction_builtin() {
        // Common typos for built-ins
        assert_eq!(suggest_correction("mkdr"), Some("mkdir".to_string()));
        assert_eq!(suggest_correction("rmdr"), Some("rmdir".to_string()));
        assert_eq!(suggest_correction("exot"), Some("exit".to_string()));

        // No match (too different)
        assert_eq!(suggest_correction("xyzabc"), None);

        // Exact match returns itself (distance 0)
        let suggestion = suggest_correction("mkdir");
        assert!(suggestion.is_some());
    }

    #[test]
    fn test_suggest_corrections_multiple() {
        let suggestions = suggest_corrections("mkdr", 3);

        // Should include mkdir
        assert!(suggestions.contains(&"mkdir".to_string()));

        // Should be limited
        assert!(suggestions.len() <= 3);
    }

    #[test]
    fn test_length_difference_filter() {
        // Should not suggest very short commands for long typos
        let suggestion = suggest_correction("verylongcommandname");
        // Unlikely to match anything within distance 2 and length diff 3
        assert!(suggestion.is_none() || suggestion.unwrap().len() >= 15);
    }
}
