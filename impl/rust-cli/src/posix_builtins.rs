// SPDX-License-Identifier: PMPL-1.0-or-later
//! POSIX Builtins — trap, alias/unalias, IFS word splitting
//!
//! Implements high-priority missing POSIX features:
//! - `trap` — register signal handlers (EXIT, INT, TERM, HUP)
//! - `alias`/`unalias` — command aliases with expansion
//! - `$IFS` word splitting — split unquoted expansions by IFS
//!
//! Author: Jonathan D.A. Jewell

use std::collections::HashMap;

// =========================================================================
// Trap (Signal Handlers)
// =========================================================================

/// Signal types that can be trapped
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TrapSignal {
    /// EXIT (pseudo-signal) — runs when shell exits
    Exit,
    /// INT (SIGINT) — Ctrl+C
    Int,
    /// TERM (SIGTERM) — termination request
    Term,
    /// HUP (SIGHUP) — hangup
    Hup,
}

impl TrapSignal {
    /// Parse a signal name or number
    pub fn from_str(s: &str) -> Option<Self> {
        match s.to_uppercase().as_str() {
            "EXIT" | "0" => Some(Self::Exit),
            "INT" | "SIGINT" | "2" => Some(Self::Int),
            "TERM" | "SIGTERM" | "15" => Some(Self::Term),
            "HUP" | "SIGHUP" | "1" => Some(Self::Hup),
            _ => None,
        }
    }

    /// Get the signal name for display
    pub fn name(&self) -> &'static str {
        match self {
            Self::Exit => "EXIT",
            Self::Int => "INT",
            Self::Term => "TERM",
            Self::Hup => "HUP",
        }
    }
}

/// Manages trap (signal handler) registrations
#[derive(Debug, Clone)]
pub struct TrapTable {
    /// Registered trap handlers: signal -> command string to execute
    handlers: HashMap<TrapSignal, String>,
}

impl TrapTable {
    /// Create a new empty trap table
    pub fn new() -> Self {
        Self {
            handlers: HashMap::new(),
        }
    }

    /// Register a trap handler.
    /// If action is empty string, the signal is ignored.
    /// If action is "-", the signal is reset to default behavior.
    pub fn set(&mut self, signal: TrapSignal, action: &str) {
        if action == "-" {
            self.handlers.remove(&signal);
        } else {
            self.handlers.insert(signal, action.to_string());
        }
    }

    /// Get the trap handler for a signal (if registered)
    pub fn get(&self, signal: TrapSignal) -> Option<&str> {
        self.handlers.get(&signal).map(|s| s.as_str())
    }

    /// Remove all trap handlers
    pub fn clear(&mut self) {
        self.handlers.clear();
    }

    /// Get all registered traps for display
    pub fn list(&self) -> Vec<(TrapSignal, &str)> {
        self.handlers
            .iter()
            .map(|(sig, action)| (*sig, action.as_str()))
            .collect()
    }

    /// Check if a signal has a handler registered
    pub fn is_trapped(&self, signal: TrapSignal) -> bool {
        self.handlers.contains_key(&signal)
    }
}

impl Default for TrapTable {
    fn default() -> Self {
        Self::new()
    }
}

// =========================================================================
// Alias/Unalias
// =========================================================================

/// Manages command aliases
#[derive(Debug, Clone)]
pub struct AliasTable {
    /// Registered aliases: name -> expansion
    aliases: HashMap<String, String>,
}

impl AliasTable {
    /// Create a new empty alias table
    pub fn new() -> Self {
        Self {
            aliases: HashMap::new(),
        }
    }

    /// Define an alias
    pub fn set(&mut self, name: &str, expansion: &str) {
        self.aliases.insert(name.to_string(), expansion.to_string());
    }

    /// Remove an alias. Returns true if it existed.
    pub fn unset(&mut self, name: &str) -> bool {
        self.aliases.remove(name).is_some()
    }

    /// Look up an alias by name
    pub fn get(&self, name: &str) -> Option<&str> {
        self.aliases.get(name).map(|s| s.as_str())
    }

    /// Check if a name is an alias
    pub fn is_alias(&self, name: &str) -> bool {
        self.aliases.contains_key(name)
    }

    /// Get all aliases for display (sorted by name)
    pub fn list(&self) -> Vec<(&str, &str)> {
        let mut result: Vec<_> = self
            .aliases
            .iter()
            .map(|(k, v)| (k.as_str(), v.as_str()))
            .collect();
        result.sort_by_key(|(k, _)| *k);
        result
    }

    /// Expand aliases in a command string.
    /// Only the first word is checked for alias expansion.
    /// If the expansion ends with a space, the next word is also checked (POSIX).
    pub fn expand(&self, input: &str) -> String {
        let trimmed = input.trim();
        if trimmed.is_empty() {
            return input.to_string();
        }

        // Split into first word and rest
        let first_space = trimmed.find(char::is_whitespace);
        let (first_word, rest) = match first_space {
            Some(pos) => (&trimmed[..pos], &trimmed[pos..]),
            None => (trimmed, ""),
        };

        // Check if first word is an alias
        if let Some(expansion) = self.aliases.get(first_word) {
            // POSIX: if expansion ends with space, also expand next word
            if expansion.ends_with(' ') && !rest.trim().is_empty() {
                let rest_trimmed = rest.trim();
                let rest_first_space = rest_trimmed.find(char::is_whitespace);
                let (next_word, next_rest) = match rest_first_space {
                    Some(pos) => (&rest_trimmed[..pos], &rest_trimmed[pos..]),
                    None => (rest_trimmed, ""),
                };
                if let Some(next_expansion) = self.aliases.get(next_word) {
                    return format!("{}{}{}", expansion, next_expansion, next_rest);
                }
            }
            format!("{}{}", expansion, rest)
        } else {
            input.to_string()
        }
    }
}

impl Default for AliasTable {
    fn default() -> Self {
        Self::new()
    }
}

// =========================================================================
// IFS Word Splitting
// =========================================================================

/// Default IFS value: space, tab, newline
pub const DEFAULT_IFS: &str = " \t\n";

/// Split a string according to IFS rules.
///
/// POSIX word splitting rules:
/// - IFS whitespace characters (space, tab, newline) are treated specially:
///   leading/trailing are trimmed, consecutive runs act as one delimiter
/// - IFS non-whitespace characters each act as a delimiter
/// - If IFS is empty (set to ""), no word splitting occurs
/// - If IFS is unset, defaults to " \t\n"
pub fn ifs_split(input: &str, ifs: &str) -> Vec<String> {
    if ifs.is_empty() {
        // Empty IFS: no splitting
        return vec![input.to_string()];
    }

    let ifs_whitespace: Vec<char> = ifs.chars().filter(|c| c.is_whitespace()).collect();
    let ifs_non_whitespace: Vec<char> = ifs.chars().filter(|c| !c.is_whitespace()).collect();

    // If IFS is entirely whitespace (the common case), use simpler splitting
    if ifs_non_whitespace.is_empty() {
        return input
            .split(|c: char| ifs_whitespace.contains(&c))
            .filter(|s| !s.is_empty())
            .map(|s| s.to_string())
            .collect();
    }

    // General case: mix of whitespace and non-whitespace IFS chars
    //
    // POSIX rule: IFS whitespace around non-whitespace delimiters is absorbed.
    // "one : two" with IFS=" :" splits as ["one", "two"] (not ["one", "", "two"]).
    // But ":one:two:" with IFS=":" splits as ["", "one", "two", ""]
    // because leading/trailing non-ws delimiters produce empty fields.
    let mut words = Vec::new();
    let mut current = String::new();
    let mut chars = input.chars().peekable();
    let mut after_whitespace = false;

    // Skip leading IFS whitespace
    while let Some(&c) = chars.peek() {
        if ifs_whitespace.contains(&c) {
            chars.next();
        } else {
            break;
        }
    }

    while let Some(c) = chars.next() {
        if ifs_non_whitespace.contains(&c) {
            // Non-whitespace IFS delimiter: creates a field boundary.
            // If we just ate whitespace, the whitespace was part of this
            // delimiter sequence (POSIX: IFS ws is absorbed adjacent to nw delimiters).
            if !current.is_empty() || !after_whitespace {
                words.push(current.clone());
            }
            current.clear();
            after_whitespace = false;
            // Skip adjacent IFS whitespace
            while let Some(&nc) = chars.peek() {
                if ifs_whitespace.contains(&nc) {
                    chars.next();
                } else {
                    break;
                }
            }
        } else if ifs_whitespace.contains(&c) {
            // IFS whitespace: skip run of whitespace, create boundary only if
            // current word is non-empty
            if !current.is_empty() {
                words.push(current.clone());
                current.clear();
                after_whitespace = true;
            }
            while let Some(&nc) = chars.peek() {
                if ifs_whitespace.contains(&nc) {
                    chars.next();
                } else {
                    break;
                }
            }
        } else {
            current.push(c);
            after_whitespace = false;
        }
    }

    // Don't lose the last word
    if !current.is_empty() {
        words.push(current);
    }

    words
}

// =========================================================================
// Tests
// =========================================================================

#[cfg(test)]
mod tests {
    use super::*;

    // === TrapTable tests ===

    #[test]
    fn test_trap_signal_from_str() {
        assert_eq!(TrapSignal::from_str("EXIT"), Some(TrapSignal::Exit));
        assert_eq!(TrapSignal::from_str("0"), Some(TrapSignal::Exit));
        assert_eq!(TrapSignal::from_str("INT"), Some(TrapSignal::Int));
        assert_eq!(TrapSignal::from_str("SIGINT"), Some(TrapSignal::Int));
        assert_eq!(TrapSignal::from_str("2"), Some(TrapSignal::Int));
        assert_eq!(TrapSignal::from_str("TERM"), Some(TrapSignal::Term));
        assert_eq!(TrapSignal::from_str("15"), Some(TrapSignal::Term));
        assert_eq!(TrapSignal::from_str("HUP"), Some(TrapSignal::Hup));
        assert_eq!(TrapSignal::from_str("1"), Some(TrapSignal::Hup));
        assert_eq!(TrapSignal::from_str("BOGUS"), None);
    }

    #[test]
    fn test_trap_table_set_and_get() {
        let mut traps = TrapTable::new();
        traps.set(TrapSignal::Exit, "echo bye");
        assert_eq!(traps.get(TrapSignal::Exit), Some("echo bye"));
        assert!(traps.is_trapped(TrapSignal::Exit));
        assert!(!traps.is_trapped(TrapSignal::Int));
    }

    #[test]
    fn test_trap_table_reset() {
        let mut traps = TrapTable::new();
        traps.set(TrapSignal::Int, "echo interrupted");
        assert!(traps.is_trapped(TrapSignal::Int));
        traps.set(TrapSignal::Int, "-");
        assert!(!traps.is_trapped(TrapSignal::Int));
    }

    #[test]
    fn test_trap_table_list() {
        let mut traps = TrapTable::new();
        traps.set(TrapSignal::Exit, "cleanup");
        traps.set(TrapSignal::Int, "handle_int");
        let list = traps.list();
        assert_eq!(list.len(), 2);
    }

    // === AliasTable tests ===

    #[test]
    fn test_alias_set_and_get() {
        let mut aliases = AliasTable::new();
        aliases.set("ll", "ls -la");
        assert_eq!(aliases.get("ll"), Some("ls -la"));
        assert!(aliases.is_alias("ll"));
        assert!(!aliases.is_alias("ls"));
    }

    #[test]
    fn test_alias_unset() {
        let mut aliases = AliasTable::new();
        aliases.set("ll", "ls -la");
        assert!(aliases.unset("ll"));
        assert!(!aliases.is_alias("ll"));
        assert!(!aliases.unset("nonexistent"));
    }

    #[test]
    fn test_alias_expand_simple() {
        let mut aliases = AliasTable::new();
        aliases.set("ll", "ls -la");
        assert_eq!(aliases.expand("ll /tmp"), "ls -la /tmp");
    }

    #[test]
    fn test_alias_expand_no_match() {
        let aliases = AliasTable::new();
        assert_eq!(aliases.expand("echo hello"), "echo hello");
    }

    #[test]
    fn test_alias_expand_trailing_space() {
        let mut aliases = AliasTable::new();
        aliases.set("sudo", "sudo ");
        aliases.set("ll", "ls -la");
        // When alias ends with space, next word is also expanded
        assert_eq!(aliases.expand("sudo ll /tmp"), "sudo ls -la /tmp");
    }

    #[test]
    fn test_alias_list_sorted() {
        let mut aliases = AliasTable::new();
        aliases.set("z", "zzz");
        aliases.set("a", "aaa");
        aliases.set("m", "mmm");
        let list = aliases.list();
        let names: Vec<&str> = list.iter().map(|(k, _)| *k).collect();
        assert_eq!(names, vec!["a", "m", "z"]);
    }

    // === IFS word splitting tests ===

    #[test]
    fn test_ifs_split_default() {
        let result = ifs_split("  hello   world  ", DEFAULT_IFS);
        assert_eq!(result, vec!["hello", "world"]);
    }

    #[test]
    fn test_ifs_split_tabs_and_newlines() {
        let result = ifs_split("hello\tworld\nfoo", DEFAULT_IFS);
        assert_eq!(result, vec!["hello", "world", "foo"]);
    }

    #[test]
    fn test_ifs_split_empty_ifs() {
        // Empty IFS means no splitting
        let result = ifs_split("hello world", "");
        assert_eq!(result, vec!["hello world"]);
    }

    #[test]
    fn test_ifs_split_custom_delimiter() {
        let result = ifs_split("one:two:three", ":");
        assert_eq!(result, vec!["one", "two", "three"]);
    }

    #[test]
    fn test_ifs_split_mixed_whitespace_and_nonwhitespace() {
        let result = ifs_split("one : two : three", " :");
        assert_eq!(result, vec!["one", "two", "three"]);
    }

    #[test]
    fn test_ifs_split_leading_delimiter() {
        let result = ifs_split(":one:two", ":");
        assert_eq!(result, vec!["", "one", "two"]);
    }

    #[test]
    fn test_ifs_split_empty_input() {
        let result = ifs_split("", DEFAULT_IFS);
        assert!(result.is_empty());
    }

    #[test]
    fn test_ifs_split_only_whitespace() {
        let result = ifs_split("   \t  \n  ", DEFAULT_IFS);
        assert!(result.is_empty());
    }
}
