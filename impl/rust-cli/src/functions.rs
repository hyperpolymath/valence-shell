// SPDX-License-Identifier: PMPL-1.0-or-later
//! Shell Functions
//!
//! Implements POSIX shell function support:
//! - Function definition: `fname() { commands; }` and `function fname { commands; }`
//! - Function invocation with positional parameter scoping
//! - `local` variable declarations within functions
//! - `return` builtin with exit code
//! - `unset -f` to remove functions
//! - Nested function calls via a parameter stack
//!
//! Author: Jonathan D.A. Jewell

use std::collections::HashMap;

/// Source location where a function was defined
#[derive(Debug, Clone, PartialEq)]
pub struct SourceLocation {
    /// File or input source (e.g., "stdin", "/path/to/script.sh")
    pub source: String,
    /// Line number where the definition starts
    pub line: usize,
}

/// A shell function definition
#[derive(Debug, Clone, PartialEq)]
pub struct FunctionDef {
    /// Function name
    pub name: String,
    /// Body of the function as raw command strings
    /// Each entry is one command (semicolon-separated lines from the braces)
    pub body: Vec<String>,
    /// Where the function was defined
    pub source_location: SourceLocation,
}

/// Manages shell functions and parameter scoping for nested calls
#[derive(Debug)]
pub struct FunctionTable {
    /// Registered function definitions (name -> definition)
    functions: HashMap<String, FunctionDef>,
    /// Stack of saved positional parameters for nested function calls.
    /// Each entry is (saved_params, local_variables) from the calling scope.
    param_stack: Vec<FunctionFrame>,
}

/// A single function call frame on the parameter stack
#[derive(Debug, Clone)]
pub struct FunctionFrame {
    /// Saved positional parameters from the caller
    pub saved_params: Vec<String>,
    /// Local variable names declared in this frame (for cleanup on return)
    pub local_vars: Vec<String>,
    /// Saved values of variables that were shadowed by `local` declarations
    /// Maps variable name -> Option<previous_value> (None if variable was unset)
    pub saved_vars: HashMap<String, Option<String>>,
}

impl FunctionTable {
    /// Create a new empty function table
    pub fn new() -> Self {
        Self {
            functions: HashMap::new(),
            param_stack: Vec::new(),
        }
    }

    /// Define (or redefine) a shell function
    pub fn define(&mut self, def: FunctionDef) {
        self.functions.insert(def.name.clone(), def);
    }

    /// Look up a function by name
    pub fn get(&self, name: &str) -> Option<&FunctionDef> {
        self.functions.get(name)
    }

    /// Remove a function definition (`unset -f name`)
    /// Returns true if the function existed and was removed
    pub fn unset(&mut self, name: &str) -> bool {
        self.functions.remove(name).is_some()
    }

    /// Check if a function is defined
    pub fn is_defined(&self, name: &str) -> bool {
        self.functions.contains_key(name)
    }

    /// Get all defined function names (for tab completion, etc.)
    pub fn names(&self) -> Vec<&str> {
        self.functions.keys().map(|s| s.as_str()).collect()
    }

    /// Push a new function call frame onto the parameter stack.
    /// Call this before executing a function body.
    pub fn push_frame(&mut self, saved_params: Vec<String>) {
        self.param_stack.push(FunctionFrame {
            saved_params,
            local_vars: Vec::new(),
            saved_vars: HashMap::new(),
        });
    }

    /// Pop the current function call frame.
    /// Returns the frame so the caller can restore positional params and local vars.
    pub fn pop_frame(&mut self) -> Option<FunctionFrame> {
        self.param_stack.pop()
    }

    /// Get a mutable reference to the current (topmost) frame, if any
    pub fn current_frame_mut(&mut self) -> Option<&mut FunctionFrame> {
        self.param_stack.last_mut()
    }

    /// Get the current call depth (0 = not in a function)
    pub fn call_depth(&self) -> usize {
        self.param_stack.len()
    }

    /// Register a `local` variable in the current frame.
    /// Saves the previous value (or None if unset) so it can be restored on return.
    pub fn declare_local(&mut self, name: &str, previous_value: Option<String>) {
        if let Some(frame) = self.param_stack.last_mut() {
            // Only save the first time a variable is declared local in this frame
            if !frame.saved_vars.contains_key(name) {
                frame.saved_vars.insert(name.to_string(), previous_value);
                frame.local_vars.push(name.to_string());
            }
        }
    }
}

impl Default for FunctionTable {
    fn default() -> Self {
        Self::new()
    }
}

/// Parse a function definition from input text.
///
/// Supports two syntaxes:
/// 1. `fname() { commands; }` (POSIX standard)
/// 2. `function fname { commands; }` (bash extension)
///
/// Returns Some((name, body_commands)) on success, None if not a function definition.
pub fn parse_function_def(input: &str) -> Option<(String, Vec<String>)> {
    let trimmed = input.trim();

    // Try syntax 1: fname() { commands; }
    if let Some(result) = try_parse_posix_function(trimmed) {
        return Some(result);
    }

    // Try syntax 2: function fname { commands; }
    if let Some(result) = try_parse_bash_function(trimmed) {
        return Some(result);
    }

    None
}

/// Try to parse `fname() { commands; }` syntax
fn try_parse_posix_function(input: &str) -> Option<(String, Vec<String>)> {
    // Look for `name()` pattern followed by `{`
    let paren_pos = input.find("()")?;
    let name = input[..paren_pos].trim();

    // Validate function name (same rules as variable names)
    if name.is_empty() || !is_valid_function_name(name) {
        return None;
    }

    // Find the body between { and }
    let after_parens = input[paren_pos + 2..].trim();

    // Must start with {
    if !after_parens.starts_with('{') {
        return None;
    }

    // Must end with }
    if !after_parens.ends_with('}') {
        return None;
    }

    // Extract body (everything between { and })
    let body_str = after_parens[1..after_parens.len() - 1].trim();
    let body = parse_function_body(body_str);

    Some((name.to_string(), body))
}

/// Try to parse `function fname { commands; }` syntax (bash extension)
fn try_parse_bash_function(input: &str) -> Option<(String, Vec<String>)> {
    if !input.starts_with("function ") {
        return None;
    }

    let rest = input["function ".len()..].trim();

    // Find the name (until whitespace or `(` or `{`)
    let name_end = rest.find(|c: char| c.is_whitespace() || c == '(' || c == '{')?;
    let name = &rest[..name_end];

    if !is_valid_function_name(name) {
        return None;
    }

    let after_name = rest[name_end..].trim();

    // Skip optional () if present
    let body_start = if after_name.starts_with("()") {
        after_name[2..].trim()
    } else {
        after_name
    };

    // Must start with {
    if !body_start.starts_with('{') {
        return None;
    }

    // Must end with }
    if !body_start.ends_with('}') {
        return None;
    }

    let body_str = body_start[1..body_start.len() - 1].trim();
    let body = parse_function_body(body_str);

    Some((name.to_string(), body))
}

/// Parse the body of a function (content between braces) into individual commands
fn parse_function_body(body_str: &str) -> Vec<String> {
    // Split on semicolons and newlines, filtering empty segments
    body_str
        .split(|c| c == ';' || c == '\n')
        .map(|s| s.trim().to_string())
        .filter(|s| !s.is_empty())
        .collect()
}

/// Check if a string is a valid function name.
/// Same rules as variable names: starts with letter or underscore,
/// then alphanumeric or underscore.
pub fn is_valid_function_name(name: &str) -> bool {
    if name.is_empty() {
        return false;
    }
    let mut chars = name.chars();
    let first = chars.next().expect("TODO: handle error");
    if !first.is_alphabetic() && first != '_' {
        return false;
    }
    chars.all(|c| c.is_alphanumeric() || c == '_')
}

#[cfg(test)]
mod tests {
    use super::*;

    // =====================================================================
    // Function definition parsing tests
    // =====================================================================

    #[test]
    fn test_parse_posix_function_def() {
        let result = parse_function_def("greet() { echo hello; }");
        assert!(result.is_some());
        let (name, body) = result.expect("TODO: handle error");
        assert_eq!(name, "greet");
        assert_eq!(body, vec!["echo hello"]);
    }

    #[test]
    fn test_parse_posix_function_multi_commands() {
        let result = parse_function_def("setup() { mkdir src; touch src/main.rs; echo done; }");
        assert!(result.is_some());
        let (name, body) = result.expect("TODO: handle error");
        assert_eq!(name, "setup");
        assert_eq!(body, vec!["mkdir src", "touch src/main.rs", "echo done"]);
    }

    #[test]
    fn test_parse_bash_function_def() {
        let result = parse_function_def("function greet { echo hello; }");
        assert!(result.is_some());
        let (name, body) = result.expect("TODO: handle error");
        assert_eq!(name, "greet");
        assert_eq!(body, vec!["echo hello"]);
    }

    #[test]
    fn test_parse_bash_function_with_parens() {
        let result = parse_function_def("function greet() { echo hello; }");
        assert!(result.is_some());
        let (name, body) = result.expect("TODO: handle error");
        assert_eq!(name, "greet");
        assert_eq!(body, vec!["echo hello"]);
    }

    #[test]
    fn test_parse_function_not_a_function() {
        assert!(parse_function_def("echo hello").is_none());
        assert!(parse_function_def("mkdir test").is_none());
        assert!(parse_function_def("if true; then echo yes; fi").is_none());
    }

    #[test]
    fn test_parse_function_invalid_name() {
        assert!(parse_function_def("123bad() { echo x; }").is_none());
        assert!(parse_function_def("() { echo x; }").is_none());
    }

    #[test]
    fn test_valid_function_name() {
        assert!(is_valid_function_name("greet"));
        assert!(is_valid_function_name("_private"));
        assert!(is_valid_function_name("my_func_2"));
        assert!(!is_valid_function_name(""));
        assert!(!is_valid_function_name("123"));
        assert!(!is_valid_function_name("a-b"));
    }

    // =====================================================================
    // FunctionTable tests
    // =====================================================================

    #[test]
    fn test_function_table_define_and_get() {
        let mut table = FunctionTable::new();
        let def = FunctionDef {
            name: "greet".to_string(),
            body: vec!["echo hello".to_string()],
            source_location: SourceLocation {
                source: "stdin".to_string(),
                line: 1,
            },
        };
        table.define(def.clone());
        assert!(table.is_defined("greet"));
        assert_eq!(table.get("greet"), Some(&def));
        assert!(!table.is_defined("nonexistent"));
    }

    #[test]
    fn test_function_table_unset() {
        let mut table = FunctionTable::new();
        table.define(FunctionDef {
            name: "greet".to_string(),
            body: vec!["echo hello".to_string()],
            source_location: SourceLocation {
                source: "stdin".to_string(),
                line: 1,
            },
        });
        assert!(table.unset("greet"));
        assert!(!table.is_defined("greet"));
        assert!(!table.unset("nonexistent"));
    }

    #[test]
    fn test_function_table_redefine() {
        let mut table = FunctionTable::new();
        table.define(FunctionDef {
            name: "greet".to_string(),
            body: vec!["echo hello".to_string()],
            source_location: SourceLocation {
                source: "stdin".to_string(),
                line: 1,
            },
        });
        table.define(FunctionDef {
            name: "greet".to_string(),
            body: vec!["echo goodbye".to_string()],
            source_location: SourceLocation {
                source: "stdin".to_string(),
                line: 5,
            },
        });
        let def = table.get("greet").expect("TODO: handle error");
        assert_eq!(def.body, vec!["echo goodbye"]);
    }

    // =====================================================================
    // Parameter stack tests (nested function calls)
    // =====================================================================

    #[test]
    fn test_parameter_stack_push_pop() {
        let mut table = FunctionTable::new();
        assert_eq!(table.call_depth(), 0);

        table.push_frame(vec!["arg1".to_string(), "arg2".to_string()]);
        assert_eq!(table.call_depth(), 1);

        table.push_frame(vec!["nested_arg".to_string()]);
        assert_eq!(table.call_depth(), 2);

        let frame = table.pop_frame().expect("TODO: handle error");
        assert_eq!(frame.saved_params, vec!["nested_arg"]);
        assert_eq!(table.call_depth(), 1);

        let frame = table.pop_frame().expect("TODO: handle error");
        assert_eq!(frame.saved_params, vec!["arg1", "arg2"]);
        assert_eq!(table.call_depth(), 0);

        assert!(table.pop_frame().is_none());
    }

    #[test]
    fn test_local_variable_tracking() {
        let mut table = FunctionTable::new();
        table.push_frame(vec![]);

        table.declare_local("x", Some("old_value".to_string()));
        table.declare_local("y", None);

        let frame = table.pop_frame().expect("TODO: handle error");
        assert_eq!(frame.local_vars, vec!["x", "y"]);
        assert_eq!(
            frame.saved_vars.get("x"),
            Some(&Some("old_value".to_string()))
        );
        assert_eq!(frame.saved_vars.get("y"), Some(&None));
    }

    #[test]
    fn test_local_variable_no_double_save() {
        let mut table = FunctionTable::new();
        table.push_frame(vec![]);

        // First declaration saves the previous value
        table.declare_local("x", Some("original".to_string()));
        // Second declaration in same frame should NOT overwrite the saved value
        table.declare_local("x", Some("modified".to_string()));

        let frame = table.pop_frame().expect("TODO: handle error");
        // The saved value should be "original", not "modified"
        assert_eq!(
            frame.saved_vars.get("x"),
            Some(&Some("original".to_string()))
        );
    }
}
