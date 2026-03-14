// SPDX-License-Identifier: PMPL-1.0-or-later
//! Tests for shell functions (TASK 1) and script execution (TASK 2)
//!
//! Covers:
//! - Function definition and invocation
//! - Nested function calls
//! - Positional parameters in functions
//! - Local variables
//! - Return values
//! - unset -f
//! - Script execution from file
//! - -c flag execution
//! - Script arguments
//! - source/dot builtin
//!
//! Author: Jonathan D.A. Jewell

use anyhow::Result;
use std::fs;
use tempfile::tempdir;
use vsh::executable::{ExecutableCommand, ExecutionResult};
use vsh::parser::parse_command;
use vsh::state::ShellState;

// =========================================================================
// TASK 1: Shell Function Tests
// =========================================================================

#[test]
fn test_function_definition_posix_syntax() -> Result<()> {
    let temp = tempdir()?;
    let mut state = ShellState::new(temp.path().to_str().unwrap())?;

    // Define a function using POSIX syntax
    let cmd = parse_command("greet() { echo hello; }")?;
    cmd.execute(&mut state)?;

    // Function should be registered
    assert!(state.functions.is_defined("greet"));

    Ok(())
}

#[test]
fn test_function_definition_bash_syntax() -> Result<()> {
    let temp = tempdir()?;
    let mut state = ShellState::new(temp.path().to_str().unwrap())?;

    // Define a function using bash syntax
    let cmd = parse_command("function greet { echo hello; }")?;
    cmd.execute(&mut state)?;

    assert!(state.functions.is_defined("greet"));

    Ok(())
}

#[test]
fn test_function_invocation() -> Result<()> {
    let temp = tempdir()?;
    let mut state = ShellState::new(temp.path().to_str().unwrap())?;

    // Define a function that creates a directory
    let def_cmd = parse_command("mkstuff() { mkdir testdir; }")?;
    def_cmd.execute(&mut state)?;

    // Invoke the function
    let invoke_cmd = parse_command("mkstuff")?;
    invoke_cmd.execute(&mut state)?;

    // Verify the function body executed
    assert!(state.resolve_path("testdir").exists());

    Ok(())
}

#[test]
fn test_function_with_positional_params() -> Result<()> {
    let temp = tempdir()?;
    let mut state = ShellState::new(temp.path().to_str().unwrap())?;

    // Define a function that uses $1
    let def_cmd = parse_command("mknamed() { mkdir $1; }")?;
    def_cmd.execute(&mut state)?;

    // Invoke with argument
    let invoke_cmd = parse_command("mknamed mydir")?;
    invoke_cmd.execute(&mut state)?;

    assert!(state.resolve_path("mydir").exists());

    Ok(())
}

#[test]
fn test_function_restores_positional_params() -> Result<()> {
    let temp = tempdir()?;
    let mut state = ShellState::new(temp.path().to_str().unwrap())?;

    // Set initial positional parameters
    state.set_positional_params(vec!["outer_arg".to_string()]);

    // Define a function
    let def_cmd = parse_command("myfunc() { echo $1; }")?;
    def_cmd.execute(&mut state)?;

    // Invoke with different argument
    let invoke_cmd = parse_command("myfunc inner_arg")?;
    invoke_cmd.execute(&mut state)?;

    // Positional params should be restored
    assert_eq!(
        state.get_positional_param(1),
        Some("outer_arg")
    );

    Ok(())
}

#[test]
fn test_nested_function_calls() -> Result<()> {
    let temp = tempdir()?;
    let mut state = ShellState::new(temp.path().to_str().unwrap())?;

    // Define two functions where one calls the other
    let inner_cmd = parse_command("inner() { mkdir $1; }")?;
    inner_cmd.execute(&mut state)?;

    let outer_cmd = parse_command("outer() { inner nested_dir; }")?;
    outer_cmd.execute(&mut state)?;

    // Call outer
    let invoke_cmd = parse_command("outer")?;
    invoke_cmd.execute(&mut state)?;

    assert!(state.resolve_path("nested_dir").exists());

    Ok(())
}

#[test]
fn test_function_local_variables() -> Result<()> {
    let temp = tempdir()?;
    let mut state = ShellState::new(temp.path().to_str().unwrap())?;

    // Set a global variable
    state.set_variable("X", "global");

    // Define a function that declares a local variable
    let def_cmd = parse_command("myfunc() { local X=local_val; }")?;
    def_cmd.execute(&mut state)?;

    // Invoke the function
    let invoke_cmd = parse_command("myfunc")?;
    invoke_cmd.execute(&mut state)?;

    // Global variable should be restored after function returns
    assert_eq!(state.get_variable("X"), Some("global"));

    Ok(())
}

#[test]
fn test_function_return_value() -> Result<()> {
    let temp = tempdir()?;
    let mut state = ShellState::new(temp.path().to_str().unwrap())?;

    // Define a function that returns a specific exit code
    let def_cmd = parse_command("fail42() { return 42; }")?;
    def_cmd.execute(&mut state)?;

    // Invoke the function
    let invoke_cmd = parse_command("fail42")?;
    let result = invoke_cmd.execute(&mut state)?;

    match result {
        ExecutionResult::ExternalCommand { exit_code } => {
            assert_eq!(exit_code, 42);
        }
        _ => panic!("Expected ExternalCommand result from return"),
    }

    Ok(())
}

#[test]
fn test_return_outside_function_fails() -> Result<()> {
    let temp = tempdir()?;
    let mut state = ShellState::new(temp.path().to_str().unwrap())?;

    let cmd = parse_command("return 0")?;
    let result = cmd.execute(&mut state);

    assert!(result.is_err());
    let err = result.unwrap_err();
    assert!(err.to_string().contains("can only return from a function"));

    Ok(())
}

#[test]
fn test_local_outside_function_fails() -> Result<()> {
    let temp = tempdir()?;
    let mut state = ShellState::new(temp.path().to_str().unwrap())?;

    let cmd = parse_command("local X=5")?;
    let result = cmd.execute(&mut state);

    assert!(result.is_err());
    let err = result.unwrap_err();
    assert!(err.to_string().contains("can only be used in a function"));

    Ok(())
}

#[test]
fn test_unset_function() -> Result<()> {
    let temp = tempdir()?;
    let mut state = ShellState::new(temp.path().to_str().unwrap())?;

    // Define then unset
    let def_cmd = parse_command("greet() { echo hi; }")?;
    def_cmd.execute(&mut state)?;
    assert!(state.functions.is_defined("greet"));

    let unset_cmd = parse_command("unset -f greet")?;
    unset_cmd.execute(&mut state)?;
    assert!(!state.functions.is_defined("greet"));

    Ok(())
}

#[test]
fn test_function_multi_command_body() -> Result<()> {
    let temp = tempdir()?;
    let mut state = ShellState::new(temp.path().to_str().unwrap())?;

    // Define a function with multiple commands
    let def_cmd = parse_command("setup() { mkdir src; mkdir tests; }")?;
    def_cmd.execute(&mut state)?;

    let invoke_cmd = parse_command("setup")?;
    invoke_cmd.execute(&mut state)?;

    assert!(state.resolve_path("src").exists());
    assert!(state.resolve_path("tests").exists());

    Ok(())
}

#[test]
fn test_function_redefine() -> Result<()> {
    let temp = tempdir()?;
    let mut state = ShellState::new(temp.path().to_str().unwrap())?;

    // Define
    let def1 = parse_command("myfn() { mkdir old; }")?;
    def1.execute(&mut state)?;

    // Redefine
    let def2 = parse_command("myfn() { mkdir new; }")?;
    def2.execute(&mut state)?;

    // Invoke should use new definition
    let invoke_cmd = parse_command("myfn")?;
    invoke_cmd.execute(&mut state)?;

    assert!(!state.resolve_path("old").exists());
    assert!(state.resolve_path("new").exists());

    Ok(())
}

// =========================================================================
// TASK 2: Shell Script Execution Tests
// =========================================================================

#[test]
fn test_source_builtin() -> Result<()> {
    let temp = tempdir()?;
    let mut state = ShellState::new(temp.path().to_str().unwrap())?;

    // Create a script file
    let script_path = temp.path().join("setup.sh");
    fs::write(&script_path, "mkdir sourced_dir\n")?;

    // Source it
    let cmd = parse_command(&format!("source {}", script_path.display()))?;
    cmd.execute(&mut state)?;

    assert!(state.resolve_path("sourced_dir").exists());

    Ok(())
}

#[test]
fn test_dot_builtin() -> Result<()> {
    let temp = tempdir()?;
    let mut state = ShellState::new(temp.path().to_str().unwrap())?;

    // Create a script file
    let script_path = temp.path().join("init.sh");
    fs::write(&script_path, "mkdir dotted_dir\n")?;

    // Source using dot
    let cmd = parse_command(&format!(". {}", script_path.display()))?;
    cmd.execute(&mut state)?;

    assert!(state.resolve_path("dotted_dir").exists());

    Ok(())
}

#[test]
fn test_source_with_variables() -> Result<()> {
    let temp = tempdir()?;
    let mut state = ShellState::new(temp.path().to_str().unwrap())?;

    // Create a script that sets variables
    let script_path = temp.path().join("vars.sh");
    fs::write(&script_path, "MY_VAR=hello_from_script\n")?;

    let cmd = parse_command(&format!("source {}", script_path.display()))?;
    cmd.execute(&mut state)?;

    // Variables from sourced file should be visible
    assert_eq!(state.get_variable("MY_VAR"), Some("hello_from_script"));

    Ok(())
}

#[test]
fn test_source_with_comments_and_empty_lines() -> Result<()> {
    let temp = tempdir()?;
    let mut state = ShellState::new(temp.path().to_str().unwrap())?;

    let script_path = temp.path().join("commented.sh");
    fs::write(
        &script_path,
        "# This is a comment\n\n# Another comment\nmkdir real_dir\n\n",
    )?;

    let cmd = parse_command(&format!("source {}", script_path.display()))?;
    cmd.execute(&mut state)?;

    assert!(state.resolve_path("real_dir").exists());

    Ok(())
}

#[test]
fn test_source_nonexistent_file_fails() -> Result<()> {
    let temp = tempdir()?;
    let mut state = ShellState::new(temp.path().to_str().unwrap())?;

    let cmd = parse_command("source /nonexistent/file.sh")?;
    let result = cmd.execute(&mut state);

    assert!(result.is_err());

    Ok(())
}

#[test]
fn test_source_with_function_definitions() -> Result<()> {
    let temp = tempdir()?;
    let mut state = ShellState::new(temp.path().to_str().unwrap())?;

    // Create a script that defines a function
    let script_path = temp.path().join("funcs.sh");
    fs::write(&script_path, "mkproject() { mkdir project; }\n")?;

    let cmd = parse_command(&format!("source {}", script_path.display()))?;
    cmd.execute(&mut state)?;

    // The function should now be defined
    assert!(state.functions.is_defined("mkproject"));

    // And callable
    let invoke_cmd = parse_command("mkproject")?;
    invoke_cmd.execute(&mut state)?;

    assert!(state.resolve_path("project").exists());

    Ok(())
}

// =========================================================================
// TASK 4: POSIX Builtins (trap, alias, unalias)
// =========================================================================

#[test]
fn test_trap_set_and_list() -> Result<()> {
    let temp = tempdir()?;
    let mut state = ShellState::new(temp.path().to_str().unwrap())?;

    // Set a trap
    let cmd = parse_command("trap 'echo bye' EXIT")?;
    cmd.execute(&mut state)?;

    // Verify it's set
    use vsh::posix_builtins::TrapSignal;
    assert_eq!(state.traps.get(TrapSignal::Exit), Some("echo bye"));

    Ok(())
}

#[test]
fn test_trap_reset() -> Result<()> {
    let temp = tempdir()?;
    let mut state = ShellState::new(temp.path().to_str().unwrap())?;

    // Set and then reset
    let set_cmd = parse_command("trap 'echo bye' EXIT")?;
    set_cmd.execute(&mut state)?;

    let reset_cmd = parse_command("trap - EXIT")?;
    reset_cmd.execute(&mut state)?;

    use vsh::posix_builtins::TrapSignal;
    assert!(!state.traps.is_trapped(TrapSignal::Exit));

    Ok(())
}

#[test]
fn test_alias_define_and_list() -> Result<()> {
    let temp = tempdir()?;
    let mut state = ShellState::new(temp.path().to_str().unwrap())?;

    let cmd = parse_command("alias ll=ls")?;
    cmd.execute(&mut state)?;

    assert_eq!(state.aliases.get("ll"), Some("ls"));

    Ok(())
}

#[test]
fn test_unalias() -> Result<()> {
    let temp = tempdir()?;
    let mut state = ShellState::new(temp.path().to_str().unwrap())?;

    let def_cmd = parse_command("alias ll=ls")?;
    def_cmd.execute(&mut state)?;

    let undef_cmd = parse_command("unalias ll")?;
    undef_cmd.execute(&mut state)?;

    assert!(!state.aliases.is_alias("ll"));

    Ok(())
}

#[test]
fn test_unalias_all() -> Result<()> {
    let temp = tempdir()?;
    let mut state = ShellState::new(temp.path().to_str().unwrap())?;

    let def_cmd = parse_command("alias ll=ls")?;
    def_cmd.execute(&mut state)?;

    let undef_cmd = parse_command("unalias -a")?;
    undef_cmd.execute(&mut state)?;

    assert!(state.aliases.list().is_empty());

    Ok(())
}
