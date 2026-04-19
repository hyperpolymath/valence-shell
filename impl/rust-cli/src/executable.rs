// SPDX-License-Identifier: PMPL-1.0-or-later
//! Executable Command Trait
//!
//! Decouples command parsing from execution, creating a clean seam
//! between Layer 1 (Implementation) and Layer 2 (Parser).

use anyhow::Result;

use crate::parser::Command;
use crate::proof_refs::ProofReference;
use crate::redirection;
use crate::state::ShellState;
use crate::{commands, external};

/// Trait for executable commands with proof references.
///
/// Separates concerns between parsing and execution:
/// - Parser creates [`Command`] enum from user input
/// - This trait handles command execution logic
/// - REPL just calls [`execute`](ExecutableCommand::execute)
///
/// # Examples
/// ```no_run
/// use vsh::executable::ExecutableCommand;
/// use vsh::parser::Command;
/// use vsh::state::ShellState;
///
/// let mut state = ShellState::new("/tmp/test")?;
/// let cmd = Command::Mkdir { path: "test".to_string(), redirects: vec![] };
/// cmd.execute(&mut state)?;
/// # Ok::<(), anyhow::Error>(())
/// ```
pub trait ExecutableCommand {
    /// Execute the command, potentially modifying shell state
    fn execute(&self, state: &mut ShellState) -> Result<ExecutionResult>;

    /// Check if this command is reversible (creates undo entry)
    #[allow(dead_code)]
    fn is_reversible(&self) -> bool;

    /// Get the proof reference for this command (if any)
    #[allow(dead_code)]
    fn proof_reference(&self) -> Option<ProofReference>;

    /// Get command description for display
    #[allow(dead_code)]
    fn description(&self) -> String;
}

/// Result of command execution indicating next REPL action.
///
/// Determines whether the REPL should continue, exit, or handle
/// external command exit codes.
#[derive(Debug)]
pub enum ExecutionResult {
    /// Command completed successfully
    Success,

    /// Command requests shell exit
    Exit,

    /// External command executed with exit code
    ExternalCommand { exit_code: i32 },

    /// `return` was invoked inside a function. This variant propagates
    /// up through nested control structures (if/while/for/case/&&/||)
    /// until it is caught by `execute_function_call`, which converts it
    /// back to a regular exit code result.
    Return { exit_code: i32 },
}

impl ExecutableCommand for Command {
    fn execute(&self, state: &mut ShellState) -> Result<ExecutionResult> {
        match self {
            // Filesystem operations (reversible)
            Command::Mkdir { path, redirects } => {
                let expanded_path = crate::parser::expand_variables(path, state);
                if redirects.is_empty() {
                    commands::mkdir(state, &expanded_path, false)?;
                } else {
                    redirection::capture_and_redirect(redirects, state, |s| {
                        commands::mkdir(s, &expanded_path, false)
                    })?;
                }
                Ok(ExecutionResult::Success)
            }

            Command::Rmdir { path, redirects } => {
                let expanded_path = crate::parser::expand_variables(path, state);
                if redirects.is_empty() {
                    commands::rmdir(state, &expanded_path, false)?;
                } else {
                    redirection::capture_and_redirect(redirects, state, |s| {
                        commands::rmdir(s, &expanded_path, false)
                    })?;
                }
                Ok(ExecutionResult::Success)
            }

            Command::Touch { path, redirects } => {
                let expanded_path = crate::parser::expand_variables(path, state);
                if redirects.is_empty() {
                    commands::touch(state, &expanded_path, false)?;
                } else {
                    redirection::capture_and_redirect(redirects, state, |s| {
                        commands::touch(s, &expanded_path, false)
                    })?;
                }
                Ok(ExecutionResult::Success)
            }

            Command::Rm { path, redirects } => {
                let expanded_path = crate::parser::expand_variables(path, state);
                if redirects.is_empty() {
                    commands::rm(state, &expanded_path, false)?;
                } else {
                    redirection::capture_and_redirect(redirects, state, |s| {
                        commands::rm(s, &expanded_path, false)
                    })?;
                }
                Ok(ExecutionResult::Success)
            }

            Command::Cp { src, dst, redirects } => {
                let expanded_src = crate::parser::expand_variables(src, state);
                let expanded_dst = crate::parser::expand_variables(dst, state);
                if redirects.is_empty() {
                    commands::cp(state, &expanded_src, &expanded_dst, false)?;
                } else {
                    redirection::capture_and_redirect(redirects, state, |s| {
                        commands::cp(s, &expanded_src, &expanded_dst, false)
                    })?;
                }
                Ok(ExecutionResult::Success)
            }

            Command::Mv { src, dst, redirects } => {
                let expanded_src = crate::parser::expand_variables(src, state);
                let expanded_dst = crate::parser::expand_variables(dst, state);
                if redirects.is_empty() {
                    commands::mv(state, &expanded_src, &expanded_dst, false)?;
                } else {
                    redirection::capture_and_redirect(redirects, state, |s| {
                        commands::mv(s, &expanded_src, &expanded_dst, false)
                    })?;
                }
                Ok(ExecutionResult::Success)
            }

            Command::Ln { target, link, redirects } => {
                let expanded_target = crate::parser::expand_variables(target, state);
                let expanded_link = crate::parser::expand_variables(link, state);
                if redirects.is_empty() {
                    commands::symlink(state, &expanded_target, &expanded_link, false)?;
                } else {
                    redirection::capture_and_redirect(redirects, state, |s| {
                        commands::symlink(s, &expanded_target, &expanded_link, false)
                    })?;
                }
                Ok(ExecutionResult::Success)
            }

            Command::Chmod { mode, path, redirects } => {
                let expanded_mode = crate::parser::expand_variables(mode, state);
                let expanded_path = crate::parser::expand_variables(path, state);
                if redirects.is_empty() {
                    commands::chmod(state, &expanded_mode, &expanded_path, false)?;
                } else {
                    redirection::capture_and_redirect(redirects, state, |s| {
                        commands::chmod(s, &expanded_mode, &expanded_path, false)
                    })?;
                }
                Ok(ExecutionResult::Success)
            }

            #[cfg(unix)]
            Command::Chown { owner, path, redirects } => {
                let expanded_owner = crate::parser::expand_variables(owner, state);
                let expanded_path = crate::parser::expand_variables(path, state);
                if redirects.is_empty() {
                    commands::chown(state, &expanded_owner, &expanded_path, false)?;
                } else {
                    redirection::capture_and_redirect(redirects, state, |s| {
                        commands::chown(s, &expanded_owner, &expanded_path, false)
                    })?;
                }
                Ok(ExecutionResult::Success)
            }

            #[cfg(not(unix))]
            Command::Chown { .. } => {
                anyhow::bail!("chown not supported on this platform");
            }

            // Undo/redo operations
            Command::Undo { count } => {
                commands::undo(state, *count, false)?;
                Ok(ExecutionResult::Success)
            }

            Command::Redo { count } => {
                commands::redo(state, *count, false)?;
                Ok(ExecutionResult::Success)
            }

            Command::History { count, show_proofs } => {
                commands::history(state, *count, *show_proofs)?;
                Ok(ExecutionResult::Success)
            }

            // Transactions
            Command::Begin { name } => {
                let expanded_name = crate::parser::expand_variables(name, state);
                commands::begin_transaction(state, &expanded_name)?;
                Ok(ExecutionResult::Success)
            }

            Command::Commit => {
                commands::commit_transaction(state)?;
                Ok(ExecutionResult::Success)
            }

            Command::Rollback => {
                commands::rollback_transaction(state)?;
                Ok(ExecutionResult::Success)
            }

            // Display commands
            Command::Graph => {
                commands::show_graph(state)?;
                Ok(ExecutionResult::Success)
            }

            Command::Proofs => {
                commands::show_proofs()?;
                Ok(ExecutionResult::Success)
            }

            // Exit commands
            Command::Exit | Command::Quit => Ok(ExecutionResult::Exit),

            // Navigation (built-ins but not reversible)
            Command::Ls { path, redirects } => {
                // Expand variables in path
                let expanded_path = path.as_ref().map(|p| crate::parser::expand_variables(p, state));

                if redirects.is_empty() {
                    // Direct output to terminal
                    use std::fs;

                    let target = if let Some(ref p) = expanded_path {
                        state.resolve_path(p)
                    } else {
                        state.root.clone()
                    };

                    if !target.is_dir() {
                        anyhow::bail!("Not a directory");
                    }

                    for entry in fs::read_dir(&target)? {
                        let entry = entry?;
                        let name = entry.file_name();
                        let file_type = entry.file_type()?;
                        if file_type.is_dir() {
                            use colored::Colorize;
                            println!("{}/", name.to_string_lossy().bright_blue());
                        } else {
                            println!("{}", name.to_string_lossy());
                        }
                    }
                } else {
                    // Capture and redirect output
                    redirection::capture_and_redirect(redirects, state, |s| {
                        use std::fs;

                        let target = if let Some(ref p) = expanded_path {
                            s.resolve_path(p)
                        } else {
                            s.root.clone()
                        };

                        if !target.is_dir() {
                            anyhow::bail!("Not a directory");
                        }

                        for entry in fs::read_dir(&target)? {
                            let entry = entry?;
                            let name = entry.file_name();
                            let file_type = entry.file_type()?;
                            if file_type.is_dir() {
                                // No colors when redirecting
                                println!("{}/", name.to_string_lossy());
                            } else {
                                println!("{}", name.to_string_lossy());
                            }
                        }
                        Ok(())
                    })?;
                }
                Ok(ExecutionResult::Success)
            }

            Command::Pwd { redirects } => {
                if redirects.is_empty() {
                    println!("{}", state.root.display());
                } else {
                    redirection::capture_and_redirect(redirects, state, |s| {
                        println!("{}", s.root.display());
                        Ok(())
                    })?;
                }
                Ok(ExecutionResult::Success)
            }

            Command::Cd { path } => {
                use std::path::PathBuf;

                // Expand variables in path first
                let expanded_path = path.as_ref().map(|p| crate::parser::expand_variables(p, state));

                let target = if let Some(ref p) = expanded_path {
                    if p == "-" {
                        // cd - : swap to previous directory
                        match &state.previous_dir {
                            Some(prev) => {
                                // Print the directory we're switching to (bash behavior)
                                println!("{}", prev.display());
                                prev.clone()
                            }
                            None => {
                                anyhow::bail!("cd: OLDPWD not set");
                            }
                        }
                    } else if p.starts_with('/') {
                        // Absolute path
                        PathBuf::from(p)
                    } else if p.starts_with("~/") {
                        // Home-relative path
                        let home = dirs::home_dir()
                            .ok_or_else(|| anyhow::anyhow!("Could not find home directory"))?;
                        home.join(&p[2..])
                    } else {
                        // Relative to current directory
                        state.root.join(p)
                    }
                } else {
                    // cd with no args goes to home
                    dirs::home_dir()
                        .ok_or_else(|| anyhow::anyhow!("Could not find home directory"))?
                };

                if !target.exists() {
                    anyhow::bail!("cd: {}: No such file or directory", target.display());
                }

                if !target.is_dir() {
                    anyhow::bail!("cd: {}: Not a directory", target.display());
                }

                // Store current directory as previous before changing
                state.previous_dir = Some(state.root.clone());

                // Change the shell's working directory
                std::env::set_current_dir(&target)?;

                // Update state root to track current directory
                state.root = std::fs::canonicalize(target)?;

                Ok(ExecutionResult::Success)
            }

            // Conditionals
            Command::Test { args, redirects } => {
                // Expand arguments
                let expanded_args: Vec<String> = args
                    .iter()
                    .map(|arg| crate::parser::expand_variables(arg, state))
                    .collect();

                let exit_code = if redirects.is_empty() {
                    crate::test_command::execute_test(&expanded_args, false)?
                } else {
                    let mut code = 0;
                    redirection::capture_and_redirect(redirects, state, |_s| {
                        code = crate::test_command::execute_test(&expanded_args, false)?;
                        Ok(())
                    })?;
                    code
                };

                Ok(ExecutionResult::ExternalCommand { exit_code })
            }

            Command::Bracket { args, redirects } => {
                // Expand arguments
                let expanded_args: Vec<String> = args
                    .iter()
                    .map(|arg| crate::parser::expand_variables(arg, state))
                    .collect();

                let exit_code = if redirects.is_empty() {
                    crate::test_command::execute_test(&expanded_args, true)?
                } else {
                    let mut code = 0;
                    redirection::capture_and_redirect(redirects, state, |_s| {
                        code = crate::test_command::execute_test(&expanded_args, true)?;
                        Ok(())
                    })?;
                    code
                };

                Ok(ExecutionResult::ExternalCommand { exit_code })
            }

            Command::ExtendedTest { args, redirects } => {
                // Extended test [[ ... ]] - NO word splitting, pattern matching enabled
                // Expand variables but without word splitting (key difference from regular test)
                let expanded_args: Vec<String> = args
                    .iter()
                    .map(|arg| crate::parser::expand_variables(arg, state))
                    .collect();

                let exit_code = if redirects.is_empty() {
                    crate::test_command::execute_extended_test(&expanded_args)?
                } else {
                    let mut code = 0;
                    redirection::capture_and_redirect(redirects, state, |_s| {
                        code = crate::test_command::execute_extended_test(&expanded_args)?;
                        Ok(())
                    })?;
                    code
                };

                Ok(ExecutionResult::ExternalCommand { exit_code })
            }

            // External commands (not reversible by default, but redirections are)
            Command::External {
                program,
                args,
                redirects,
                background,
            } => {
                // Expand program name (no process substitutions in program name)
                let expanded_program = crate::parser::expand_with_command_sub(program, state)?;

                // Check if the command is a shell function before external execution.
                // `if let Some(...)` performs a single map lookup; the previous
                // `is_defined()` + `.get(...).expect("TODO")` shape both panicked
                // through a fake-debt marker and duplicated the lookup.
                if let Some(func_def) = state.functions.get(&expanded_program).cloned() {
                    let expanded_args: Vec<String> = args
                        .iter()
                        .map(|a| crate::parser::expand_variables(a, state))
                        .collect();
                    return execute_function_call(&func_def, &expanded_args, state);
                }

                // Expand arguments with process substitutions
                let mut all_process_subs = Vec::new();
                let mut expanded_args = Vec::new();

                for arg in args {
                    let (expanded_arg, proc_subs) =
                        crate::parser::expand_with_process_sub(arg, state)?;
                    expanded_args.push(expanded_arg);
                    all_process_subs.extend(proc_subs);
                }

                // Execute main command
                if *background {
                    // Background execution
                    let _job_id = external::execute_external_background(
                        &expanded_program,
                        &expanded_args,
                        redirects,
                        state,
                    )
                    .unwrap_or_else(|e| {
                        eprintln!("{}: {}", expanded_program, e);
                        0 // No job created
                    });

                    // Cleanup all process substitutions
                    for proc_sub in all_process_subs {
                        if let Err(e) = proc_sub.cleanup() {
                            eprintln!("Warning: Failed to cleanup process substitution: {}", e);
                        }
                    }

                    Ok(ExecutionResult::Success)
                } else {
                    // Foreground execution
                    let exit_code = if redirects.is_empty() {
                        // No redirections - use simple path
                        external::execute_external(&expanded_program, &expanded_args)
                    } else {
                        // Has redirections - use redirection-aware execution
                        external::execute_external_with_redirects(
                            &expanded_program,
                            &expanded_args,
                            redirects,
                            state,
                        )
                    }
                    .unwrap_or_else(|e| {
                        eprintln!("{}: {}", expanded_program, e);
                        127
                    });

                    // Cleanup all process substitutions
                    for proc_sub in all_process_subs {
                        if let Err(e) = proc_sub.cleanup() {
                            eprintln!("Warning: Failed to cleanup process substitution: {}", e);
                        }
                    }

                    Ok(ExecutionResult::ExternalCommand { exit_code })
                }
            }

            // Pipeline commands (not reversible by default, but redirections are)
            Command::Pipeline { stages, redirects, background } => {
                // Expand variables and command substitutions in all pipeline stages
                let expanded_stages: Result<Vec<(String, Vec<String>)>> = stages
                    .iter()
                    .map(|(program, args)| {
                        let expanded_program = crate::parser::expand_with_command_sub(program, state)?;
                        let expanded_args: Result<Vec<String>> = args
                            .iter()
                            .map(|arg| crate::parser::expand_with_command_sub(arg, state))
                            .collect();
                        Ok((expanded_program, expanded_args?))
                    })
                    .collect();
                let expanded_stages = expanded_stages?;

                if *background && !expanded_stages.is_empty() {
                    // Background pipeline: launch first stage in background, pipe rest
                    // For now, warn and run in foreground — full background pipeline
                    // requires SIGCHLD handler and process group management for all stages
                    eprintln!("vsh: background pipelines not yet fully supported, running in foreground");
                }

                let exit_code = external::execute_pipeline(&expanded_stages, redirects, state)
                    .unwrap_or_else(|e| {
                        eprintln!("Pipeline error: {}", e);
                        127
                    });

                Ok(ExecutionResult::ExternalCommand { exit_code })
            }

            // Variable assignment (tracked for undo/redo)
            Command::Assignment { name, value } => {
                // Expand variables and command substitutions in the value
                let expanded_value = crate::parser::expand_with_command_sub(value, state)?;
                state.set_variable_tracked(name, expanded_value);
                Ok(ExecutionResult::Success)
            }

            // Array assignment
            Command::ArrayAssignment { name, elements } => {
                // Expand variables in each element
                let expanded_elements: Vec<String> = elements
                    .iter()
                    .map(|elem| crate::parser::expand_variables(elem, state))
                    .collect();
                state.set_array(name, expanded_elements);
                Ok(ExecutionResult::Success)
            }

            // Array element assignment
            Command::ArrayElementAssignment { name, index, value } => {
                // Expand variables in the value
                let expanded_value = crate::parser::expand_variables(value, state);
                state.set_array_element(name, *index, expanded_value);
                Ok(ExecutionResult::Success)
            }

            // Array append
            Command::ArrayAppend { name, elements } => {
                // Expand variables in each element
                let expanded_elements: Vec<String> = elements
                    .iter()
                    .map(|elem| crate::parser::expand_variables(elem, state))
                    .collect();
                state.append_to_array(name, expanded_elements);
                Ok(ExecutionResult::Success)
            }

            // Export command
            Command::Export { name, value } => {
                if let Some(val) = value {
                    // export VAR=value
                    // Expand variables and command substitutions in the value
                    let expanded_value = crate::parser::expand_with_command_sub(val, state)?;
                    state.set_variable(name, expanded_value);
                    state.export_variable(name);
                } else {
                    // export VAR (export existing variable)
                    if state.get_variable(name).is_some() {
                        state.export_variable(name);
                    } else {
                        anyhow::bail!("export: {}: variable not set", name);
                    }
                }
                Ok(ExecutionResult::Success)
            }

            // Job control
            Command::Jobs { long } => {
                commands::jobs(state, *long)?;
                Ok(ExecutionResult::Success)
            }

            Command::Fg { job_spec } => {
                commands::fg(state, job_spec.as_deref())?;
                Ok(ExecutionResult::Success)
            }

            Command::Bg { job_spec } => {
                commands::bg(state, job_spec.as_deref())?;
                Ok(ExecutionResult::Success)
            }

            Command::Kill { signal, job_spec } => {
                commands::kill_job(state, signal.as_deref(), job_spec)?;
                Ok(ExecutionResult::Success)
            }

            // Shell builtins

            Command::Echo { args, no_newline, interpret_escapes, redirects } => {
                let expanded_args: Vec<String> = args
                    .iter()
                    .map(|a| crate::parser::expand_variables(a, state))
                    .collect();

                let output = if *interpret_escapes {
                    expanded_args.join(" ")
                        .replace("\\n", "\n")
                        .replace("\\t", "\t")
                        .replace("\\\\", "\\")
                        .replace("\\a", "\x07")
                        .replace("\\b", "\x08")
                } else {
                    expanded_args.join(" ")
                };

                if redirects.is_empty() {
                    if *no_newline {
                        print!("{}", output);
                        std::io::Write::flush(&mut std::io::stdout()).ok();
                    } else {
                        println!("{}", output);
                    }
                } else {
                    let full_output = if *no_newline {
                        output
                    } else {
                        format!("{}\n", output)
                    };
                    redirection::capture_and_redirect(redirects, state, |_s| {
                        print!("{}", full_output);
                        Ok(())
                    })?;
                }
                Ok(ExecutionResult::Success)
            }

            Command::True => {
                Ok(ExecutionResult::ExternalCommand { exit_code: 0 })
            }

            Command::False => {
                Ok(ExecutionResult::ExternalCommand { exit_code: 1 })
            }

            Command::Read { var_name, prompt, redirects: _ } => {
                let expanded_var = crate::parser::expand_variables(var_name, state);

                if let Some(p) = prompt {
                    let expanded_prompt = crate::parser::expand_variables(p, state);
                    eprint!("{}", expanded_prompt);
                    std::io::Write::flush(&mut std::io::stderr()).ok();
                }

                let mut input = String::new();
                match std::io::stdin().read_line(&mut input) {
                    Ok(0) => {
                        // EOF
                        Ok(ExecutionResult::ExternalCommand { exit_code: 1 })
                    }
                    Ok(_) => {
                        let value = input.trim_end_matches('\n').trim_end_matches('\r');
                        state.set_variable(expanded_var, value.to_string());
                        Ok(ExecutionResult::Success)
                    }
                    Err(e) => Err(anyhow::anyhow!("read: {}", e)),
                }
            }

            Command::Source { file } => {
                let expanded_file = crate::parser::expand_variables(file, state);
                // For absolute paths, use directly; for relative, resolve against root
                let path = if expanded_file.starts_with('/') {
                    std::path::PathBuf::from(&expanded_file)
                } else {
                    state.resolve_path(&expanded_file)
                };

                let content = std::fs::read_to_string(&path)
                    .map_err(|e| anyhow::anyhow!("source: {}: {}", path.display(), e))?;

                // Strip whole-line comments first, then feed the entire
                // content to the statement splitter so multi-line `if/fi`,
                // `for/done`, etc. stay together.
                let stripped: String = content
                    .lines()
                    .map(|line| {
                        let trimmed = line.trim_start();
                        if trimmed.starts_with('#') {
                            ""
                        } else {
                            line
                        }
                    })
                    .collect::<Vec<_>>()
                    .join("\n");

                let mut last_result = ExecutionResult::Success;
                for segment in crate::parser::split_on_statement_separators(&stripped) {
                    let segment = segment.trim();
                    if segment.is_empty() || segment.starts_with('#') {
                        continue;
                    }
                    let cmd = crate::parser::parse_command(segment)?;
                    last_result = cmd.execute(state)?;
                    // Propagate Exit (shell-wide) and Return (function-scope).
                    // A `return` inside a sourced file that was itself sourced
                    // from a function must break out all the way to
                    // `execute_function_call`.
                    if matches!(
                        last_result,
                        ExecutionResult::Exit | ExecutionResult::Return { .. }
                    ) {
                        return Ok(last_result);
                    }
                }
                Ok(last_result)
            }

            Command::Set { args } => {
                if args.is_empty() {
                    // Display all variables
                    for (name, value) in state.get_all_variables() {
                        println!("{}={}", name, value);
                    }
                } else if args[0] == "--" {
                    // Set positional parameters: set -- arg1 arg2 ...
                    let params: Vec<String> = args[1..].to_vec();
                    state.set_positional_params(params);
                } else if args[0].starts_with('-') || args[0].starts_with('+') {
                    // Shell options (stub: just acknowledge)
                    // -e: exit on error, -x: trace, -u: error on unset, etc.
                    for arg in args {
                        let enable = arg.starts_with('-');
                        for ch in arg[1..].chars() {
                            match ch {
                                'e' => state.set_variable("SHOPT_E".to_string(), if enable { "1" } else { "0" }.to_string()),
                                'x' => state.set_variable("SHOPT_X".to_string(), if enable { "1" } else { "0" }.to_string()),
                                'u' => state.set_variable("SHOPT_U".to_string(), if enable { "1" } else { "0" }.to_string()),
                                _ => {}
                            }
                        }
                    }
                } else {
                    // Set positional params
                    state.set_positional_params(args.clone());
                }
                Ok(ExecutionResult::Success)
            }

            Command::Unset { name } => {
                let expanded_name = crate::parser::expand_variables(name, state);
                if expanded_name.starts_with("-f ") {
                    // unset -f: remove a function
                    let func_name = &expanded_name[3..];
                    if !state.functions.unset(func_name) {
                        eprintln!("unset: {}: not a function", func_name);
                    }
                } else {
                    state.unset_variable_tracked(&expanded_name);
                }
                Ok(ExecutionResult::Success)
            }

            Command::Eval { args } => {
                if args.is_empty() {
                    return Ok(ExecutionResult::Success);
                }
                let expanded_args: Vec<String> = args
                    .iter()
                    .map(|a| crate::parser::expand_variables(a, state))
                    .collect();
                let combined = expanded_args.join(" ");
                let cmd = crate::parser::parse_command(&combined)?;
                cmd.execute(state)
            }

            // Control structures

            Command::If { condition, then_body, elif_parts, else_body } => {
                // Execute condition and get exit code
                let cond_result = condition.execute(state)?;
                let cond_exit = match cond_result {
                    ExecutionResult::Success => 0,
                    ExecutionResult::Exit => return Ok(ExecutionResult::Exit),
                    ExecutionResult::Return { .. } => return Ok(cond_result),
                    ExecutionResult::ExternalCommand { exit_code } => exit_code,
                };

                if cond_exit == 0 {
                    // Condition succeeded — execute then body
                    return execute_block(then_body, state);
                }

                // Try elif parts
                for (elif_cond, elif_body) in elif_parts {
                    let elif_result = elif_cond.execute(state)?;
                    let elif_exit = match elif_result {
                        ExecutionResult::Success => 0,
                        ExecutionResult::Exit => return Ok(ExecutionResult::Exit),
                        ExecutionResult::Return { .. } => return Ok(elif_result),
                        ExecutionResult::ExternalCommand { exit_code } => exit_code,
                    };

                    if elif_exit == 0 {
                        return execute_block(elif_body, state);
                    }
                }

                // Execute else body if present
                if let Some(ref else_cmds) = else_body {
                    return execute_block(else_cmds, state);
                }

                // No branch matched — return last condition's exit code
                Ok(ExecutionResult::ExternalCommand { exit_code: 1 })
            }

            Command::WhileLoop { condition, body } => {
                let mut last_result = ExecutionResult::Success;
                // Safety: limit iterations to prevent infinite loops
                let max_iterations = 100_000;
                let mut iterations = 0;

                loop {
                    if iterations >= max_iterations {
                        return Err(anyhow::anyhow!("while: exceeded {} iterations (safety limit)", max_iterations));
                    }
                    iterations += 1;

                    // Check condition
                    let cond_result = condition.execute(state)?;
                    let cond_exit = match cond_result {
                        ExecutionResult::Success => 0,
                        ExecutionResult::Exit => return Ok(ExecutionResult::Exit),
                        ExecutionResult::Return { .. } => return Ok(cond_result),
                        ExecutionResult::ExternalCommand { exit_code } => exit_code,
                    };

                    if cond_exit != 0 {
                        break; // Condition failed — exit loop
                    }

                    // Execute body
                    last_result = execute_block(body, state)?;
                    if matches!(last_result, ExecutionResult::Exit | ExecutionResult::Return { .. }) {
                        return Ok(last_result);
                    }

                    // Check for SIGINT
                    if crate::signals::is_interrupt_requested() {
                        crate::signals::clear_interrupt();
                        break;
                    }
                }

                Ok(last_result)
            }

            Command::ForLoop { var, words, body } => {
                let mut last_result = ExecutionResult::Success;

                for word in words {
                    // Expand variables in the word
                    let expanded = crate::parser::expand_variables(word, state);
                    // Set loop variable
                    state.set_variable(var.clone(), expanded);

                    // Execute body
                    last_result = execute_block(body, state)?;
                    if matches!(last_result, ExecutionResult::Exit | ExecutionResult::Return { .. }) {
                        return Ok(last_result);
                    }

                    // Check for SIGINT
                    if crate::signals::is_interrupt_requested() {
                        crate::signals::clear_interrupt();
                        break;
                    }
                }

                Ok(last_result)
            }

            Command::CaseStatement { word, arms } => {
                let expanded_word = crate::parser::expand_variables(word, state);

                for arm in arms {
                    for pattern in &arm.patterns {
                        let expanded_pattern = crate::parser::expand_variables(pattern, state);
                        if case_pattern_matches(&expanded_word, &expanded_pattern) {
                            return execute_block(&arm.body, state);
                        }
                    }
                }

                // No pattern matched
                Ok(ExecutionResult::ExternalCommand { exit_code: 0 })
            }

            // Logical operators (short-circuit evaluation)
            Command::LogicalOp { operator, left, right } => {
                use crate::parser::LogicalOperator;

                // Execute left command
                let left_result = left.execute(state)?;

                // Get exit code from left command
                let left_exit_code = match left_result {
                    ExecutionResult::Success => 0,
                    ExecutionResult::Exit => return Ok(ExecutionResult::Exit),
                    ExecutionResult::Return { .. } => return Ok(left_result),
                    ExecutionResult::ExternalCommand { exit_code } => exit_code,
                };

                // Short-circuit evaluation based on operator
                match operator {
                    LogicalOperator::And => {
                        // && : execute right only if left succeeded (exit code 0)
                        if left_exit_code == 0 {
                            right.execute(state)
                        } else {
                            Ok(ExecutionResult::ExternalCommand { exit_code: left_exit_code })
                        }
                    }
                    LogicalOperator::Or => {
                        // || : execute right only if left failed (exit code != 0)
                        if left_exit_code != 0 {
                            right.execute(state)
                        } else {
                            Ok(ExecutionResult::ExternalCommand { exit_code: left_exit_code })
                        }
                    }
                }
            }

            // Wow-factor features
            Command::Explain { inner } => {
                commands::explain_command(inner, state)?;
                Ok(ExecutionResult::Success)
            }
            Command::Checkpoint { name } => {
                commands::checkpoint(state, name)?;
                Ok(ExecutionResult::Success)
            }
            Command::Restore { name } => {
                commands::restore(state, name)?;
                Ok(ExecutionResult::Success)
            }
            Command::Checkpoints => {
                commands::list_checkpoints(state)?;
                Ok(ExecutionResult::Success)
            }
            Command::Diff { target_op } => {
                commands::diff_state(state, *target_op)?;
                Ok(ExecutionResult::Success)
            }
            Command::Replay { start, end } => {
                commands::replay(state, *start, *end)?;
                Ok(ExecutionResult::Success)
            }

            // Shell function definition
            Command::FunctionDef { name, body, raw_body } => {
                use crate::functions::{FunctionDef as FuncDef, SourceLocation};
                let def = FuncDef {
                    name: name.clone(),
                    body: body.clone(),
                    raw_body: raw_body.clone(),
                    source_location: SourceLocation {
                        source: "stdin".to_string(),
                        line: 0,
                    },
                };
                state.functions.define(def);
                Ok(ExecutionResult::Success)
            }

            // Return from function
            Command::Return { code } => {
                if state.functions.call_depth() == 0 {
                    anyhow::bail!("return: can only return from a function");
                }
                let exit_code = code.unwrap_or(state.last_exit_code);
                state.last_exit_code = exit_code;
                // Emit the sentinel Return variant so enclosing control
                // structures short-circuit up to the function boundary.
                Ok(ExecutionResult::Return { exit_code })
            }

            // Local variable declaration
            Command::Local { assignments } => {
                if state.functions.call_depth() == 0 {
                    anyhow::bail!("local: can only be used in a function");
                }
                for (name, value) in assignments {
                    let expanded_name = crate::parser::expand_variables(name, state);
                    let prev_value = state.get_variable(&expanded_name).map(|s| s.to_string());
                    state.functions.declare_local(&expanded_name, prev_value);
                    if let Some(val) = value {
                        let expanded_val = crate::parser::expand_variables(val, state);
                        state.set_variable(expanded_name, expanded_val);
                    }
                    // If no value, the variable is declared local but keeps current value
                    // (or empty string if unset, per POSIX)
                }
                Ok(ExecutionResult::Success)
            }

            // Trap builtin
            Command::Trap { action, signals } => {
                use crate::posix_builtins::TrapSignal;
                if action.is_none() && signals.is_empty() {
                    // List all traps
                    for (sig, action) in state.traps.list() {
                        println!("trap -- '{}' {}", action, sig.name());
                    }
                } else if let Some(action) = action {
                    for sig_name in signals {
                        let expanded = crate::parser::expand_variables(sig_name, state);
                        if let Some(sig) = TrapSignal::from_str(&expanded) {
                            state.traps.set(sig, &action);
                        } else {
                            eprintln!("trap: {}: invalid signal specification", expanded);
                        }
                    }
                }
                Ok(ExecutionResult::Success)
            }

            // Alias builtin
            Command::Alias { definitions } => {
                if definitions.is_empty() {
                    // List all aliases
                    for (name, value) in state.aliases.list() {
                        println!("alias {}='{}'", name, value);
                    }
                } else {
                    for (name, value) in definitions {
                        let expanded_value = crate::parser::expand_variables(value, state);
                        state.aliases.set(name, &expanded_value);
                    }
                }
                Ok(ExecutionResult::Success)
            }

            // Unalias builtin
            Command::Unalias { names, all } => {
                if *all {
                    // unalias -a: remove all aliases (create a new empty table)
                    state.aliases = crate::posix_builtins::AliasTable::new();
                } else {
                    for name in names {
                        if !state.aliases.unset(name) {
                            eprintln!("unalias: {}: not found", name);
                        }
                    }
                }
                Ok(ExecutionResult::Success)
            }
        }
    }

    fn is_reversible(&self) -> bool {
        matches!(
            self,
            Command::Mkdir { .. }
                | Command::Rmdir { .. }
                | Command::Touch { .. }
                | Command::Rm { .. }
                | Command::Cp { .. }
                | Command::Mv { .. }
                | Command::Ln { .. }
                | Command::Chmod { .. }
                | Command::Chown { .. }
        )
    }

    fn proof_reference(&self) -> Option<ProofReference> {
        use crate::proof_refs::{
            MKDIR_RMDIR_REVERSIBLE, CREATE_DELETE_REVERSIBLE,
            COPY_FILE_REVERSIBLE, MOVE_REVERSIBLE, SYMLINK_UNLINK_REVERSIBLE,
            CHMOD_REVERSIBLE, CHOWN_REVERSIBLE,
        };

        match self {
            Command::Mkdir { .. } | Command::Rmdir { .. } => {
                Some(MKDIR_RMDIR_REVERSIBLE)
            }
            Command::Touch { .. } | Command::Rm { .. } => {
                Some(CREATE_DELETE_REVERSIBLE)
            }
            Command::Cp { .. } => Some(COPY_FILE_REVERSIBLE),
            Command::Mv { .. } => Some(MOVE_REVERSIBLE),
            Command::Ln { .. } => Some(SYMLINK_UNLINK_REVERSIBLE),
            Command::Chmod { .. } => Some(CHMOD_REVERSIBLE),
            Command::Chown { .. } => Some(CHOWN_REVERSIBLE),
            _ => None,
        }
    }

    fn description(&self) -> String {
        match self {
            Command::Mkdir { path, .. } => format!("mkdir {}", path),
            Command::Rmdir { path, .. } => format!("rmdir {}", path),
            Command::Touch { path, .. } => format!("touch {}", path),
            Command::Rm { path, .. } => format!("rm {}", path),
            Command::Cp { src, dst, .. } => format!("cp {} {}", src, dst),
            Command::Mv { src, dst, .. } => format!("mv {} {}", src, dst),
            Command::Ln { target, link, .. } => format!("ln -s {} {}", target, link),
            Command::Chmod { mode, path, .. } => format!("chmod {} {}", mode, path),
            Command::Chown { owner, path, .. } => format!("chown {} {}", owner, path),
            Command::Undo { count } => format!("undo {}", count),
            Command::Redo { count } => format!("redo {}", count),
            Command::History { count, show_proofs } => {
                if *show_proofs {
                    format!("history {} --proofs", count)
                } else {
                    format!("history {}", count)
                }
            }
            Command::Exit => "exit".to_string(),
            Command::Quit => "quit".to_string(),
            Command::Begin { name } => format!("begin {}", name),
            Command::Commit => "commit".to_string(),
            Command::Rollback => "rollback".to_string(),
            Command::Graph => "graph".to_string(),
            Command::Proofs => "proofs".to_string(),
            Command::Ls { path, .. } => {
                if let Some(p) = path {
                    format!("ls {}", p)
                } else {
                    "ls".to_string()
                }
            }
            Command::Pwd { .. } => "pwd".to_string(),
            Command::Cd { path } => {
                if let Some(p) = path {
                    format!("cd {}", p)
                } else {
                    "cd".to_string()
                }
            }
            Command::Test { args, .. } => {
                if args.is_empty() {
                    "test".to_string()
                } else {
                    format!("test {}", args.join(" "))
                }
            }
            Command::Bracket { args, .. } => {
                if args.is_empty() {
                    "[ ]".to_string()
                } else {
                    format!("[ {} ]", args.join(" "))
                }
            }
            Command::ExtendedTest { args, .. } => {
                if args.is_empty() {
                    "[[ ]]".to_string()
                } else {
                    format!("[[ {} ]]", args.join(" "))
                }
            }
            Command::External { program, args, .. } => {
                if args.is_empty() {
                    program.clone()
                } else {
                    format!("{} {}", program, args.join(" "))
                }
            }
            Command::Pipeline { stages, .. } => {
                let stage_desc: Vec<_> = stages
                    .iter()
                    .map(|(prog, args)| {
                        if args.is_empty() {
                            prog.clone()
                        } else {
                            format!("{} {}", prog, args.join(" "))
                        }
                    })
                    .collect();
                stage_desc.join(" | ")
            }

            Command::Assignment { name, value } => {
                format!("{}={}", name, value)
            }

            Command::ArrayAssignment { name, elements } => {
                format!("{}=({})", name, elements.join(" "))
            }

            Command::ArrayElementAssignment { name, index, value } => {
                format!("{}[{}]={}", name, index, value)
            }

            Command::ArrayAppend { name, elements } => {
                format!("{}+=({})", name, elements.join(" "))
            }

            Command::Export { name, value } => {
                if let Some(val) = value {
                    format!("export {}={}", name, val)
                } else {
                    format!("export {}", name)
                }
            }

            Command::Jobs { long } => {
                if *long {
                    "jobs -l".to_string()
                } else {
                    "jobs".to_string()
                }
            }

            Command::Fg { job_spec } => {
                if let Some(spec) = job_spec {
                    format!("fg {}", spec)
                } else {
                    "fg".to_string()
                }
            }

            Command::Bg { job_spec } => {
                if let Some(spec) = job_spec {
                    format!("bg {}", spec)
                } else {
                    "bg".to_string()
                }
            }

            Command::Kill { signal, job_spec } => {
                if let Some(sig) = signal {
                    format!("kill {} {}", sig, job_spec)
                } else {
                    format!("kill {}", job_spec)
                }
            }

            Command::LogicalOp { operator, left, right } => {
                use crate::parser::LogicalOperator;
                let op_str = match operator {
                    LogicalOperator::And => "&&",
                    LogicalOperator::Or => "||",
                };
                format!("{} {} {}", left.description(), op_str, right.description())
            }

            Command::Echo { args, .. } => format!("echo {}", args.join(" ")),
            Command::True => "true".to_string(),
            Command::False => "false".to_string(),
            Command::Read { var_name, .. } => format!("read {}", var_name),
            Command::Source { file } => format!("source {}", file),
            Command::Set { args } => format!("set {}", args.join(" ")),
            Command::Unset { name } => format!("unset {}", name),
            Command::Eval { args } => format!("eval {}", args.join(" ")),

            Command::If { condition, .. } => {
                format!("if {} then ...", condition.description())
            }

            Command::WhileLoop { condition, .. } => {
                format!("while {} do ...", condition.description())
            }

            Command::ForLoop { var, words, .. } => {
                format!("for {} in {} do ...", var, words.join(" "))
            }

            Command::CaseStatement { word, .. } => {
                format!("case {} in ...", word)
            }

            Command::FunctionDef { name, .. } => format!("{}() {{ ... }}", name),
            Command::Return { code } => match code {
                Some(c) => format!("return {}", c),
                None => "return".to_string(),
            },
            Command::Local { assignments } => {
                let vars: Vec<String> = assignments
                    .iter()
                    .map(|(n, v)| match v {
                        Some(val) => format!("{}={}", n, val),
                        None => n.clone(),
                    })
                    .collect();
                format!("local {}", vars.join(" "))
            }
            Command::Trap { action, signals } => {
                match action {
                    Some(a) => format!("trap '{}' {}", a, signals.join(" ")),
                    None => "trap".to_string(),
                }
            }
            Command::Alias { definitions } => {
                if definitions.is_empty() {
                    "alias".to_string()
                } else {
                    let defs: Vec<String> = definitions
                        .iter()
                        .map(|(n, v)| format!("{}='{}'", n, v))
                        .collect();
                    format!("alias {}", defs.join(" "))
                }
            }
            Command::Unalias { names, all } => {
                if *all {
                    "unalias -a".to_string()
                } else {
                    format!("unalias {}", names.join(" "))
                }
            }
            Command::Explain { inner } => format!("explain {}", inner.description()),
            Command::Checkpoint { name } => format!("checkpoint {}", name),
            Command::Restore { name } => format!("restore {}", name),
            Command::Checkpoints => "checkpoints".to_string(),
            Command::Diff { target_op } => format!("diff {}", target_op),
            Command::Replay { start, end } => format!("replay {}..{}", start, end),
        }
    }
}

/// Execute a shell function call with arguments.
///
/// Steps:
/// 1. Save current positional parameters
/// 2. Set new positional parameters from function arguments
/// 3. Push a function frame for local variable scoping
/// 4. Parse the raw function body, splitting on semicolons/newlines with
///    control-structure awareness (so `if/fi`, `for/done`, `while/done`,
///    and `case/esac` work inside a function body)
/// 5. Execute each segment; stop early on `return` / `exit`
/// 6. Restore positional parameters and local variables
fn execute_function_call(
    func_def: &crate::functions::FunctionDef,
    args: &[String],
    state: &mut ShellState,
) -> Result<ExecutionResult> {
    // Save current positional parameters
    let saved_params = state.positional_params.clone();

    // Set new positional parameters from function arguments
    state.set_positional_params(args.to_vec());

    // Push a function frame
    state.functions.push_frame(saved_params.clone());

    // Execute function body. We prefer the raw body string (which preserves
    // control-structure integrity) and fall back to the pre-split segments
    // for older in-memory definitions.
    let segments: Vec<String> = if !func_def.raw_body.is_empty() {
        // Treat each line as a script line, then split that line on top-level
        // semicolons (inside quotes / control structures those are preserved).
        func_def
            .raw_body
            .lines()
            .flat_map(|line| {
                crate::parser::split_on_semicolons(line)
                    .into_iter()
                    .map(|s| s.to_string())
                    .collect::<Vec<_>>()
            })
            .collect()
    } else {
        func_def.body.clone()
    };

    let mut last_result = ExecutionResult::Success;
    for cmd_str in &segments {
        let cmd_str = cmd_str.trim();
        if cmd_str.is_empty() || cmd_str.starts_with('#') {
            continue;
        }

        match crate::parser::parse_command(cmd_str) {
            Ok(cmd) => {
                last_result = cmd.execute(state)?;
                match &last_result {
                    ExecutionResult::Exit => break,
                    // `return` (possibly from deep inside nested control
                    // structures) — stop executing the body and convert the
                    // sentinel into a regular exit-code result so the caller
                    // sees `fn() returned N`, not the internal Return marker.
                    ExecutionResult::Return { exit_code } => {
                        let code = *exit_code;
                        state.last_exit_code = code;
                        last_result = ExecutionResult::ExternalCommand { exit_code: code };
                        break;
                    }
                    ExecutionResult::ExternalCommand { exit_code } => {
                        state.last_exit_code = *exit_code;
                    }
                    ExecutionResult::Success => {
                        state.last_exit_code = 0;
                    }
                }
            }
            Err(e) => {
                eprintln!("{}: {}", func_def.name, e);
                state.last_exit_code = 1;
            }
        }
    }

    // Pop function frame and restore local variables
    if let Some(frame) = state.functions.pop_frame() {
        // Restore positional parameters
        state.set_positional_params(frame.saved_params);

        // Restore local variables to their previous values
        for (var_name, prev_value) in &frame.saved_vars {
            match prev_value {
                Some(val) => state.set_variable(var_name.clone(), val.clone()),
                None => { state.unset_variable(var_name); }
            }
        }
    }

    Ok(last_result)
}

/// Execute a block of commands in sequence, returning the result of the last command.
///
/// Short-circuits on `Exit` (shell-wide) and `Return` (function-scope) so the
/// signal propagates up through nested control structures.
fn execute_block(commands: &[Command], state: &mut ShellState) -> Result<ExecutionResult> {
    let mut last_result = ExecutionResult::Success;
    for cmd in commands {
        last_result = cmd.execute(state)?;
        match &last_result {
            ExecutionResult::Exit => return Ok(ExecutionResult::Exit),
            ExecutionResult::Return { exit_code } => {
                state.last_exit_code = *exit_code;
                return Ok(last_result);
            }
            ExecutionResult::ExternalCommand { exit_code } => {
                state.last_exit_code = *exit_code;
            }
            ExecutionResult::Success => {
                state.last_exit_code = 0;
            }
        }
    }
    Ok(last_result)
}

/// Match a word against a case pattern (supports glob-style wildcards)
fn case_pattern_matches(word: &str, pattern: &str) -> bool {
    if pattern == "*" {
        return true; // Match-all
    }

    // Use glob-style matching
    // Simple implementation: * matches any sequence, ? matches one char
    glob_match(pattern, word)
}

/// Simple glob pattern matching for case statements
fn glob_match(pattern: &str, text: &str) -> bool {
    let mut p = pattern.chars().peekable();
    let mut t = text.chars().peekable();

    glob_match_inner(&mut pattern.chars().collect::<Vec<_>>(), &mut text.chars().collect::<Vec<_>>(), 0, 0)
}

fn glob_match_inner(pattern: &[char], text: &[char], pi: usize, ti: usize) -> bool {
    if pi == pattern.len() && ti == text.len() {
        return true;
    }
    if pi == pattern.len() {
        return false;
    }

    match pattern[pi] {
        '*' => {
            // Try matching 0 or more characters
            for skip in 0..=(text.len() - ti) {
                if glob_match_inner(pattern, text, pi + 1, ti + skip) {
                    return true;
                }
            }
            false
        }
        '?' => {
            if ti < text.len() {
                glob_match_inner(pattern, text, pi + 1, ti + 1)
            } else {
                false
            }
        }
        ch => {
            if ti < text.len() && text[ti] == ch {
                glob_match_inner(pattern, text, pi + 1, ti + 1)
            } else {
                false
            }
        }
    }
}
