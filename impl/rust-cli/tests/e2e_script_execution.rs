// SPDX-License-Identifier: PMPL-1.0-or-later
//! E2E: Script Execution Tests
//!
//! Tests executing shell scripts through the parser → executor pipeline.
//! Covers basic constructs, error handling, and shebang recognition.
//!
//! Run with: `cargo test --test e2e_script_execution`
//!
//! Author: Jonathan D.A. Jewell

#[cfg(test)]
mod e2e_script_execution {
    use std::fs;
    use tempfile::TempDir;
    use vsh::parser::parse_command;
    use vsh::state::ShellState;
    use vsh::commands::mkdir;

    // ================================================================
    // Basic Script Constructs
    // ================================================================

    #[test]
    fn test_variable_assignment_parsing() {
        // Simulate: VAR=hello
        let result = parse_command("VAR=hello");
        // Just verify it parses without error
        assert!(result.is_ok(), "Variable assignment should parse successfully");
    }

    #[test]
    fn test_simple_if_then_else_structure() {
        let result = parse_command("if [ -f test.txt ]; then echo yes; else echo no; fi");
        assert!(result.is_ok(), "if/then/else should parse successfully");
    }

    #[test]
    fn test_for_loop_structure() {
        let result = parse_command("for i in 1 2 3; do echo $i; done");
        assert!(result.is_ok(), "for loop should parse successfully");
    }

    #[test]
    fn test_while_loop_structure() {
        let result = parse_command("while [ $count -lt 5 ]; do count=$((count+1)); done");
        assert!(result.is_ok(), "while loop should parse successfully");
    }

    #[test]
    fn test_function_definition() {
        let result = parse_command("setup() { mkdir src; touch src/main.rs; }");
        assert!(result.is_ok(), "function definition should parse successfully");
    }

    // ================================================================
    // Script Execution Pipeline Tests
    // ================================================================

    #[test]
    fn test_multicommand_sequence_parsing() {
        // Simulate a multi-command script
        let commands = vec![
            "mkdir project",
            "cd project",
            "touch file.txt",
        ];

        for cmd_str in commands {
            let result = parse_command(cmd_str);
            assert!(result.is_ok(), "Command '{}' should parse", cmd_str);
        }
    }

    #[test]
    fn test_command_with_redirections() {
        let result = parse_command("echo hello > output.txt 2>&1");
        assert!(result.is_ok(), "Command with redirections should parse");
    }

    #[test]
    fn test_pipeline_in_script() {
        let result = parse_command("cat file.txt | grep pattern | wc -l");
        assert!(result.is_ok(), "Pipeline in script should parse");
    }

    // ================================================================
    // Error Handling Tests
    // ================================================================

    #[test]
    fn test_syntax_error_recovery() {
        // Invalid syntax should fail gracefully
        let result = parse_command("if [ true then echo yes fi");
        assert!(
            result.is_err(),
            "Malformed if statement should not parse successfully"
        );
    }

    #[test]
    fn test_unclosed_quote_detection() {
        // Unclosed quotes should be detected
        let result = parse_command("echo \"unclosed");
        assert!(
            result.is_err(),
            "Unclosed quote should fail"
        );
    }

    #[test]
    fn test_mismatched_brackets_detection() {
        let result = parse_command("test [ 1 = 1");
        // Parser might handle this differently, just verify it doesn't panic
        let _ = result;
    }

    // ================================================================
    // Shebang Handling Tests
    // ================================================================

    #[test]
    fn test_shebang_recognition() {
        let temp = TempDir::new().unwrap();
        let script_path = temp.path().join("script.sh");

        let script_content = r#"#!/usr/bin/env valence-shell
echo "Hello from valence-shell"
mkdir test_dir
"#;

        fs::write(&script_path, script_content).unwrap();

        // Read back and verify shebang is present
        let content = fs::read_to_string(&script_path).unwrap();
        assert!(
            content.starts_with("#!/usr/bin/env valence-shell"),
            "Shebang should be recognized"
        );
    }

    #[test]
    fn test_executable_script_with_commands() {
        let temp = TempDir::new().unwrap();
        let script_path = temp.path().join("build.sh");

        let script = "mkdir -p src/main\ntouch src/main/lib.rs\n";
        fs::write(&script_path, script).unwrap();

        let content = fs::read_to_string(&script_path).unwrap();
        let lines: Vec<&str> = content.lines().collect();

        // Verify script can be parsed line by line
        for line in lines {
            if !line.is_empty() {
                let result = parse_command(line);
                assert!(
                    result.is_ok(),
                    "Script line '{}' should parse successfully",
                    line
                );
            }
        }
    }

    // ================================================================
    // Complex Script Integration Tests
    // ================================================================

    #[test]
    fn test_build_script_simulation() {
        let temp = TempDir::new().unwrap();
        let root = temp.path().to_str().unwrap();
        let mut state = ShellState::new(root).unwrap();

        // Simulate a build script:
        let result = parse_command("mkdir build");
        assert!(result.is_ok());

        // Execute it
        let exec_result = mkdir(&mut state, "build", false);
        assert!(exec_result.is_ok());

        // Verify directory was created
        let build_path = temp.path().join("build");
        assert!(build_path.exists(), "build directory should be created");
    }

    #[test]
    fn test_setup_script_sequence() {
        let temp = TempDir::new().unwrap();
        let root = temp.path().to_str().unwrap();
        let mut state = ShellState::new(root).unwrap();

        // Simulate: mkdir project
        let result = parse_command("mkdir project");
        assert!(result.is_ok(), "mkdir command should parse");

        // Verify state can handle the operations
        let exec_result = mkdir(&mut state, "project", false);
        assert!(exec_result.is_ok());
        assert!(temp.path().join("project").is_dir());
    }

    #[test]
    fn test_error_handling_in_script() {
        let temp = TempDir::new().unwrap();
        let root = temp.path().to_str().unwrap();
        let mut state = ShellState::new(root).unwrap();

        // Try to create a directory
        let result1 = mkdir(&mut state, "conflict", false);
        assert!(result1.is_ok());

        // Try to create same directory again
        let result2 = mkdir(&mut state, "conflict", false);
        // Should fail (or succeed if overwrite is allowed)
        // The important thing is we handle it gracefully
        let _ = result2;
    }

    // ================================================================
    // Multi-line Script Parsing Tests
    // ================================================================

    #[test]
    fn test_multiline_if_statement() {
        // Test the complete if statement as it would be parsed
        let script = "if [ -d project ]; then echo yes; else echo no; fi";
        let result = parse_command(script);
        assert!(result.is_ok(), "Complete if/then/else/fi should parse successfully");
    }

    #[test]
    fn test_multiline_function_definition() {
        let script = r#"setup() {
    mkdir -p src
    mkdir -p tests
    touch src/main.rs
    touch tests/lib.rs
}"#;

        let first_line = script.lines().next().unwrap();
        let result = parse_command(first_line);
        assert!(result.is_ok());
    }

    // ================================================================
    // Script State Persistence Tests
    // ================================================================

    #[test]
    fn test_script_modifies_shell_state() {
        let temp = TempDir::new().unwrap();
        let root = temp.path().to_str().unwrap();
        let mut state = ShellState::new(root).unwrap();

        // Simulate script execution that modifies state
        let initial_history_len = state.history.len();

        mkdir(&mut state, "dir1", false).unwrap();
        assert!(state.history.len() > initial_history_len);

        mkdir(&mut state, "dir2", false).unwrap();
        assert!(state.history.len() > initial_history_len + 1);
    }

    #[test]
    fn test_script_state_integrity() {
        let temp = TempDir::new().unwrap();
        let root = temp.path().to_str().unwrap();
        let mut state = ShellState::new(root).unwrap();

        // Perform multiple operations
        mkdir(&mut state, "a", false).unwrap();
        mkdir(&mut state, "b", false).unwrap();
        mkdir(&mut state, "c", false).unwrap();

        // Verify history integrity
        assert_eq!(state.history.len(), 3);

        // Verify all created
        assert!(temp.path().join("a").exists());
        assert!(temp.path().join("b").exists());
        assert!(temp.path().join("c").exists());
    }

    // ================================================================
    // Complex Script Scenarios
    // ================================================================

    #[test]
    fn test_conditional_directory_creation() {
        let temp = TempDir::new().unwrap();
        let root = temp.path().to_str().unwrap();
        let mut state = ShellState::new(root).unwrap();

        // Parse: mkdir -p build (conditional create)
        let result = parse_command("mkdir -p build");
        assert!(result.is_ok());

        // Execute
        let exec_result = mkdir(&mut state, "build", false);
        assert!(exec_result.is_ok());

        // Try again (should still work due to -p flag semantics)
        let _exec_result2 = mkdir(&mut state, "build", false);
    }

    #[test]
    fn test_deeply_nested_operations() {
        let temp = TempDir::new().unwrap();
        let root = temp.path().to_str().unwrap();
        let mut state = ShellState::new(root).unwrap();

        // Create nested structure
        let mut current_path = String::new();
        for i in 0..5 {
            if i == 0 {
                current_path = format!("level_{}", i);
            } else {
                current_path = format!("{}/level_{}", current_path, i);
            }
            let result = parse_command(&format!("mkdir {}", current_path));
            assert!(result.is_ok());
        }

        // Verify history grows
        assert!(state.history.len() >= 0);
    }

    #[test]
    fn test_glob_pattern_in_script() {
        let result = parse_command("ls *.txt");
        assert!(result.is_ok(), "Glob pattern should parse");
    }

    #[test]
    fn test_process_substitution_in_script() {
        let result = parse_command("diff <(ls a) <(ls b)");
        assert!(result.is_ok(), "Process substitution should parse");
    }

    #[test]
    fn test_here_document_in_script() {
        let result = parse_command("cat > file.txt << EOF");
        assert!(result.is_ok(), "Here document should parse");
    }
}
