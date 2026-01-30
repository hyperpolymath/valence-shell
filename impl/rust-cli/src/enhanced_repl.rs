// SPDX-License-Identifier: PLMP-1.0-or-later
//! Enhanced REPL with reedline
//!
//! Features:
//! - Tab completion for commands and paths
//! - Syntax highlighting
//! - History search (Ctrl+R)
//! - Multi-line editing
//! - Better prompts showing undo stack

use anyhow::Result;
use nu_ansi_term::{Color, Style};
use reedline::{
    default_emacs_keybindings, ColumnarMenu, Completer, DefaultHinter, DefaultValidator,
    Emacs, FileBackedHistory, HistoryItem, KeyCode, KeyModifiers, MenuBuilder, Prompt,
    PromptEditMode, PromptHistorySearch, PromptHistorySearchStatus, Reedline, ReedlineEvent,
    ReedlineMenu, Signal, Span, StyledText, Suggestion,
};
use std::borrow::Cow;
use std::path::PathBuf;

use crate::executable::{ExecutableCommand, ExecutionResult};
use crate::highlighter::VshHighlighter;
use crate::parser;
use crate::signals;
use crate::state::ShellState;

/// Shell commands for completion
const BUILTIN_COMMANDS: &[&str] = &[
    "cd", "pwd", "exit", "mkdir", "rmdir", "touch", "rm", "cp", "mv", "cat", "echo", "ls",
    "undo", "redo", "history", "begin", "commit", "rollback", "help",
];

/// Custom completer for VSH
struct VshCompleter;

impl Completer for VshCompleter {
    fn complete(&mut self, line: &str, pos: usize) -> Vec<Suggestion> {
        let words: Vec<&str> = line[..pos].split_whitespace().collect();

        if words.is_empty() || (words.len() == 1 && !line.ends_with(' ')) {
            // Complete command
            let prefix = words.first().unwrap_or(&"");
            BUILTIN_COMMANDS
                .iter()
                .filter(|cmd| cmd.starts_with(prefix))
                .map(|cmd| Suggestion {
                    value: cmd.to_string(),
                    description: None,
                    style: None,
                    extra: None,
                    span: Span::new(pos.saturating_sub(prefix.len()), pos),
                    append_whitespace: true,
                })
                .collect()
        } else {
            // Complete file paths
            let last_word = words.last().unwrap_or(&"");
            complete_path(last_word, pos)
        }
    }
}

fn complete_path(prefix: &str, pos: usize) -> Vec<Suggestion> {
    let path = if prefix.is_empty() {
        PathBuf::from(".")
    } else if prefix.ends_with('/') {
        PathBuf::from(prefix)
    } else {
        PathBuf::from(prefix).parent().unwrap_or_else(|| std::path::Path::new(".")).to_path_buf()
    };

    let prefix_path = PathBuf::from(prefix);
    let filename_prefix = if prefix.ends_with('/') {
        ""
    } else {
        prefix_path
            .file_name()
            .and_then(|s| s.to_str())
            .unwrap_or("")
    };

    let Ok(entries) = std::fs::read_dir(&path) else {
        return vec![];
    };

    entries
        .filter_map(|entry| {
            let entry = entry.ok()?;
            let name = entry.file_name().to_string_lossy().into_owned();

            if !name.starts_with(filename_prefix) {
                return None;
            }

            let is_dir = entry.file_type().ok()?.is_dir();
            let value = if is_dir {
                format!("{}/", name)
            } else {
                name.clone()
            };

            Some(Suggestion {
                value,
                description: if is_dir {
                    Some("directory".to_string())
                } else {
                    Some("file".to_string())
                },
                style: if is_dir {
                    Some(Style::new().fg(Color::Blue).bold())
                } else {
                    None
                },
                extra: None,
                span: Span::new(pos.saturating_sub(filename_prefix.len()), pos),
                append_whitespace: !is_dir,
            })
        })
        .take(50)
        .collect()
}

/// Custom prompt for VSH
struct VshPrompt {
    txn_name: Option<String>,
    undo_count: usize,
    cwd: String,
}

impl Prompt for VshPrompt {
    fn render_prompt_left(&self) -> Cow<str> {
        Cow::Borrowed("")
    }

    fn render_prompt_right(&self) -> Cow<str> {
        if let Some(ref txn) = self.txn_name {
            Cow::Owned(format!("[txn:{}]", txn))
        } else {
            Cow::Borrowed("")
        }
    }

    fn render_prompt_indicator(&self, _edit_mode: PromptEditMode) -> Cow<str> {
        let undo_indicator = if self.undo_count > 0 {
            format!("({}) ", self.undo_count)
        } else {
            String::new()
        };

        let txn_indicator = if self.txn_name.is_some() {
            Color::Cyan.paint("txn> ")
        } else {
            Color::Green.paint("vsh> ")
        };

        Cow::Owned(format!("{}{}", undo_indicator, txn_indicator))
    }

    fn render_prompt_multiline_indicator(&self) -> Cow<str> {
        Cow::Borrowed("...> ")
    }

    fn render_prompt_history_search_indicator(
        &self,
        history_search: PromptHistorySearch,
    ) -> Cow<str> {
        let prefix = match history_search.status {
            PromptHistorySearchStatus::Passing => "",
            PromptHistorySearchStatus::Failing => "failing ",
        };

        Cow::Owned(format!(
            "({}reverse-search: {}) ",
            prefix, history_search.term
        ))
    }
}

/// Run enhanced REPL
pub fn run(state: &mut ShellState) -> Result<()> {
    // Set up history file
    let history_file = dirs::home_dir()
        .unwrap_or_else(|| PathBuf::from("/tmp"))
        .join(".vsh_history");

    let history = Box::new(
        FileBackedHistory::with_file(1000, history_file)
            .expect("Failed to initialize history"),
    );

    // Set up completion menu
    let completion_menu = Box::new(ColumnarMenu::default().with_name("completion_menu"));

    // Set up keybindings
    let mut keybindings = default_emacs_keybindings();
    keybindings.add_binding(
        KeyModifiers::NONE,
        KeyCode::Tab,
        ReedlineEvent::UntilFound(vec![
            ReedlineEvent::Menu("completion_menu".to_string()),
            ReedlineEvent::MenuNext,
        ]),
    );

    let edit_mode = Box::new(Emacs::new(keybindings));

    // Create reedline instance
    let mut line_editor = Reedline::create()
        .with_history(history)
        .with_completer(Box::new(VshCompleter))
        .with_highlighter(Box::new(VshHighlighter::new()))
        .with_hinter(Box::new(
            DefaultHinter::default().with_style(Style::new().fg(Color::DarkGray)),
        ))
        .with_validator(Box::new(DefaultValidator))
        .with_edit_mode(edit_mode)
        .with_menu(ReedlineMenu::EngineCompleter(completion_menu));

    // Install SIGINT handler
    ctrlc::set_handler(move || {
        signals::request_interrupt();
    })
    .expect("Error setting Ctrl-C handler");

    loop {
        // Build prompt
        let txn_name = state
            .active_transaction
            .as_ref()
            .map(|t| t.name.clone());
        let undo_count = state.history.iter().filter(|o| !o.undone).count();
        let cwd = std::env::current_dir()
            .ok()
            .and_then(|p| p.to_str().map(|s| s.to_string()))
            .unwrap_or_else(|| "/".to_string());

        let prompt = VshPrompt {
            txn_name,
            undo_count,
            cwd,
        };

        // Read input
        let sig = line_editor.read_line(&prompt);

        match sig {
            Ok(Signal::Success(input)) => {
                let input = input.trim();
                if input.is_empty() || input.starts_with('#') {
                    continue;
                }

                // Execute command
                match execute_line(state, input) {
                    Ok(should_exit) => {
                        if should_exit {
                            break;
                        }
                    }
                    Err(e) => {
                        eprintln!("{} {}", Color::Red.paint("Error:"), e);
                    }
                }
            }
            Ok(Signal::CtrlD) => {
                println!("{}", Color::Blue.paint("\nGoodbye!"));
                break;
            }
            Ok(Signal::CtrlC) => {
                // Clear line on Ctrl+C
                continue;
            }
            Err(err) => {
                eprintln!("Error reading input: {}", err);
                break;
            }
        }
    }

    Ok(())
}

fn execute_line(state: &mut ShellState, input: &str) -> Result<bool> {
    // Check for exit
    if input == "exit" || input == "quit" {
        return Ok(true);
    }

    // Parse command
    let cmd = parser::parse_command(input)?;

    // Execute command
    let result = cmd.execute(state)?;

    // Handle execution result
    match result {
        ExecutionResult::Exit => Ok(true),
        ExecutionResult::ExternalCommand { exit_code } => {
            state.last_exit_code = exit_code;
            Ok(false)
        }
        ExecutionResult::Success => Ok(false),
    }
}
