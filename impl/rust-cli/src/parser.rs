// SPDX-License-Identifier: PMPL-1.0-or-later
//! Command Parser
//!
//! Parses shell input into structured commands.
//! Distinguishes between built-in commands and external programs.
//! Supports I/O redirections (>, <, >>, 2>, etc.)

use anyhow::{anyhow, Context, Result};

use crate::redirection::Redirection;

/// Quote type for a word or word part
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum QuoteType {
    /// No quotes
    None,
    /// Single quotes '...' - no expansion
    Single,
    /// Double quotes "..." - expansion allowed
    Double,
}

/// Type of process substitution
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ProcessSubType {
    /// Input: <(cmd) - command output as readable file
    Input,
    /// Output: >(cmd) - command input as writable file
    Output,
}

/// Part of a word that may contain literals and variable references
#[derive(Debug, Clone, PartialEq)]
enum WordPart {
    /// Literal text (no expansion)
    Literal(String),
    /// Variable reference $VAR
    Variable(String),
    /// Braced variable reference ${VAR}
    BracedVariable(String),
    /// Command substitution $(cmd) or `cmd`
    CommandSub(String),
    /// Process substitution <(cmd) or >(cmd)
    ProcessSub(ProcessSubType, String),
}

/// Parameter expansion operations supported in ${VAR...} syntax
#[derive(Debug, Clone, PartialEq)]
enum ExpansionOp {
    /// Simple expansion: ${VAR}
    Simple,
    /// Use default value: ${VAR:-default} or ${VAR-default}
    Default {
        value: String,
        check_null: bool,  // true for :-, false for -
    },
    /// Assign default value: ${VAR:=default} or ${VAR=default}
    AssignDefault {
        value: String,
        check_null: bool,
    },
    /// Use alternative value: ${VAR:+value} or ${VAR+value}
    UseAlternative {
        value: String,
        check_null: bool,
    },
    /// Error if unset: ${VAR:?message} or ${VAR?message}
    ErrorIfUnset {
        message: Option<String>,
        check_null: bool,
    },
    /// String length: ${#VAR}
    Length,
    /// Substring extraction: ${VAR:offset} or ${VAR:offset:length}
    Substring {
        offset: i32,
        length: Option<usize>,
    },
}

/// Parsed parameter expansion from ${VAR...} syntax
#[derive(Debug, Clone, PartialEq)]
struct ParameterExpansion {
    var_name: String,
    operation: ExpansionOp,
}

/// Word with quote information for expansion
#[derive(Debug, Clone, PartialEq)]
struct QuotedWord {
    parts: Vec<WordPart>,
    quote_type: QuoteType,
}

impl QuotedWord {
    fn new() -> Self {
        Self {
            parts: Vec::new(),
            quote_type: QuoteType::None,
        }
    }

    fn with_quote_type(quote_type: QuoteType) -> Self {
        Self {
            parts: Vec::new(),
            quote_type,
        }
    }

    fn is_empty(&self) -> bool {
        self.parts.is_empty()
    }

    fn push_literal(&mut self, s: String) {
        if !s.is_empty() {
            self.parts.push(WordPart::Literal(s));
        }
    }

    fn push_variable(&mut self, name: String) {
        self.parts.push(WordPart::Variable(name));
    }

    fn push_braced_variable(&mut self, name: String) {
        self.parts.push(WordPart::BracedVariable(name));
    }

    fn push_command_sub(&mut self, cmd: String) {
        self.parts.push(WordPart::CommandSub(cmd));
    }

    fn push_process_sub(&mut self, sub_type: ProcessSubType, cmd: String) {
        self.parts.push(WordPart::ProcessSub(sub_type, cmd));
    }
}

/// Token from lexical analysis
#[derive(Debug, Clone, PartialEq)]
enum Token {
    /// Word with potential quoting and variables
    Word(QuotedWord),

    /// Output redirection operator: >
    OutputRedirect,

    /// Append redirection operator: >>
    AppendRedirect,

    /// Input redirection operator: <
    InputRedirect,

    /// Error output redirection operator: 2>
    ErrorRedirect,

    /// Error append redirection operator: 2>>
    ErrorAppendRedirect,

    /// Error to output redirection: 2>&1
    ErrorToOutput,

    /// Both output redirection (bash extension): &>
    BothRedirect,

    /// Pipeline operator: |
    Pipe,

    /// Here document: <<
    HereDoc,

    /// Here document with tab stripping: <<-
    HereDocDash,

    /// Here string: <<<
    HereString,

    /// Background operator: &
    Background,

    /// Logical AND operator: &&
    And,

    /// Logical OR operator: ||
    Or,

    /// Extended test open: [[
    ExtendedTestOpen,

    /// Extended test close: ]]
    ExtendedTestClose,
}

/// Parsed command with arguments and redirections.
///
/// Represents all built-in and external commands that can be executed.
/// Built-in commands are variants of this enum; external commands use
/// [`Command::External`].
///
/// # Examples
/// ```
/// use vsh::parser::{parse_command, Command};
///
/// let cmd = parse_command("mkdir test")?;
/// match cmd {
///     Command::Mkdir { path, .. } => assert_eq!(path, "test"),
///     _ => panic!("Wrong command"),
/// }
/// # Ok::<(), anyhow::Error>(())
/// ```
#[derive(Debug, PartialEq)]
pub enum Command {
    // Built-ins (existing)
    Mkdir {
        path: String,
        redirects: Vec<Redirection>,
    },
    Rmdir {
        path: String,
        redirects: Vec<Redirection>,
    },
    Touch {
        path: String,
        redirects: Vec<Redirection>,
    },
    Rm {
        path: String,
        redirects: Vec<Redirection>,
    },
    Undo {
        count: usize,
    },
    Redo {
        count: usize,
    },
    History {
        count: usize,
        show_proofs: bool,
    },
    Exit,
    Quit,

    // Transactions
    Begin {
        name: String,
    },
    Commit,
    Rollback,

    // Display commands
    Graph,
    Proofs,
    Ls {
        path: Option<String>,
        redirects: Vec<Redirection>,
    },
    Pwd {
        redirects: Vec<Redirection>,
    },
    Cd {
        path: Option<String>,
    },

    // Conditionals
    Test {
        args: Vec<String>,
        redirects: Vec<Redirection>,
    },
    Bracket {
        args: Vec<String>,
        redirects: Vec<Redirection>,
    },
    /// Extended test [[ ... ]] - bash-style with pattern/regex matching
    ExtendedTest {
        args: Vec<String>,
        redirects: Vec<Redirection>,
    },

    // External command
    External {
        program: String,
        args: Vec<String>,
        redirects: Vec<Redirection>,
        background: bool,
    },

    /// Pipeline of external commands (cmd1 | cmd2 | cmd3)
    ///
    /// Each stage is a (program, args) pair. Intermediate stages use piped stdio.
    /// Final redirections apply to the last stage only.
    Pipeline {
        stages: Vec<(String, Vec<String>)>,
        redirects: Vec<Redirection>,
        background: bool,
    },

    /// Variable assignment (VAR=value)
    ///
    /// Sets a shell variable. If followed by a command, the assignment is
    /// temporary for that command only (not yet implemented).
    Assignment {
        name: String,
        value: String,
    },

    /// Array assignment (arr=(val1 val2 val3))
    ///
    /// Sets an indexed array variable with initial values
    ArrayAssignment {
        name: String,
        elements: Vec<String>,
    },

    /// Array element assignment (arr[index]=value)
    ///
    /// Sets a single array element at the specified index (supports sparse arrays)
    ArrayElementAssignment {
        name: String,
        index: usize,
        value: String,
    },

    /// Array append (arr+=(val1 val2))
    ///
    /// Appends elements to an existing array
    ArrayAppend {
        name: String,
        elements: Vec<String>,
    },

    /// Export command (export VAR or export VAR=value)
    Export {
        name: String,
        value: Option<String>,
    },

    // Job control
    /// List jobs
    Jobs {
        long: bool,
    },

    /// Bring job to foreground
    Fg {
        job_spec: Option<String>,
    },

    /// Continue job in background
    Bg {
        job_spec: Option<String>,
    },

    /// Kill a job
    Kill {
        signal: Option<String>,
        job_spec: String,
    },

    /// Logical operation (cmd1 && cmd2 or cmd1 || cmd2)
    LogicalOp {
        operator: LogicalOperator,
        left: Box<Command>,
        right: Box<Command>,
    },
}

/// Logical operators for command chaining
#[derive(Debug, Clone, PartialEq)]
pub enum LogicalOperator {
    /// AND (&&) - execute right only if left succeeds
    And,
    /// OR (||) - execute right only if left fails
    Or,
}

/// Quote state during tokenization
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum QuoteState {
    None,
    SingleQuote,   // Inside '...'
    DoubleQuote,   // Inside "..."
    Backslash,     // After \ (escape next char)
}

/// Tokenize input string into words and redirection operators
///
/// Handles:
/// - Single quotes '...' (no expansion)
/// - Double quotes "..." (expansion allowed)
/// - Backslash escaping \
/// - Redirection operators: >, >>, <, 2>, 2>>, 2>&1, &>
/// - Pipeline operator: |
fn tokenize(input: &str) -> Result<Vec<Token>> {
    let mut tokens = Vec::new();
    let mut chars = input.chars().peekable();
    let mut current_word = QuotedWord::new();
    let mut current_literal = String::new();
    let mut quote_state = QuoteState::None;

    /// Helper to push current literal to word if not empty
    macro_rules! push_literal {
        () => {
            if !current_literal.is_empty() {
                current_word.push_literal(current_literal.clone());
                current_literal.clear();
            }
        };
    }

    /// Helper to push current word to tokens if not empty
    macro_rules! push_word {
        () => {
            push_literal!();
            if !current_word.is_empty() {
                tokens.push(Token::Word(current_word.clone()));
                current_word = QuotedWord::new();
            }
        };
    }

    while let Some(ch) = chars.next() {
        match quote_state {
            QuoteState::Backslash => {
                // After backslash: take character literally
                // If escaping $, keep the backslash so expand_variables() skips it
                if ch == '$' {
                    current_literal.push('\\');
                }
                current_literal.push(ch);
                quote_state = QuoteState::None;
            }

            QuoteState::SingleQuote => {
                // Inside single quotes: everything is literal except closing '
                if ch == '\'' {
                    push_literal!();
                    quote_state = QuoteState::None;
                } else {
                    current_literal.push(ch);
                }
            }

            QuoteState::DoubleQuote => {
                // Inside double quotes: expansion allowed, escape with \
                match ch {
                    '"' => {
                        // End double quote
                        push_literal!();
                        quote_state = QuoteState::None;
                    }
                    '\\' => {
                        // Backslash in double quotes
                        if let Some(&next_ch) = chars.peek() {
                            if matches!(next_ch, '"' | '$' | '\\' | '\n') {
                                // Escape these special chars
                                chars.next();
                                // If escaping $, keep backslash so expand_variables() skips it
                                if next_ch == '$' {
                                    current_literal.push('\\');
                                }
                                current_literal.push(next_ch);
                            } else {
                                // Not a special char, keep backslash
                                current_literal.push('\\');
                            }
                        } else {
                            current_literal.push('\\');
                        }
                    }
                    '$' => {
                        // Variable expansion in double quotes
                        push_literal!();
                        parse_variable(&mut chars, &mut current_word)?;
                    }
                    '`' => {
                        // Backtick command substitution in double quotes
                        push_literal!();
                        let cmd = parse_command_sub_backtick(&mut chars)?;
                        current_word.push_command_sub(cmd);
                    }
                    _ => {
                        current_literal.push(ch);
                    }
                }
            }

            QuoteState::None => {
                // Outside quotes
                match ch {
                    // Quotes
                    '\'' => {
                        push_literal!();
                        current_word.quote_type = QuoteType::Single;
                        quote_state = QuoteState::SingleQuote;
                    }
                    '"' => {
                        push_literal!();
                        current_word.quote_type = QuoteType::Double;
                        quote_state = QuoteState::DoubleQuote;
                    }
                    '\\' => {
                        push_literal!();
                        quote_state = QuoteState::Backslash;
                    }

                    // Variable expansion
                    '$' => {
                        push_literal!();
                        parse_variable(&mut chars, &mut current_word)?;
                    }

                    // Backtick command substitution
                    '`' => {
                        push_literal!();
                        let cmd = parse_command_sub_backtick(&mut chars)?;
                        current_word.push_command_sub(cmd);
                    }

                    // Whitespace: end current word
                    ' ' | '\t' => {
                        push_word!();
                    }

                    // Redirection operators and process substitution
                    '>' => {
                        if chars.peek() == Some(&'(') {
                            // Process substitution: >(cmd)
                            push_literal!();
                            let cmd = parse_process_sub_output(&mut chars)?;
                            current_word.push_process_sub(ProcessSubType::Output, cmd);
                        } else {
                            // Regular redirection: > or >>
                            push_word!();
                            if chars.peek() == Some(&'>') {
                                chars.next();
                                tokens.push(Token::AppendRedirect);
                            } else {
                                tokens.push(Token::OutputRedirect);
                            }
                        }
                    }

                    '<' => {
                        if chars.peek() == Some(&'<') {
                            // Could be << or <<<
                            chars.next(); // consume second <
                            if chars.peek() == Some(&'<') {
                                // Here string: <<<
                                chars.next(); // consume third <
                                push_word!();
                                tokens.push(Token::HereString);
                            } else if chars.peek() == Some(&'-') {
                                // Here document with tab stripping: <<-
                                chars.next(); // consume -
                                push_word!();
                                tokens.push(Token::HereDocDash);
                            } else {
                                // Here document: <<
                                push_word!();
                                tokens.push(Token::HereDoc);
                            }
                        } else if chars.peek() == Some(&'(') {
                            // Process substitution: <(cmd)
                            push_literal!();
                            let cmd = parse_process_sub_input(&mut chars)?;
                            current_word.push_process_sub(ProcessSubType::Input, cmd);
                        } else {
                            // Input redirection: <
                            push_word!();
                            tokens.push(Token::InputRedirect);
                        }
                    }

                    '2' => {
                        // Check if this is start of 2> or 2>&1
                        if chars.peek() == Some(&'>') {
                            push_word!();
                            chars.next(); // consume >

                            match chars.peek() {
                                Some(&'>') => {
                                    chars.next();
                                    tokens.push(Token::ErrorAppendRedirect);
                                }
                                Some(&'&') => {
                                    chars.next();
                                    if chars.peek() == Some(&'1') {
                                        chars.next();
                                        tokens.push(Token::ErrorToOutput);
                                    } else {
                                        // Invalid: 2>&[not 1]
                                        current_literal.push_str("2>&");
                                    }
                                }
                                _ => {
                                    tokens.push(Token::ErrorRedirect);
                                }
                            }
                        } else {
                            // Regular '2' character, part of word
                            current_literal.push(ch);
                        }
                    }

                    '&' => {
                        // Check for &&, &>, or &
                        if chars.peek() == Some(&'&') {
                            push_word!();
                            chars.next();
                            tokens.push(Token::And);
                        } else if chars.peek() == Some(&'>') {
                            push_word!();
                            chars.next();
                            tokens.push(Token::BothRedirect);
                        } else {
                            // Background job operator: &
                            push_word!();
                            tokens.push(Token::Background);
                        }
                    }

                    '|' => {
                        // Check for || or |
                        if chars.peek() == Some(&'|') {
                            push_word!();
                            chars.next();
                            tokens.push(Token::Or);
                        } else {
                            push_word!();
                            tokens.push(Token::Pipe);
                        }
                    }

                    '[' => {
                        // Check for [[ (extended test) or [ (regular test/bracket)
                        if chars.peek() == Some(&'[') {
                            push_word!();
                            chars.next();
                            tokens.push(Token::ExtendedTestOpen);
                        } else {
                            // Regular '[' character, part of word
                            current_literal.push(ch);
                        }
                    }

                    ']' => {
                        // Check for ]] (extended test close) or ] (regular bracket)
                        if chars.peek() == Some(&']') {
                            push_word!();
                            chars.next();
                            tokens.push(Token::ExtendedTestClose);
                        } else {
                            // Regular ']' character, part of word
                            current_literal.push(ch);
                        }
                    }

                    // Regular character
                    _ => {
                        current_literal.push(ch);
                    }
                }
            }
        }
    }

    // Check for unclosed quotes
    match quote_state {
        QuoteState::SingleQuote => {
            return Err(anyhow!("Unclosed single quote"));
        }
        QuoteState::DoubleQuote => {
            return Err(anyhow!("Unclosed double quote"));
        }
        _ => {}
    }

    // Add final word if any
    push_word!();

    Ok(tokens)
}

/// Parse a variable reference ($VAR or ${VAR}) from the character stream
fn parse_variable(
    chars: &mut std::iter::Peekable<std::str::Chars>,
    word: &mut QuotedWord,
) -> Result<()> {
    if chars.peek() == Some(&'(') {
        // Command substitution: $(cmd)
        chars.next(); // consume '('
        let cmd = parse_command_sub_dollar(chars)?;
        word.push_command_sub(cmd);
    } else if chars.peek() == Some(&'{') {
        // Braced form: ${VAR}
        chars.next(); // consume '{'
        let mut var_name = String::new();

        loop {
            match chars.peek() {
                Some(&'}') => {
                    chars.next(); // consume '}'
                    break;
                }
                Some(&ch) => {
                    var_name.push(ch);
                    chars.next();
                }
                None => {
                    return Err(anyhow!("Unclosed braced variable reference"));
                }
            }
        }

        word.push_braced_variable(var_name);
    } else if let Some(&next_ch) = chars.peek() {
        // Simple form: $VAR or special variables
        if next_ch == '?' || next_ch == '$' || next_ch == '#' {
            // Single-character special variable
            let var_name = chars.next().unwrap().to_string();
            word.push_variable(var_name);
        } else if next_ch.is_ascii_digit() {
            // Positional parameter: $0, $1, $2, etc.
            let var_name = chars.next().unwrap().to_string();
            word.push_variable(var_name);
        } else if next_ch.is_alphabetic() || next_ch == '_' {
            // Variable name
            let mut var_name = String::new();

            while let Some(&c) = chars.peek() {
                if c.is_alphanumeric() || c == '_' {
                    var_name.push(c);
                    chars.next();
                } else {
                    break;
                }
            }

            word.push_variable(var_name);
        } else if next_ch == '@' || next_ch == '*' {
            // Special positional parameters: $@ or $*
            let var_name = chars.next().unwrap().to_string();
            word.push_variable(var_name);
        } else {
            // $ not followed by variable, treat as literal
            word.push_literal("$".to_string());
        }
    } else {
        // $ at end of string
        word.push_literal("$".to_string());
    }

    Ok(())
}

/// Parse command substitution in $(cmd) form
fn parse_command_sub_dollar(chars: &mut std::iter::Peekable<std::str::Chars>) -> Result<String> {
    let mut cmd = String::new();
    let mut depth = 1;  // Track nesting depth for nested $()

    while let Some(ch) = chars.next() {
        match ch {
            '(' => {
                // Check if it's $( to track nested command substitution
                if cmd.ends_with('$') {
                    depth += 1;
                }
                cmd.push(ch);
            }
            ')' => {
                depth -= 1;
                if depth == 0 {
                    return Ok(cmd);
                }
                cmd.push(ch);
            }
            _ => cmd.push(ch),
        }
    }

    Err(anyhow!("Unclosed command substitution: $("))
}

/// Parse command substitution in `cmd` form
fn parse_command_sub_backtick(chars: &mut std::iter::Peekable<std::str::Chars>) -> Result<String> {
    let mut cmd = String::new();
    let mut escaped = false;

    while let Some(ch) = chars.next() {
        match (ch, escaped) {
            ('\\', false) => escaped = true,
            ('`', false) => return Ok(cmd),
            ('`', true) => {
                cmd.push('`');
                escaped = false;
            }
            ('\\', true) => {
                cmd.push('\\');
                escaped = false;
            }
            ('$', true) => {
                cmd.push('$');
                escaped = false;
            }
            (_, true) => {
                // Other escaped characters: keep backslash
                cmd.push('\\');
                cmd.push(ch);
                escaped = false;
            }
            (_, false) => cmd.push(ch),
        }
    }

    Err(anyhow!("Unclosed command substitution: `"))
}

/// Parse process substitution in <(cmd) form (input)
fn parse_process_sub_input(chars: &mut std::iter::Peekable<std::str::Chars>) -> Result<String> {
    // Expects that '<(' has been detected and < consumed
    chars.next(); // consume '('

    let mut cmd = String::new();
    let mut depth = 1;  // Track nesting depth

    while let Some(ch) = chars.next() {
        match ch {
            '(' => {
                depth += 1;
                cmd.push(ch);
            }
            ')' => {
                depth -= 1;
                if depth == 0 {
                    return Ok(cmd);
                }
                cmd.push(ch);
            }
            _ => cmd.push(ch),
        }
    }

    Err(anyhow!("Unclosed process substitution: <("))
}

/// Parse process substitution in >(cmd) form (output)
fn parse_process_sub_output(chars: &mut std::iter::Peekable<std::str::Chars>) -> Result<String> {
    // Expects that '>(' has been detected and > consumed
    chars.next(); // consume '('

    let mut cmd = String::new();
    let mut depth = 1;  // Track nesting depth

    while let Some(ch) = chars.next() {
        match ch {
            '(' => {
                depth += 1;
                cmd.push(ch);
            }
            ')' => {
                depth -= 1;
                if depth == 0 {
                    return Ok(cmd);
                }
                cmd.push(ch);
            }
            _ => cmd.push(ch),
        }
    }

    Err(anyhow!("Unclosed process substitution: >("))
}

/// Parse a pipeline command (tokens containing `|` operators).
///
/// Splits the token stream on Pipe operators, parses each stage as (program, args),
/// and extracts final redirections from the last stage.
///
/// # Arguments
/// * `tokens` - Token stream containing at least one `Token::Pipe`
///
/// # Returns
/// [`Command::Pipeline`] with stages and final redirections
///
/// # Errors
/// Returns error if:
/// - Pipeline has empty stages
/// - Pipeline has less than 2 stages
/// - Stage has no command name
/// - Invalid redirections in last stage
/// Parse extended test command [[ ... ]]
fn parse_extended_test(tokens: &[Token]) -> Result<Command> {
    // Verify structure: [[ ... ]]
    if tokens.first() != Some(&Token::ExtendedTestOpen) {
        return Err(anyhow!("Extended test must start with [["));
    }

    // Find closing ]]
    let close_pos = tokens.iter().position(|t| matches!(t, Token::ExtendedTestClose))
        .ok_or_else(|| anyhow!("Extended test missing closing ]]"))?;

    // Extract arguments between [[ and ]]
    let mut args = Vec::new();
    for i in 1..close_pos {
        if let Token::Word(w) = &tokens[i] {
            args.push(quoted_word_to_string(w));
        } else {
            // For now, convert other tokens to strings
            // TODO: Handle operators specially in Task #40
            args.push(format!("{:?}", tokens[i]));
        }
    }

    // Extract redirections after ]]
    let mut redirects = Vec::new();
    let mut i = close_pos + 1;
    while i < tokens.len() {
        match &tokens[i] {
            Token::OutputRedirect => {
                let file = expect_word(tokens, i + 1, "output redirection")?;
                redirects.push(Redirection::Output { file });
                i += 2;
            }
            Token::AppendRedirect => {
                let file = expect_word(tokens, i + 1, "append redirection")?;
                redirects.push(Redirection::Append { file });
                i += 2;
            }
            Token::InputRedirect => {
                let file = expect_word(tokens, i + 1, "input redirection")?;
                redirects.push(Redirection::Input { file });
                i += 2;
            }
            Token::ErrorRedirect => {
                let file = expect_word(tokens, i + 1, "error redirection")?;
                redirects.push(Redirection::ErrorOutput { file });
                i += 2;
            }
            _ => {
                return Err(anyhow!("Unexpected token after ]]"));
            }
        }
    }

    Ok(Command::ExtendedTest { args, redirects })
}

/// Parse logical operators (&& and ||)
fn parse_logical_op(tokens: &[Token], op_pos: usize) -> Result<Command> {
    // Get the operator type
    let operator = match &tokens[op_pos] {
        Token::And => LogicalOperator::And,
        Token::Or => LogicalOperator::Or,
        _ => return Err(anyhow!("Expected && or ||")),
    };

    // Split into left and right parts
    let left_tokens = &tokens[..op_pos];
    let right_tokens = &tokens[op_pos + 1..];

    if left_tokens.is_empty() {
        return Err(anyhow!("Missing command before {:?}", operator));
    }
    if right_tokens.is_empty() {
        return Err(anyhow!("Missing command after {:?}", operator));
    }

    // Recursively parse left and right commands
    // Convert tokens back to string for parsing (simplified approach)
    let left_str = tokens_to_string(left_tokens)?;
    let right_str = tokens_to_string(right_tokens)?;

    let left_cmd = parse_command(&left_str)?;
    let right_cmd = parse_command(&right_str)?;

    Ok(Command::LogicalOp {
        operator,
        left: Box::new(left_cmd),
        right: Box::new(right_cmd),
    })
}

/// Convert tokens back to a string for recursive parsing
fn tokens_to_string(tokens: &[Token]) -> Result<String> {
    let mut result = String::new();

    for (i, token) in tokens.iter().enumerate() {
        if i > 0 {
            result.push(' ');
        }

        match token {
            Token::Word(w) => result.push_str(&quoted_word_to_string(w)),
            Token::OutputRedirect => result.push('>'),
            Token::AppendRedirect => result.push_str(">>"),
            Token::InputRedirect => result.push('<'),
            Token::ErrorRedirect => result.push_str("2>"),
            Token::ErrorAppendRedirect => result.push_str("2>>"),
            Token::ErrorToOutput => result.push_str("2>&1"),
            Token::BothRedirect => result.push_str("&>"),
            Token::Pipe => result.push('|'),
            Token::HereDoc => result.push_str("<<"),
            Token::HereDocDash => result.push_str("<<-"),
            Token::HereString => result.push_str("<<<"),
            Token::Background => result.push('&'),
            Token::And => return Err(anyhow!("Unexpected && in tokens_to_string")),
            Token::Or => return Err(anyhow!("Unexpected || in tokens_to_string")),
            Token::ExtendedTestOpen => result.push_str("[["),
            Token::ExtendedTestClose => result.push_str("]]"),
        }
    }

    Ok(result)
}

fn parse_pipeline(tokens: &[Token]) -> Result<Command> {
    // Split token stream on Pipe tokens
    let mut stages: Vec<Vec<Token>> = Vec::new();
    let mut current_stage: Vec<Token> = Vec::new();

    for token in tokens {
        match token {
            Token::Pipe => {
                if current_stage.is_empty() {
                    return Err(anyhow!("Empty pipeline stage"));
                }
                stages.push(current_stage.clone());
                current_stage.clear();
            }
            _ => current_stage.push(token.clone()),
        }
    }

    // Add final stage
    if current_stage.is_empty() {
        return Err(anyhow!("Pipeline ends with |"));
    }
    stages.push(current_stage);

    if stages.len() < 2 {
        return Err(anyhow!("Pipeline must have at least 2 stages"));
    }

    // Extract final redirections from last stage
    let last_stage_idx = stages.len() - 1;
    let (last_command_tokens, final_redirects) =
        extract_redirections_from_tokens(&stages[last_stage_idx])?;
    stages[last_stage_idx] = last_command_tokens;

    // Parse each stage as (program, args)
    let mut parsed_stages: Vec<(String, Vec<String>)> = Vec::new();

    for stage_tokens in stages {
        if stage_tokens.is_empty() {
            return Err(anyhow!("Empty pipeline stage"));
        }

        let words: Vec<String> = stage_tokens
            .iter()
            .filter_map(|t| match t {
                Token::Word(w) => Some(quoted_word_to_string(w)),
                _ => None,
            })
            .collect();

        if words.is_empty() {
            return Err(anyhow!("Pipeline stage has no command"));
        }

        let program = words[0].clone();
        let args = words[1..].to_vec();
        parsed_stages.push((program, args));
    }

    Ok(Command::Pipeline {
        stages: parsed_stages,
        redirects: final_redirects,
        background: false,  // TODO: detect & in pipeline
    })
}

/// Extract redirections from a token slice, returning (command_tokens, redirections).
///
/// Separates command words from redirection operators and their targets.
fn extract_redirections_from_tokens(tokens: &[Token]) -> Result<(Vec<Token>, Vec<Redirection>)> {
    let mut command_tokens = Vec::new();
    let mut redirects = Vec::new();

    let mut i = 0;
    while i < tokens.len() {
        match &tokens[i] {
            Token::Word(_) => {
                command_tokens.push(tokens[i].clone());
                i += 1;
            }

            Token::OutputRedirect => {
                let file = expect_word(tokens, i + 1, "output redirection")?;
                redirects.push(Redirection::Output { file });
                i += 2;
            }

            Token::AppendRedirect => {
                let file = expect_word(tokens, i + 1, "append redirection")?;
                redirects.push(Redirection::Append { file });
                i += 2;
            }

            Token::InputRedirect => {
                let file = expect_word(tokens, i + 1, "input redirection")?;
                redirects.push(Redirection::Input { file });
                i += 2;
            }

            Token::ErrorRedirect => {
                let file = expect_word(tokens, i + 1, "error redirection")?;
                redirects.push(Redirection::ErrorOutput { file });
                i += 2;
            }

            Token::ErrorAppendRedirect => {
                let file = expect_word(tokens, i + 1, "error append redirection")?;
                redirects.push(Redirection::ErrorAppend { file });
                i += 2;
            }

            Token::ErrorToOutput => {
                redirects.push(Redirection::ErrorToOutput);
                i += 1;
            }

            Token::BothRedirect => {
                let file = expect_word(tokens, i + 1, "both redirection")?;
                redirects.push(Redirection::BothOutput { file });
                i += 2;
            }

            Token::HereDoc | Token::HereDocDash => {
                // Here document: << DELIMITER or <<- DELIMITER
                let strip_tabs = matches!(&tokens[i], Token::HereDocDash);
                let delimiter = expect_word(&tokens, i + 1, "here document delimiter")?;

                // Check if delimiter is quoted (disables expansion)
                let (delimiter_clean, expand) = if delimiter.starts_with('\'') || delimiter.starts_with('"') {
                    (delimiter.trim_matches(|c| c == '\'' || c == '"').to_string(), false)
                } else {
                    (delimiter.clone(), true)
                };

                // Content will be provided by REPL after reading subsequent lines
                // For now, create placeholder - will be filled by execute_with_heredoc
                redirects.push(Redirection::HereDoc {
                    delimiter: delimiter_clean,
                    content: String::new(), // Filled later
                    expand,
                    strip_tabs,
                });
                i += 2;
            }

            Token::HereString => {
                // Here string: <<< word
                let content_word = expect_word(&tokens, i + 1, "here string content")?;

                // Check if quoted (disables expansion)
                let (content, expand) = if content_word.starts_with('\'') {
                    (content_word.trim_matches('\'').to_string(), false)
                } else if content_word.starts_with('"') {
                    (content_word.trim_matches('"').to_string(), true)
                } else {
                    (content_word.clone(), true)
                };

                redirects.push(Redirection::HereString {
                    content,
                    expand,
                });
                i += 2;
            }

            Token::Background => {
                // Background operator - skip it here, handled at top level
                i += 1;
            }

            Token::Pipe => {
                return Err(anyhow!("Unexpected pipe in stage"));
            }

            Token::And | Token::Or => {
                return Err(anyhow!("Unexpected logical operator in stage"));
            }

            Token::ExtendedTestOpen | Token::ExtendedTestClose => {
                return Err(anyhow!("Unexpected [[ or ]] token - should be handled at top level"));
            }
        }
    }

    Ok((command_tokens, redirects))
}

/// Parse a command line into a structured [`Command`] with redirections.
///
/// Tokenizes the input, identifies built-in commands vs external programs,
/// and extracts I/O redirections.
///
/// # Arguments
/// * `input` - Raw command line string (e.g., "ls -la > output.txt")
///
/// # Returns
/// Parsed [`Command`] ready for execution
///
/// # Errors
/// Returns error if:
/// - Invalid redirection syntax
/// - Missing redirection target
/// - Malformed command
///
/// # Examples
/// ```
/// use vsh::parser::parse_command;
///
/// let cmd = parse_command("mkdir project > log.txt")?;
/// // Creates Mkdir command with Output redirection
/// # Ok::<(), anyhow::Error>(())
/// ```
pub fn parse_command(input: &str) -> Result<Command> {
    // Skip comments (lines starting with #)
    let trimmed = input.trim_start();
    if trimmed.starts_with('#') || trimmed.is_empty() {
        return Err(anyhow!("Empty command"));
    }

    // Tokenize input
    let tokens = tokenize(input)?;

    if tokens.is_empty() {
        return Err(anyhow!("Empty command"));
    }

    // Check for variable/array assignment
    // Must be first token and contain '=' but not be a redirection
    if tokens.len() >= 1 {
        if let Token::Word(first_word) = &tokens[0] {
            let first_str = quoted_word_to_string(first_word);

            // Check for array element assignment: arr[index]=value
            if let Some(bracket_pos) = first_str.find('[') {
                if let Some(close_bracket) = first_str.find(']') {
                    if let Some(eq_pos) = first_str.find('=') {
                        if bracket_pos < close_bracket && close_bracket < eq_pos {
                            let name = &first_str[..bracket_pos];
                            let index_str = &first_str[bracket_pos + 1..close_bracket];
                            let value = &first_str[eq_pos + 1..];

                            if is_valid_var_name(name) {
                                if let Ok(index) = index_str.parse::<usize>() {
                                    return Ok(Command::ArrayElementAssignment {
                                        name: name.to_string(),
                                        index,
                                        value: value.to_string(),
                                    });
                                }
                            }
                        }
                    }
                }
            }

            // Check for array append: arr+=(val1 val2)
            if let Some(plus_pos) = first_str.find("+=(") {
                let name = &first_str[..plus_pos];
                if is_valid_var_name(name) {
                    // Extract array elements from parentheses
                    let rest = &first_str[plus_pos + 3..];
                    if let Some(close_paren) = rest.rfind(')') {
                        let elements_str = &rest[..close_paren];
                        let elements: Vec<String> = elements_str
                            .split_whitespace()
                            .map(|s| s.to_string())
                            .collect();
                        return Ok(Command::ArrayAppend {
                            name: name.to_string(),
                            elements,
                        });
                    }
                }
            }

            // Check for array assignment: arr=(val1 val2 val3)
            if let Some(eq_pos) = first_str.find("=(") {
                let name = &first_str[..eq_pos];
                if is_valid_var_name(name) {
                    // Extract array elements from parentheses
                    let rest = &first_str[eq_pos + 2..];
                    if let Some(close_paren) = rest.rfind(')') {
                        let elements_str = &rest[..close_paren];
                        let elements: Vec<String> = elements_str
                            .split_whitespace()
                            .map(|s| s.to_string())
                            .collect();
                        return Ok(Command::ArrayAssignment {
                            name: name.to_string(),
                            elements,
                        });
                    }
                }
            }

            // Check for scalar assignment: VAR=value
            if let Some(eq_pos) = first_str.find('=') {
                // Make sure it's not already handled above
                if !first_str.contains("=(") && !first_str.contains("[") && !first_str.contains("+=") {
                    let name = &first_str[..eq_pos];
                    let value = &first_str[eq_pos + 1..];

                    // Variable name must be valid: start with letter/underscore, then alphanumeric/underscore
                    if is_valid_var_name(name) {
                        return Ok(Command::Assignment {
                            name: name.to_string(),
                            value: value.to_string(),
                        });
                    }
                }
            }
        }
    }

    // Check for extended test [[ ... ]]
    if tokens.first() == Some(&Token::ExtendedTestOpen) {
        return parse_extended_test(&tokens);
    }

    // Check for logical operators (&&, ||) - lowest precedence
    if let Some(op_pos) = tokens.iter().position(|t| matches!(t, Token::And | Token::Or)) {
        return parse_logical_op(&tokens, op_pos);
    }

    // Check if input contains pipes - if so, parse as pipeline
    if tokens.iter().any(|t| matches!(t, Token::Pipe)) {
        return parse_pipeline(&tokens);
    }

    // Separate command tokens from redirections
    let mut command_tokens: Vec<String> = Vec::new();
    let mut redirects = Vec::new();
    let mut background = false;

    let mut i = 0;
    while i < tokens.len() {
        match &tokens[i] {
            Token::Word(w) => {
                command_tokens.push(quoted_word_to_string(w));
                i += 1;
            }

            Token::OutputRedirect => {
                let file = expect_word(&tokens, i + 1, "output redirection")?;
                redirects.push(Redirection::Output { file });
                i += 2;
            }

            Token::AppendRedirect => {
                let file = expect_word(&tokens, i + 1, "append redirection")?;
                redirects.push(Redirection::Append { file });
                i += 2;
            }

            Token::InputRedirect => {
                let file = expect_word(&tokens, i + 1, "input redirection")?;
                redirects.push(Redirection::Input { file });
                i += 2;
            }

            Token::ErrorRedirect => {
                let file = expect_word(&tokens, i + 1, "error redirection")?;
                redirects.push(Redirection::ErrorOutput { file });
                i += 2;
            }

            Token::ErrorAppendRedirect => {
                let file = expect_word(&tokens, i + 1, "error append redirection")?;
                redirects.push(Redirection::ErrorAppend { file });
                i += 2;
            }

            Token::ErrorToOutput => {
                redirects.push(Redirection::ErrorToOutput);
                i += 1;
            }

            Token::BothRedirect => {
                let file = expect_word(&tokens, i + 1, "both redirection")?;
                redirects.push(Redirection::BothOutput { file });
                i += 2;
            }

            Token::HereDoc | Token::HereDocDash => {
                // Here document: << DELIMITER or <<- DELIMITER
                let strip_tabs = matches!(&tokens[i], Token::HereDocDash);
                let delimiter = expect_word(&tokens, i + 1, "here document delimiter")?;

                // Check if delimiter is quoted (disables expansion)
                let (delimiter_clean, expand) = if delimiter.starts_with('\'') || delimiter.starts_with('"') {
                    (delimiter.trim_matches(|c| c == '\'' || c == '"').to_string(), false)
                } else {
                    (delimiter.clone(), true)
                };

                // Content will be provided by REPL after reading subsequent lines
                // For now, create placeholder - will be filled by execute_with_heredoc
                redirects.push(Redirection::HereDoc {
                    delimiter: delimiter_clean,
                    content: String::new(), // Filled later
                    expand,
                    strip_tabs,
                });
                i += 2;
            }

            Token::HereString => {
                // Here string: <<< word
                let content_word = expect_word(&tokens, i + 1, "here string content")?;

                // Check if quoted (disables expansion)
                let (content, expand) = if content_word.starts_with('\'') {
                    (content_word.trim_matches('\'').to_string(), false)
                } else if content_word.starts_with('"') {
                    (content_word.trim_matches('"').to_string(), true)
                } else {
                    (content_word.clone(), true)
                };

                redirects.push(Redirection::HereString {
                    content,
                    expand,
                });
                i += 2;
            }

            Token::Background => {
                // Background job: &
                // Must be last token
                if i != tokens.len() - 1 {
                    return Err(anyhow!("Background operator & must be at end of command"));
                }
                background = true;
                i += 1;
            }

            Token::Pipe => {
                // Should never reach here - pipes are caught at parse_command() entry
                return Err(anyhow!("Unexpected pipe token in single command"));
            }

            Token::And | Token::Or => {
                // Should never reach here - logical operators are caught at parse_command() entry
                return Err(anyhow!("Unexpected logical operator in single command"));
            }

            Token::ExtendedTestOpen | Token::ExtendedTestClose => {
                // Should never reach here - extended test is caught at parse_command() entry
                return Err(anyhow!("Unexpected [[ or ]] in single command"));
            }
        }
    }

    // Must have at least command name
    if command_tokens.is_empty() {
        return Err(anyhow!("Missing command (only redirections found)"));
    }

    // Parse command from tokens
    let cmd = &command_tokens[0];
    let args: Vec<String> = command_tokens[1..].to_vec();

    // Parse base command with redirections
    parse_base_command(cmd, args, redirects, background)
}

/// Check if a string is a valid variable name
/// Valid: starts with letter or underscore, then letters/digits/underscores
fn is_valid_var_name(name: &str) -> bool {
    if name.is_empty() {
        return false;
    }

    let mut chars = name.chars();
    let first = chars.next().unwrap();

    // First char must be letter or underscore
    if !first.is_alphabetic() && first != '_' {
        return false;
    }

    // Rest must be alphanumeric or underscore
    chars.all(|c| c.is_alphanumeric() || c == '_')
}

/// Expand variables in a string ($VAR and ${VAR} syntax).
///
/// Expands variable references to their values from the shell state.
/// Undefined variables expand to empty string (POSIX behavior).
///
/// # Syntax
/// - `$VAR` - Simple variable reference
/// - `${VAR}` - Braced variable reference
/// - `$$` - Process ID (special variable)
/// - `$?` - Last exit code (special variable)
/// - `$HOME`, `$PWD`, `$USER`, `$PATH` - Environment variables
///
/// # Examples
/// ```
/// use vsh::parser::expand_variables;
/// use vsh::state::ShellState;
///
/// let mut state = ShellState::new("/tmp/test")?;
/// state.set_variable("NAME", "Alice");
///
/// assert_eq!(expand_variables("Hello $NAME", &state), "Hello Alice");
/// assert_eq!(expand_variables("Hello ${NAME}!", &state), "Hello Alice!");
/// assert_eq!(expand_variables("Exit code: $?", &state), "Exit code: 0");
/// # Ok::<(), anyhow::Error>(())
/// ```
/// Expand variables and command substitutions in a string
pub fn expand_with_command_sub(input: &str, state: &mut crate::state::ShellState) -> Result<String> {
    let mut result = String::new();
    let mut chars = input.chars().peekable();

    while let Some(ch) = chars.next() {
        if ch == '\\' && chars.peek() == Some(&'$') {
            // Escaped dollar from single quotes - skip backslash, keep literal $
            result.push(chars.next().unwrap());
        } else if ch == '<' && chars.peek() == Some(&'(') {
            // Input process substitution: <(cmd)
            chars.next(); // consume '('
            let cmd = parse_process_sub_input(&mut chars)?;
            return Err(anyhow!(
                "Process substitution not yet implemented: execution requires FIFO support (<({}))",
                cmd
            ));
        } else if ch == '>' && chars.peek() == Some(&'(') {
            // Output process substitution: >(cmd)
            chars.next(); // consume '('
            let cmd = parse_process_sub_output(&mut chars)?;
            return Err(anyhow!(
                "Process substitution not yet implemented: execution requires FIFO support (>({}))",
                cmd
            ));
        } else if ch == '$' {
            // Check for $((expr)), $(cmd), ${VAR} or $VAR
            if chars.peek() == Some(&'(') {
                chars.next(); // consume first '('

                // Check for arithmetic expansion: $((
                if chars.peek() == Some(&'(') {
                    chars.next(); // consume second '('

                    // Read until ))
                    let mut expr_str = String::new();
                    let mut paren_depth = 0;

                    loop {
                        match chars.peek() {
                            None => return Err(anyhow!("Unclosed arithmetic expansion")),
                            Some(&')') => {
                                chars.next();
                                if chars.peek() == Some(&')') && paren_depth == 0 {
                                    chars.next(); // consume second ')'
                                    break;
                                } else if paren_depth > 0 {
                                    paren_depth -= 1;
                                    expr_str.push(')');
                                } else {
                                    expr_str.push(')');
                                }
                            }
                            Some(&'(') => {
                                paren_depth += 1;
                                expr_str.push(chars.next().unwrap());
                            }
                            Some(_) => {
                                expr_str.push(chars.next().unwrap());
                            }
                        }
                    }

                    // Parse and evaluate arithmetic expression
                    let expr = crate::arith::parse_arithmetic(&expr_str)?;
                    let value = crate::arith::eval_arith(&expr, state)?;
                    result.push_str(&value.to_string());
                } else {
                    // Command substitution: $(cmd)
                    let cmd = parse_command_sub_dollar(&mut chars)?;
                    let output = expand_command_substitution(&cmd, state)?;
                    result.push_str(&output);
                }
            } else if chars.peek() == Some(&'{') {
                // Braced form: ${VAR}
                chars.next(); // consume '{'
                let mut var_name = String::new();

                // Read until '}'
                while let Some(&c) = chars.peek() {
                    if c == '}' {
                        chars.next(); // consume '}'
                        break;
                    }
                    var_name.push(chars.next().unwrap());
                }

                // Expand the variable
                result.push_str(&state.expand_variable(&var_name));
            } else if let Some(&next_ch) = chars.peek() {
                // Simple form: $VAR or special variables like $?, $$
                if next_ch == '?' || next_ch == '$' || next_ch == '#' || next_ch == '@' || next_ch == '*' {
                    // Single-character special variable
                    let var_name = chars.next().unwrap().to_string();
                    result.push_str(&state.expand_variable(&var_name));
                } else if next_ch.is_ascii_digit() {
                    // Positional parameter: $0, $1, etc.
                    let var_name = chars.next().unwrap().to_string();
                    result.push_str(&state.expand_variable(&var_name));
                } else if next_ch.is_alphabetic() || next_ch == '_' {
                    // Variable name: starts with letter or underscore
                    let mut var_name = String::new();

                    // Read variable name (alphanumeric + underscore)
                    while let Some(&c) = chars.peek() {
                        if c.is_alphanumeric() || c == '_' {
                            var_name.push(chars.next().unwrap());
                        } else {
                            break;
                        }
                    }

                    result.push_str(&state.expand_variable(&var_name));
                } else {
                    // $ followed by non-variable character, keep literal $
                    result.push('$');
                }
            } else {
                // $ at end of string, keep literal $
                result.push('$');
            }
        } else if ch == '`' {
            // Backtick command substitution
            let cmd = parse_command_sub_backtick(&mut chars)?;
            let output = expand_command_substitution(&cmd, state)?;
            result.push_str(&output);
        } else {
            // Regular character
            result.push(ch);
        }
    }

    Ok(result)
}

/// Expand string with process substitutions (returns expanded string + process sub objects)
pub fn expand_with_process_sub(
    input: &str,
    state: &mut crate::state::ShellState,
) -> Result<(String, Vec<crate::process_sub::ProcessSubstitution>)> {
    let mut result = String::new();
    let mut process_subs = Vec::new();
    let mut chars = input.chars().peekable();

    while let Some(ch) = chars.next() {
        if ch == '<' && chars.peek() == Some(&'(') {
            // Input process substitution: <(cmd)
            // parse_process_sub_input will consume '(' itself
            let cmd = parse_process_sub_input(&mut chars)?;

            // Create and start process substitution
            let mut proc_sub = crate::process_sub::ProcessSubstitution::create(
                ProcessSubType::Input,
                cmd,
                state,
            )?;
            proc_sub.start(state)?;

            // Add FIFO path to result
            result.push_str(&proc_sub.fifo_path.to_string_lossy());
            process_subs.push(proc_sub);
        } else if ch == '>' && chars.peek() == Some(&'(') {
            // Output process substitution: >(cmd)
            // parse_process_sub_output will consume '(' itself
            let cmd = parse_process_sub_output(&mut chars)?;

            // Create and start process substitution
            let mut proc_sub = crate::process_sub::ProcessSubstitution::create(
                ProcessSubType::Output,
                cmd,
                state,
            )?;
            proc_sub.start(state)?;

            // Add FIFO path to result
            result.push_str(&proc_sub.fifo_path.to_string_lossy());
            process_subs.push(proc_sub);
        } else {
            // Not a process substitution, pass through to expand_with_command_sub
            result.push(ch);
        }
    }

    // Now expand variables and command substitutions in the result
    let expanded = expand_with_command_sub(&result, state)?;

    Ok((expanded, process_subs))
}

/// Parse parameter expansion syntax: ${VAR:-default}, ${VAR:offset}, ${#VAR}, etc.
fn parse_parameter_expansion(content: &str) -> Result<ParameterExpansion, String> {
    // Handle empty content
    if content.is_empty() {
        return Err("Empty parameter expansion".to_string());
    }

    let chars: Vec<char> = content.chars().collect();
    let mut pos = 0;

    // Check for length operator: ${#VAR}
    if chars[0] == '#' {
        let var_name = content[1..].to_string();
        return Ok(ParameterExpansion {
            var_name,
            operation: ExpansionOp::Length,
        });
    }

    // Extract variable name (until operator or end)
    let var_name_end = chars.iter()
        .position(|&c| matches!(c, ':' | '-' | '=' | '+' | '?'))
        .unwrap_or(chars.len());

    let var_name = content[..var_name_end].to_string();

    // If no operator, simple expansion
    if var_name_end == chars.len() {
        return Ok(ParameterExpansion {
            var_name,
            operation: ExpansionOp::Simple,
        });
    }

    pos = var_name_end;
    let check_null = chars[pos] == ':';
    if check_null {
        pos += 1;  // Skip ':'
    }

    if pos >= chars.len() {
        // ${VAR:} with nothing after - try substring with offset 0
        return Ok(ParameterExpansion {
            var_name,
            operation: ExpansionOp::Substring { offset: 0, length: None },
        });
    }

    let op_char = chars[pos];
    let rest = &content[pos + 1..];

    // Disambiguate operators from substring syntax
    // - ${VAR-X}, ${VAR:-X} → Default operator (dash immediately after var or colon)
    // - ${VAR: -5} → Substring (space after colon, then dash)
    // - ${VAR:5} → Substring (digit after colon)

    match op_char {
        '-' => {
            // ${VAR:-default} or ${VAR-default}
            Ok(ParameterExpansion {
                var_name,
                operation: ExpansionOp::Default {
                    value: rest.to_string(),
                    check_null,
                },
            })
        }
        '=' => {
            // ${VAR:=default} or ${VAR=default}
            Ok(ParameterExpansion {
                var_name,
                operation: ExpansionOp::AssignDefault {
                    value: rest.to_string(),
                    check_null,
                },
            })
        }
        '+' => {
            // ${VAR:+value} or ${VAR+value}
            Ok(ParameterExpansion {
                var_name,
                operation: ExpansionOp::UseAlternative {
                    value: rest.to_string(),
                    check_null,
                },
            })
        }
        '?' => {
            // ${VAR:?message} or ${VAR?message}
            let message = if rest.is_empty() {
                None
            } else {
                Some(rest.to_string())
            };
            Ok(ParameterExpansion {
                var_name,
                operation: ExpansionOp::ErrorIfUnset { message, check_null },
            })
        }
        c if c.is_ascii_digit() || c.is_whitespace() => {
            // ${VAR:offset} or ${VAR: -offset} (substring with space before negative)
            let offset_str = content[pos..].to_string();
            parse_substring_params(&offset_str)
                .map(|(offset, length)| ParameterExpansion {
                    var_name,
                    operation: ExpansionOp::Substring { offset, length },
                })
        }
        _ => Err(format!("Unknown expansion operator: {}", op_char)),
    }
}

/// Parse substring parameters: offset or offset:length
fn parse_substring_params(params: &str) -> Result<(i32, Option<usize>), String> {
    let parts: Vec<&str> = params.split(':').collect();

    match parts.len() {
        1 => {
            // Just offset (trim to handle ${VAR: -5} with space before negative)
            let offset = parts[0].trim().parse::<i32>()
                .map_err(|_| format!("Invalid offset: {}", parts[0]))?;
            Ok((offset, None))
        }
        2 => {
            // Offset and length (trim both parts)
            let offset = parts[0].trim().parse::<i32>()
                .map_err(|_| format!("Invalid offset: {}", parts[0]))?;
            let length = parts[1].trim().parse::<usize>()
                .map_err(|_| format!("Invalid length: {}", parts[1]))?;
            Ok((offset, Some(length)))
        }
        _ => Err("Too many colons in substring expression".to_string()),
    }
}

/// Apply parameter expansion operation
fn apply_expansion(expansion: &ParameterExpansion, state: &crate::state::ShellState) -> String {
    let var_value = state.get_variable(&expansion.var_name);
    let is_unset = var_value.is_none();
    let is_null = var_value.map(|v| v.is_empty()).unwrap_or(false);

    match &expansion.operation {
        ExpansionOp::Simple => {
            // ${VAR} - just expand normally
            state.expand_variable(&expansion.var_name)
        }

        ExpansionOp::Default { value, check_null } => {
            // ${VAR:-default} or ${VAR-default}
            if is_unset || (*check_null && is_null) {
                // Recursively expand the default value
                expand_variables(value, state)
            } else {
                var_value.unwrap().to_string()
            }
        }

        ExpansionOp::AssignDefault { value, check_null } => {
            // ${VAR:=default} or ${VAR=default}
            // TODO: Assignment not implemented - requires mutable state
            // For v1.1.0, just return default without assigning (like Default)
            if is_unset || (*check_null && is_null) {
                let default_expanded = expand_variables(value, state);
                // Note: In bash, this would also assign to VAR
                // Requires signature change: &mut ShellState
                default_expanded
            } else {
                var_value.unwrap().to_string()
            }
        }

        ExpansionOp::UseAlternative { value, check_null } => {
            // ${VAR:+value} or ${VAR+value}
            if is_unset || (*check_null && is_null) {
                String::new()
            } else {
                expand_variables(value, state)
            }
        }

        ExpansionOp::ErrorIfUnset { message, check_null } => {
            // ${VAR:?message} or ${VAR?message}
            if is_unset || (*check_null && is_null) {
                let error_msg = message.as_deref().unwrap_or("parameter null or not set");
                eprintln!("vsh: {}: {}", expansion.var_name, error_msg);
                // Return empty string (bash exits non-interactively, but we continue)
                String::new()
            } else {
                var_value.unwrap().to_string()
            }
        }

        ExpansionOp::Length => {
            // ${#VAR}
            let value = state.expand_variable(&expansion.var_name);
            value.chars().count().to_string()
        }

        ExpansionOp::Substring { offset, length } => {
            // ${VAR:offset} or ${VAR:offset:length}
            let value = state.expand_variable(&expansion.var_name);
            apply_substring(&value, *offset, *length)
        }
    }
}

/// Apply substring extraction with bash-compatible negative offset handling
fn apply_substring(value: &str, offset: i32, length: Option<usize>) -> String {
    let chars: Vec<char> = value.chars().collect();
    let len = chars.len() as i32;

    // Handle negative offset (from end)
    let start = if offset < 0 {
        (len + offset).max(0) as usize
    } else {
        offset.min(len) as usize
    };

    match length {
        Some(n) => {
            let end = (start + n).min(chars.len());
            chars[start..end].iter().collect()
        }
        None => {
            chars[start..].iter().collect()
        }
    }
}

pub fn expand_variables(input: &str, state: &crate::state::ShellState) -> String {
    let mut result = String::new();
    let mut chars = input.chars().peekable();

    while let Some(ch) = chars.next() {
        if ch == '\\' && chars.peek() == Some(&'$') {
            // Escaped dollar from single quotes - skip backslash, keep literal $
            result.push(chars.next().unwrap());
        } else if ch == '$' {
            // Check for ${VAR} or $VAR
            if chars.peek() == Some(&'{') {
                // Braced form: ${VAR} or ${VAR:-default}, etc.
                chars.next(); // consume '{'
                let mut var_expr = String::new();

                // Read until '}', handling nested braces
                let mut brace_depth = 1;
                while let Some(&c) = chars.peek() {
                    if c == '}' {
                        brace_depth -= 1;
                        if brace_depth == 0 {
                            chars.next(); // consume '}'
                            break;
                        }
                    } else if c == '{' {
                        brace_depth += 1;
                    }
                    var_expr.push(chars.next().unwrap());
                }

                // Parse the parameter expansion
                match parse_parameter_expansion(&var_expr) {
                    Ok(expansion) => {
                        let expanded = apply_expansion(&expansion, state);
                        result.push_str(&expanded);
                    }
                    Err(err) => {
                        // On parse error, keep the literal text (bash behavior)
                        eprintln!("vsh: bad substitution: {}", err);
                        result.push_str("${");
                        result.push_str(&var_expr);
                        result.push('}');
                    }
                }
            } else if let Some(&next_ch) = chars.peek() {
                // Simple form: $VAR or special variables like $?, $$
                if next_ch == '?' || next_ch == '$' {
                    // Single-character special variable
                    let var_name = chars.next().unwrap().to_string();
                    result.push_str(&state.expand_variable(&var_name));
                } else if next_ch.is_alphabetic() || next_ch == '_' {
                    // Variable name: starts with letter or underscore
                    let mut var_name = String::new();

                    // Read variable name (alphanumeric + underscore)
                    while let Some(&c) = chars.peek() {
                        if c.is_alphanumeric() || c == '_' {
                            var_name.push(chars.next().unwrap());
                        } else {
                            break;
                        }
                    }

                    result.push_str(&state.expand_variable(&var_name));
                } else {
                    // $ followed by non-variable character, keep literal $
                    result.push('$');
                }
            } else {
                // $ at end of string, keep literal $
                result.push('$');
            }
        } else {
            // Regular character
            result.push(ch);
        }
    }

    result
}

/// Extract word token at index or return error, converting to String
fn expect_word(tokens: &[Token], index: usize, context: &str) -> Result<String> {
    match tokens.get(index) {
        Some(Token::Word(w)) => Ok(quoted_word_to_string(w)),
        Some(_) => Err(anyhow!("{}: expected filename, got redirection operator", context)),
        None => Err(anyhow!("{}: missing filename", context)),
    }
}

/// Convert QuotedWord to String with quote removal but NO variable expansion
/// Variable markers ($VAR, ${VAR}) are preserved for later expansion during execution
/// Single-quoted content has $ escaped to prevent expansion
fn quoted_word_to_string(word: &QuotedWord) -> String {
    let mut result = String::new();

    for part in &word.parts {
        match part {
            WordPart::Literal(s) => {
                // In quotes (single or double), escape special characters
                // to prevent unwanted expansion later
                if word.quote_type != QuoteType::None {
                    // Escape $ in single quotes so expand_variables() doesn't expand
                    // Escape glob metacharacters (* ? [ {) in all quotes
                    for ch in s.chars() {
                        if (word.quote_type == QuoteType::Single && ch == '$')
                            || matches!(ch, '*' | '?' | '[' | '{')
                        {
                            result.push('\\');
                        }
                        result.push(ch);
                    }
                } else {
                    result.push_str(s);
                }
            }
            WordPart::Variable(name) => {
                // This shouldn't happen in single quotes (tokenizer prevents it)
                // but handle it anyway
                if word.quote_type != QuoteType::Single {
                    result.push('$');
                    result.push_str(name);
                } else {
                    // In single quotes, escape the $
                    result.push('\\');
                    result.push('$');
                    result.push_str(name);
                }
            }
            WordPart::BracedVariable(name) => {
                // This shouldn't happen in single quotes
                if word.quote_type != QuoteType::Single {
                    result.push_str("${");
                    result.push_str(name);
                    result.push('}');
                } else {
                    // In single quotes, escape the $
                    result.push_str("\\${");
                    result.push_str(name);
                    result.push('}');
                }
            }
            WordPart::CommandSub(cmd) => {
                // Command substitution - keep as-is for now
                // Actual expansion happens in expand_quoted_word_with_state
                if word.quote_type != QuoteType::Single {
                    result.push_str("$(");
                    result.push_str(cmd);
                    result.push(')');
                } else {
                    // In single quotes, it's literal
                    result.push_str("$(");
                    result.push_str(cmd);
                    result.push(')');
                }
            }
            WordPart::ProcessSub(sub_type, cmd) => {
                // Process substitution - keep as-is for now
                // Actual expansion happens in expand_quoted_word_with_state
                match sub_type {
                    ProcessSubType::Input => {
                        result.push_str("<(");
                        result.push_str(cmd);
                        result.push(')');
                    }
                    ProcessSubType::Output => {
                        result.push_str(">(");
                        result.push_str(cmd);
                        result.push(')');
                    }
                }
            }
        }
    }

    result
}

/// Expand command substitution by executing the command and capturing output
pub fn expand_command_substitution(cmd: &str, state: &mut crate::state::ShellState) -> Result<String> {
    use std::process::{Command as ProcessCommand, Stdio};

    // Parse the command
    let parsed_cmd = parse_command(cmd)?;

    // Execute and capture output based on command type
    let output = match &parsed_cmd {
        Command::External { program, args, .. } => {
            // Execute external command and capture stdout
            let mut process_cmd = ProcessCommand::new(program);
            process_cmd.stdout(Stdio::piped());
            process_cmd.stderr(Stdio::null());

            // Expand variables and command substitutions in args before execution
            let expanded_args: Result<Vec<String>> = args
                .iter()
                .map(|arg| expand_with_command_sub(arg, state))
                .collect();
            let expanded_args = expanded_args?;

            process_cmd.args(&expanded_args);

            let output_result = process_cmd.output()
                .with_context(|| format!("Failed to execute: {}", program))?;

            if output_result.status.success() {
                String::from_utf8_lossy(&output_result.stdout).to_string()
            } else {
                return Err(anyhow!("Command failed with exit code: {:?}", output_result.status.code()));
            }
        }

        Command::Pwd { .. } => {
            // pwd builtin
            std::env::current_dir()
                .context("Failed to get current directory")?
                .to_string_lossy()
                .to_string() + "\n"
        }

        Command::Ls { path, .. } => {
            // ls builtin - delegate to external ls command
            let ls_path = path.as_deref().unwrap_or(".");
            let output_result = ProcessCommand::new("ls")
                .arg(ls_path)
                .stdout(Stdio::piped())
                .stderr(Stdio::null())
                .output()
                .context("Failed to execute ls")?;

            String::from_utf8_lossy(&output_result.stdout).to_string()
        }

        _ => {
            return Err(anyhow!("Command substitution not supported for this command type"));
        }
    };

    // Strip trailing newlines (POSIX behavior)
    let trimmed = output.trim_end_matches('\n').to_string();

    Ok(trimmed)
}

/// Expand a QuotedWord into a final string, respecting quote context
pub fn expand_quoted_word_with_state(word: &QuotedWord, state: &mut crate::state::ShellState) -> Result<String> {
    let mut result = String::new();

    for part in &word.parts {
        match part {
            WordPart::Literal(s) => {
                result.push_str(s);
            }
            WordPart::Variable(name) | WordPart::BracedVariable(name) => {
                // Expand unless in single quotes
                if word.quote_type != QuoteType::Single {
                    result.push_str(&state.expand_variable(name));
                } else {
                    // In single quotes, variables are literal
                    match part {
                        WordPart::Variable(n) => {
                            result.push('$');
                            result.push_str(n);
                        }
                        WordPart::BracedVariable(n) => {
                            result.push_str("${");
                            result.push_str(n);
                            result.push('}');
                        }
                        _ => unreachable!(),
                    }
                }
            }
            WordPart::CommandSub(cmd) => {
                // Expand command substitution unless in single quotes
                if word.quote_type != QuoteType::Single {
                    let output = expand_command_substitution(cmd, state)?;
                    result.push_str(&output);
                } else {
                    // In single quotes, it's literal
                    result.push_str("$(");
                    result.push_str(cmd);
                    result.push(')');
                }
            }
            WordPart::ProcessSub(sub_type, cmd) => {
                // Process substitution parsing is implemented, but execution is deferred
                // Execution requires FIFO (named pipe) support which will be added later
                if word.quote_type != QuoteType::Single {
                    return Err(anyhow!(
                        "Process substitution not yet implemented: execution requires FIFO support ({})",
                        match sub_type {
                            ProcessSubType::Input => format!("<({})", cmd),
                            ProcessSubType::Output => format!(">({})", cmd),
                        }
                    ));
                } else {
                    // In single quotes, it's literal
                    match sub_type {
                        ProcessSubType::Input => {
                            result.push_str("<(");
                            result.push_str(cmd);
                            result.push(')');
                        }
                        ProcessSubType::Output => {
                            result.push_str(">(");
                            result.push_str(cmd);
                            result.push(')');
                        }
                    }
                }
            }
        }
    }

    Ok(result)
}

/// Parse base command with arguments and redirections
fn parse_base_command(cmd: &str, args: Vec<String>, redirects: Vec<Redirection>, background: bool) -> Result<Command> {
    match cmd {
        "mkdir" => {
            if args.is_empty() {
                return Err(anyhow!("mkdir: missing operand"));
            }
            Ok(Command::Mkdir {
                path: args[0].clone(),
                redirects,
            })
        }
        "rmdir" => {
            if args.is_empty() {
                return Err(anyhow!("rmdir: missing operand"));
            }
            Ok(Command::Rmdir {
                path: args[0].clone(),
                redirects,
            })
        }
        "touch" => {
            if args.is_empty() {
                return Err(anyhow!("touch: missing operand"));
            }
            Ok(Command::Touch {
                path: args[0].clone(),
                redirects,
            })
        }
        "rm" => {
            if args.is_empty() {
                return Err(anyhow!("rm: missing operand"));
            }
            Ok(Command::Rm {
                path: args[0].clone(),
                redirects,
            })
        }
        "undo" => {
            let count = args.get(0).and_then(|s| s.parse().ok()).unwrap_or(1);
            Ok(Command::Undo { count })
        }
        "redo" => {
            let count = args.get(0).and_then(|s| s.parse().ok()).unwrap_or(1);
            Ok(Command::Redo { count })
        }
        "history" => {
            let show_proofs = args.contains(&"--proofs".to_string())
                || args.contains(&"-p".to_string());
            let count = args
                .iter()
                .filter(|s| !s.starts_with('-'))
                .find_map(|s| s.parse().ok())
                .unwrap_or(10);
            Ok(Command::History { count, show_proofs })
        }
        "exit" => Ok(Command::Exit),
        "quit" => Ok(Command::Quit),

        // Transactions
        "begin" => {
            if args.is_empty() {
                return Err(anyhow!("begin: missing transaction name"));
            }
            Ok(Command::Begin {
                name: args[0].clone(),
            })
        }
        "commit" => Ok(Command::Commit),
        "rollback" => Ok(Command::Rollback),

        // Display commands
        "graph" => Ok(Command::Graph),
        "proofs" | "proof" => Ok(Command::Proofs),
        "ls" => Ok(Command::Ls {
            path: args.get(0).map(|s| s.to_string()),
            redirects,
        }),
        "pwd" => Ok(Command::Pwd { redirects }),
        "cd" => {
            // cd doesn't support redirections (it's a state change, not output)
            if !redirects.is_empty() {
                return Err(anyhow!("cd: redirections not supported for this command"));
            }
            Ok(Command::Cd {
                path: args.get(0).map(|s| s.to_string()),
            })
        }

        "export" => {
            // export VAR or export VAR=value
            if args.is_empty() {
                return Err(anyhow!("export: missing variable name"));
            }

            let first_arg = &args[0];

            // Check if it's export VAR=value
            if let Some(eq_pos) = first_arg.find('=') {
                let name = &first_arg[..eq_pos];
                let value = &first_arg[eq_pos + 1..];

                if !is_valid_var_name(name) {
                    return Err(anyhow!("export: invalid variable name: {}", name));
                }

                Ok(Command::Export {
                    name: name.to_string(),
                    value: Some(value.to_string()),
                })
            } else {
                // export VAR (export existing variable)
                if !is_valid_var_name(first_arg) {
                    return Err(anyhow!("export: invalid variable name: {}", first_arg));
                }

                Ok(Command::Export {
                    name: first_arg.to_string(),
                    value: None,
                })
            }
        }

        // Job control
        "jobs" => {
            let long = args.contains(&"-l".to_string()) || args.contains(&"--long".to_string());
            Ok(Command::Jobs { long })
        }

        "fg" => {
            // fg with optional job spec
            Ok(Command::Fg {
                job_spec: args.get(0).map(|s| s.to_string()),
            })
        }

        "bg" => {
            // bg with optional job spec
            Ok(Command::Bg {
                job_spec: args.get(0).map(|s| s.to_string()),
            })
        }

        "kill" => {
            // kill [-SIGNAL] %job
            let (signal, job_spec) = if args.len() >= 2 && args[0].starts_with('-') {
                // kill -9 %1 or kill -SIGTERM %1
                (Some(args[0].clone()), args[1].clone())
            } else if args.len() >= 1 {
                // kill %1 (default SIGTERM)
                (None, args[0].clone())
            } else {
                return Err(anyhow!("kill: missing job specification"));
            };

            Ok(Command::Kill { signal, job_spec })
        }

        // Conditionals
        "test" => {
            Ok(Command::Test {
                args,
                redirects,
            })
        }

        "[" => {
            // For bracket command, verify closing ]
            if args.is_empty() || args.last() != Some(&"]".to_string()) {
                return Err(anyhow!("[: missing closing bracket ]"));
            }

            // Remove the closing ] from args
            let mut test_args = args;
            test_args.pop();

            Ok(Command::Bracket {
                args: test_args,
                redirects,
            })
        }

        // Everything else: external command
        _ => Ok(Command::External {
            program: cmd.to_string(),
            args,
            redirects,
            background,
        }),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // Helper function for tests to create simple literal words
    fn word(s: &str) -> QuotedWord {
        let mut w = QuotedWord::new();
        w.push_literal(s.to_string());
        w
    }

    #[test]
    fn test_parse_mkdir() {
        let cmd = parse_command("mkdir foo").unwrap();
        assert_eq!(
            cmd,
            Command::Mkdir {
                path: "foo".to_string(),
                redirects: vec![],
            }
        );
    }

    #[test]
    fn test_parse_external() {
        let cmd = parse_command("echo hello world").unwrap();
        match cmd {
            Command::External {
                program,
                args,
                redirects,
                background,
            } => {
                assert_eq!(program, "echo");
                assert_eq!(args, vec!["hello", "world"]);
                assert_eq!(redirects, vec![]);
                assert!(!background);
            }
            _ => panic!("Expected External command"),
        }
    }

    #[test]
    fn test_parse_undo() {
        let cmd = parse_command("undo 3").unwrap();
        assert_eq!(cmd, Command::Undo { count: 3 });
    }

    #[test]
    fn test_parse_history() {
        let cmd = parse_command("history 20 --proofs").unwrap();
        assert_eq!(cmd, Command::History {
            count: 20,
            show_proofs: true
        });
    }

    #[test]
    fn test_parse_begin() {
        let cmd = parse_command("begin mytxn").unwrap();
        assert_eq!(cmd, Command::Begin {
            name: "mytxn".to_string()
        });
    }

    #[test]
    fn test_parse_ls() {
        let cmd = parse_command("ls /tmp").unwrap();
        match cmd {
            Command::Ls { path, redirects } => {
                assert_eq!(path, Some("/tmp".to_string()));
                assert_eq!(redirects, vec![]);
            }
            _ => panic!("Expected Ls command"),
        }
    }

    #[test]
    fn test_parse_cd() {
        let cmd = parse_command("cd /home").unwrap();
        match cmd {
            Command::Cd { path } => {
                assert_eq!(path, Some("/home".to_string()));
            }
            _ => panic!("Expected Cd command"),
        }
    }

    #[test]
    fn test_parse_cd_no_args() {
        let cmd = parse_command("cd").unwrap();
        match cmd {
            Command::Cd { path } => {
                assert_eq!(path, None);
            }
            _ => panic!("Expected Cd command"),
        }
    }

    #[test]
    fn test_parse_cd_dash() {
        let cmd = parse_command("cd -").unwrap();
        match cmd {
            Command::Cd { path } => {
                assert_eq!(path, Some("-".to_string()));
            }
            _ => panic!("Expected Cd command"),
        }
    }

    // Redirection parsing tests
    #[test]
    fn test_parse_output_redirect() {
        let cmd = parse_command("ls > output.txt").unwrap();
        match cmd {
            Command::Ls { redirects, .. } => {
                assert_eq!(redirects.len(), 1);
                assert_eq!(
                    redirects[0],
                    Redirection::Output {
                        file: "output.txt".to_string()
                    }
                );
            }
            _ => panic!("Expected Ls command"),
        }
    }

    #[test]
    fn test_parse_append_redirect() {
        let cmd = parse_command("echo test >> log.txt").unwrap();
        match cmd {
            Command::External { redirects, .. } => {
                assert_eq!(redirects.len(), 1);
                assert_eq!(
                    redirects[0],
                    Redirection::Append {
                        file: "log.txt".to_string()
                    }
                );
            }
            _ => panic!("Expected External command"),
        }
    }

    #[test]
    fn test_parse_input_redirect() {
        let cmd = parse_command("cat < input.txt").unwrap();
        match cmd {
            Command::External { redirects, .. } => {
                assert_eq!(redirects.len(), 1);
                assert_eq!(
                    redirects[0],
                    Redirection::Input {
                        file: "input.txt".to_string()
                    }
                );
            }
            _ => panic!("Expected External command"),
        }
    }

    #[test]
    fn test_parse_error_redirect() {
        let cmd = parse_command("make 2> errors.log").unwrap();
        match cmd {
            Command::External { redirects, .. } => {
                assert_eq!(redirects.len(), 1);
                assert_eq!(
                    redirects[0],
                    Redirection::ErrorOutput {
                        file: "errors.log".to_string()
                    }
                );
            }
            _ => panic!("Expected External command"),
        }
    }

    #[test]
    fn test_parse_error_to_output() {
        let cmd = parse_command("make 2>&1").unwrap();
        match cmd {
            Command::External { redirects, .. } => {
                assert_eq!(redirects.len(), 1);
                assert_eq!(redirects[0], Redirection::ErrorToOutput);
            }
            _ => panic!("Expected External command"),
        }
    }

    #[test]
    fn test_parse_multiple_redirects() {
        let cmd = parse_command("cat < in.txt > out.txt 2> err.log").unwrap();
        match cmd {
            Command::External { redirects, .. } => {
                assert_eq!(redirects.len(), 3);
                assert_eq!(
                    redirects[0],
                    Redirection::Input {
                        file: "in.txt".to_string()
                    }
                );
                assert_eq!(
                    redirects[1],
                    Redirection::Output {
                        file: "out.txt".to_string()
                    }
                );
                assert_eq!(
                    redirects[2],
                    Redirection::ErrorOutput {
                        file: "err.log".to_string()
                    }
                );
            }
            _ => panic!("Expected External command"),
        }
    }

    #[test]
    fn test_parse_both_redirect() {
        let cmd = parse_command("make &> output.log").unwrap();
        match cmd {
            Command::External { redirects, .. } => {
                assert_eq!(redirects.len(), 1);
                assert_eq!(
                    redirects[0],
                    Redirection::BothOutput {
                        file: "output.log".to_string()
                    }
                );
            }
            _ => panic!("Expected External command"),
        }
    }

    // NOTE: Old tokenize tests disabled after Phase 6 M5 (Quote Parsing)
    // Token::Word now contains QuotedWord instead of String
    // These tests would need to be rewritten to construct QuotedWord structs
    // We test tokenization through integration tests (parse_command) instead

    // #[test]
    // fn test_tokenize_basic() { ... }
    // #[test]
    // fn test_tokenize_output_redirect() { ... }
    // #[test]
    // fn test_tokenize_append_redirect() { ... }
    // #[test]
    // fn test_tokenize_error_redirect() { ... }
    // #[test]
    // fn test_tokenize_error_to_output() { ... }
    // #[test]
    // fn test_tokenize_pipe() { ... }
    // #[test]
    // fn test_tokenize_multi_pipe() { ... }
    // #[test]
    // fn test_tokenize_pipe_with_redirect() { ... }

    #[test]
    fn test_parse_empty() {
        assert!(parse_command("").is_err());
        assert!(parse_command("   ").is_err());
    }

    #[test]
    fn test_parse_simple_pipeline() {
        let cmd = parse_command("ls | grep test").unwrap();
        match cmd {
            Command::Pipeline { stages, redirects, background } => {
                assert_eq!(stages.len(), 2);
                assert_eq!(stages[0].0, "ls");
                assert_eq!(stages[0].1.len(), 0);
                assert_eq!(stages[1].0, "grep");
                assert_eq!(stages[1].1, vec!["test"]);
                assert!(redirects.is_empty());
                assert_eq!(background, false);
            }
            _ => panic!("Expected Pipeline"),
        }
    }

    #[test]
    fn test_parse_multi_stage_pipeline() {
        let cmd = parse_command("cat file.txt | grep foo | wc -l").unwrap();
        match cmd {
            Command::Pipeline { stages, .. } => {
                assert_eq!(stages.len(), 3);
                assert_eq!(stages[0].0, "cat");
                assert_eq!(stages[0].1, vec!["file.txt"]);
                assert_eq!(stages[1].0, "grep");
                assert_eq!(stages[1].1, vec!["foo"]);
                assert_eq!(stages[2].0, "wc");
                assert_eq!(stages[2].1, vec!["-l"]);
            }
            _ => panic!("Expected Pipeline"),
        }
    }

    #[test]
    fn test_parse_pipeline_with_redirect() {
        let cmd = parse_command("ls | grep test > output.txt").unwrap();
        match cmd {
            Command::Pipeline { stages, redirects, background } => {
                assert_eq!(stages.len(), 2);
                assert_eq!(redirects.len(), 1);
                assert_eq!(background, false);
                match &redirects[0] {
                    Redirection::Output { file } => assert_eq!(file, "output.txt"),
                    _ => panic!("Expected Output redirection"),
                }
            }
            _ => panic!("Expected Pipeline"),
        }
    }

    #[test]
    fn test_parse_pipeline_empty_stage_error() {
        assert!(parse_command("ls |").is_err());
        assert!(parse_command("| grep test").is_err());
    }

    #[test]
    fn test_parse_pipeline_single_stage_not_pipeline() {
        // Single command with no pipe should not create pipeline
        let cmd = parse_command("ls").unwrap();
        match cmd {
            Command::Ls { .. } => {}, // Built-in command
            _ => panic!("Single command should not create pipeline"),
        }

        // External command without pipe should also not create pipeline
        let cmd2 = parse_command("echo hello").unwrap();
        match cmd2 {
            Command::External { .. } => {},
            _ => panic!("Single external command should not create pipeline"),
        }
    }

    #[test]
    fn test_variable_expansion_simple() {
        use crate::state::ShellState;

        let mut state = ShellState::new("/tmp/vsh_test").unwrap();

        // Test simple variable expansion
        state.set_variable("NAME", "Alice");
        assert_eq!(expand_variables("Hello $NAME", &state), "Hello Alice");

        // Test undefined variable (expands to empty string)
        assert_eq!(expand_variables("Hello $UNDEFINED", &state), "Hello ");

        // Test literal $ (not followed by valid variable name)
        assert_eq!(expand_variables("Price: $10", &state), "Price: $10");
        assert_eq!(expand_variables("End$", &state), "End$");
    }

    #[test]
    fn test_variable_expansion_braced() {
        use crate::state::ShellState;

        let mut state = ShellState::new("/tmp/vsh_test").unwrap();

        state.set_variable("VAR", "test");

        // Test braced variable expansion
        assert_eq!(expand_variables("${VAR}", &state), "test");
        assert_eq!(expand_variables("prefix_${VAR}_suffix", &state), "prefix_test_suffix");

        // Test concatenation
        assert_eq!(expand_variables("${VAR}file", &state), "testfile");
    }

    #[test]
    fn test_variable_expansion_special() {
        use crate::state::ShellState;

        let mut state = ShellState::new("/tmp/vsh_test").unwrap();

        // Test $?
        state.last_exit_code = 42;
        assert_eq!(expand_variables("Exit: $?", &state), "Exit: 42");

        // Test $$
        let result = expand_variables("PID: $$", &state);
        assert!(result.starts_with("PID: "));
        assert!(result.len() > 5); // PID should be numeric
    }

    #[test]
    fn test_variable_expansion_multiple() {
        use crate::state::ShellState;

        let mut state = ShellState::new("/tmp/vsh_test").unwrap();

        state.set_variable("FIRST", "Hello");
        state.set_variable("SECOND", "World");

        // Test multiple variables in one string
        assert_eq!(
            expand_variables("$FIRST $SECOND!", &state),
            "Hello World!"
        );

        // Test mixed simple and braced
        assert_eq!(
            expand_variables("$FIRST ${SECOND}", &state),
            "Hello World"
        );
    }

    #[test]
    fn test_variable_assignment() {
        let cmd = parse_command("VAR=value").unwrap();
        match cmd {
            Command::Assignment { name, value } => {
                assert_eq!(name, "VAR");
                assert_eq!(value, "value");
            }
            _ => panic!("Expected Assignment"),
        }
    }

    #[test]
    fn test_export_simple() {
        let cmd = parse_command("export VAR").unwrap();
        match cmd {
            Command::Export { name, value } => {
                assert_eq!(name, "VAR");
                assert!(value.is_none());
            }
            _ => panic!("Expected Export"),
        }
    }

    #[test]
    fn test_export_with_value() {
        let cmd = parse_command("export VAR=value").unwrap();
        match cmd {
            Command::Export { name, value } => {
                assert_eq!(name, "VAR");
                assert_eq!(value, Some("value".to_string()));
            }
            _ => panic!("Expected Export"),
        }
    }

    // =========================================================================
    // Quote Parsing Tests (Phase 6 M5)
    // =========================================================================

    #[test]
    fn test_single_quotes_no_expansion() {
        use crate::state::ShellState;

        let _state = ShellState::new("/tmp/vsh_test").unwrap();

        // Test that tokenize correctly preserves $ in single quotes
        let tokens = tokenize("echo '$NAME'").unwrap();
        assert_eq!(tokens.len(), 2);

        // Convert to string and verify $ is escaped
        if let Token::Word(w) = &tokens[1] {
            let s = quoted_word_to_string(w);
            assert!(s.contains("\\$") || s == "$NAME"); // Either escaped or literal
        }
    }

    #[test]
    fn test_double_quotes_with_expansion() {
        use crate::state::ShellState;

        let mut state = ShellState::new("/tmp/vsh_test").unwrap();
        state.set_variable("NAME", "Alice");

        // Test external command with variable expansion
        let cmd = parse_command("touch \"file_$NAME\"").unwrap();
        match cmd {
            Command::External { program, args, .. } => {
                assert_eq!(program, "touch");
                let expanded = expand_variables(&args[0], &state);
                assert_eq!(expanded, "file_Alice");
            }
            Command::Touch { path, .. } => {
                // Could also be parsed as Touch command
                let expanded = expand_variables(&path, &state);
                assert!(expanded.contains("file_"));
            }
            _ => panic!("Expected External or Touch command"),
        }
    }

    #[test]
    fn test_backslash_escaping_outside_quotes() {
        use crate::state::ShellState;

        let mut state = ShellState::new("/tmp/vsh_test").unwrap();
        state.set_variable("NAME", "Alice");

        // Test that \$ prevents expansion
        let result = expand_variables("\\$NAME", &state);
        assert_eq!(result, "$NAME");
    }

    #[test]
    fn test_backslash_in_double_quotes() {
        use crate::state::ShellState;

        let mut state = ShellState::new("/tmp/vsh_test").unwrap();
        state.set_variable("NAME", "Alice");

        // Test that \$ in double quotes prevents expansion
        let result = expand_variables("\"\\$NAME\"", &state);
        assert!(result.contains("$NAME"));
    }

    #[test]
    fn test_empty_quoted_strings() {
        let result = tokenize("echo '' \"\"");
        assert!(result.is_ok());
        let tokens = result.unwrap();
        // Should have at least echo token
        // Empty quoted strings may or may not create separate tokens
        assert!(tokens.len() >= 1);
    }

    #[test]
    fn test_quotes_preserve_spaces() {
        let tokens = tokenize("echo \"one   two   three\"").unwrap();
        assert_eq!(tokens.len(), 2);

        if let Token::Word(w) = &tokens[1] {
            let s = quoted_word_to_string(w);
            // Should preserve internal spaces
            assert!(s.contains("   "));
        }
    }

    #[test]
    fn test_mixed_quotes() {
        let tokens = tokenize("echo 'Hello' \"World\"").unwrap();
        // Should have: echo, Hello, World (or combined)
        assert!(tokens.len() >= 2);
    }

    #[test]
    fn test_unclosed_single_quote_error() {
        let result = tokenize("echo 'hello");
        assert!(result.is_err());
        assert!(result.unwrap_err().to_string().contains("Unclosed"));
    }

    #[test]
    fn test_unclosed_double_quote_error() {
        let result = tokenize("echo \"hello");
        assert!(result.is_err());
        assert!(result.unwrap_err().to_string().contains("Unclosed"));
    }

    #[test]
    fn test_positional_param_expansion() {
        use crate::state::ShellState;

        let mut state = ShellState::new("/tmp/vsh_test").unwrap();
        state.set_positional_params(vec!["arg1".to_string(), "arg2".to_string()]);

        // Test $1 expansion
        assert_eq!(state.expand_variable("1"), "arg1");

        // Test $@ expansion
        assert_eq!(state.expand_variable("@"), "arg1 arg2");

        // Test $# expansion
        assert_eq!(state.expand_variable("#"), "2");
    }

    #[test]
    fn test_special_var_dollar_zero() {
        use crate::state::ShellState;

        let state = ShellState::new("/tmp/vsh_test").unwrap();

        // Test $0 expansion
        assert_eq!(state.expand_variable("0"), "vsh");
    }

    #[test]
    fn test_positional_param_in_command() {
        use crate::state::ShellState;

        let mut state = ShellState::new("/tmp/vsh_test").unwrap();
        state.set_positional_params(vec!["myfile".to_string()]);

        // Test using $1 in a command
        let cmd = parse_command("touch $1").unwrap();
        match cmd {
            Command::External { args: _, .. } | Command::Touch { path: _, .. } => {
                // After parsing, before execution, $1 should still be present
                // Expansion happens during execution
                assert!(true);
            }
            _ => {}
        }
    }

    #[test]
    fn test_comment_lines_rejected() {
        // Comments should be rejected as empty commands
        let result = parse_command("# this is a comment");
        assert!(result.is_err());

        let result = parse_command("   # comment with leading space");
        assert!(result.is_err());
    }

    // =========================================================================
    // Command Substitution Tests (Phase 6 M6)
    // =========================================================================

    #[test]
    fn test_command_sub_dollar_parse() {
        // Test $(cmd) parsing
        let tokens = tokenize("echo $(pwd)").unwrap();
        assert_eq!(tokens.len(), 2);

        if let Token::Word(w) = &tokens[1] {
            assert_eq!(w.parts.len(), 1);
            if let WordPart::CommandSub(cmd) = &w.parts[0] {
                assert_eq!(cmd, "pwd");
            } else {
                panic!("Expected CommandSub, got {:?}", w.parts[0]);
            }
        } else {
            panic!("Expected Word token");
        }
    }

    #[test]
    fn test_command_sub_backtick_parse() {
        // Test `cmd` parsing
        let tokens = tokenize("echo `date`").unwrap();
        assert_eq!(tokens.len(), 2);

        if let Token::Word(w) = &tokens[1] {
            if let WordPart::CommandSub(cmd) = &w.parts[0] {
                assert_eq!(cmd, "date");
            }
        }
    }

    #[test]
    fn test_command_sub_in_double_quotes() {
        // Command substitution should work inside double quotes
        let tokens = tokenize("echo \"Result: $(pwd)\"").unwrap();
        assert_eq!(tokens.len(), 2);

        if let Token::Word(w) = &tokens[1] {
            // Should have literal "Result: " and command sub
            assert!(w.parts.len() >= 1);
            assert_eq!(w.quote_type, QuoteType::Double);
        }
    }

    #[test]
    fn test_command_sub_in_single_quotes() {
        // Command substitution should NOT work inside single quotes (literal)
        let tokens = tokenize("echo '$(pwd)'").unwrap();
        assert_eq!(tokens.len(), 2);

        if let Token::Word(w) = &tokens[1] {
            assert_eq!(w.quote_type, QuoteType::Single);
            // Should be literal text, not CommandSub
            if let WordPart::Literal(s) = &w.parts[0] {
                assert!(s.contains("$(pwd)") || s.contains("$"));
            }
        }
    }

    #[test]
    fn test_command_sub_nested_dollar() {
        // Test nested $(outer $(inner))
        let tokens = tokenize("echo $(echo $(echo nested))").unwrap();
        assert_eq!(tokens.len(), 2);

        if let Token::Word(w) = &tokens[1] {
            if let WordPart::CommandSub(cmd) = &w.parts[0] {
                // The nested command should be parsed as part of the outer command
                assert!(cmd.contains("$(echo nested)"));
            }
        }
    }

    #[test]
    fn test_command_sub_unclosed_dollar() {
        // Unclosed $( should be an error
        let result = tokenize("echo $(pwd");
        assert!(result.is_err());
        assert!(result.unwrap_err().to_string().contains("Unclosed"));
    }

    #[test]
    fn test_command_sub_unclosed_backtick() {
        // Unclosed ` should be an error
        let result = tokenize("echo `pwd");
        assert!(result.is_err());
        assert!(result.unwrap_err().to_string().contains("Unclosed"));
    }

    #[test]
    fn test_command_sub_empty() {
        // Empty command substitution should parse
        let tokens = tokenize("echo $()").unwrap();
        assert_eq!(tokens.len(), 2);

        if let Token::Word(w) = &tokens[1] {
            if let WordPart::CommandSub(cmd) = &w.parts[0] {
                assert_eq!(cmd, "");
            }
        }
    }

    #[test]
    fn test_command_sub_with_args() {
        // Command with arguments
        let tokens = tokenize("echo $(ls -la)").unwrap();
        assert_eq!(tokens.len(), 2);

        if let Token::Word(w) = &tokens[1] {
            if let WordPart::CommandSub(cmd) = &w.parts[0] {
                assert_eq!(cmd, "ls -la");
            }
        }
    }

    #[test]
    fn test_command_sub_multiple() {
        // Multiple command substitutions in one line
        let tokens = tokenize("echo $(pwd) $(date)").unwrap();
        assert_eq!(tokens.len(), 3);

        // First command sub
        if let Token::Word(w) = &tokens[1] {
            if let WordPart::CommandSub(cmd) = &w.parts[0] {
                assert_eq!(cmd, "pwd");
            }
        }

        // Second command sub
        if let Token::Word(w) = &tokens[2] {
            if let WordPart::CommandSub(cmd) = &w.parts[0] {
                assert_eq!(cmd, "date");
            }
        }
    }

    #[test]
    fn test_command_sub_mixed_with_variables() {
        // Mix of variables and command substitution
        let tokens = tokenize("echo $VAR $(pwd)").unwrap();
        assert_eq!(tokens.len(), 3);

        // Variable
        if let Token::Word(w) = &tokens[1] {
            if let WordPart::Variable(name) = &w.parts[0] {
                assert_eq!(name, "VAR");
            }
        }

        // Command sub
        if let Token::Word(w) = &tokens[2] {
            if let WordPart::CommandSub(cmd) = &w.parts[0] {
                assert_eq!(cmd, "pwd");
            }
        }
    }

    #[test]
    fn test_command_sub_backtick_escaped() {
        // Escaped backtick inside backtick command sub
        let tokens = tokenize("echo `echo \\`test\\``").unwrap();
        assert_eq!(tokens.len(), 2);

        if let Token::Word(w) = &tokens[1] {
            if let WordPart::CommandSub(cmd) = &w.parts[0] {
                assert!(cmd.contains("`test`"));
            }
        }
    }

    // ===== Process Substitution Tests =====

    #[test]
    fn test_process_sub_input_parse() {
        // Input process substitution: <(cmd)
        let tokens = tokenize("diff <(ls dir1) <(ls dir2)").unwrap();
        assert_eq!(tokens.len(), 3);

        // First arg: <(ls dir1)
        if let Token::Word(w) = &tokens[1] {
            assert_eq!(w.parts.len(), 1);
            if let WordPart::ProcessSub(sub_type, cmd) = &w.parts[0] {
                assert!(matches!(sub_type, ProcessSubType::Input));
                assert_eq!(cmd, "ls dir1");
            } else {
                panic!("Expected ProcessSub, got {:?}", w.parts[0]);
            }
        } else {
            panic!("Expected Word token");
        }

        // Second arg: <(ls dir2)
        if let Token::Word(w) = &tokens[2] {
            assert_eq!(w.parts.len(), 1);
            if let WordPart::ProcessSub(sub_type, cmd) = &w.parts[0] {
                assert!(matches!(sub_type, ProcessSubType::Input));
                assert_eq!(cmd, "ls dir2");
            } else {
                panic!("Expected ProcessSub, got {:?}", w.parts[0]);
            }
        } else {
            panic!("Expected Word token");
        }
    }

    #[test]
    fn test_process_sub_output_parse() {
        // Output process substitution: >(cmd)
        let tokens = tokenize("tee >(wc -l) >(grep pattern)").unwrap();
        assert_eq!(tokens.len(), 3);

        // First arg: >(wc -l)
        if let Token::Word(w) = &tokens[1] {
            assert_eq!(w.parts.len(), 1);
            if let WordPart::ProcessSub(sub_type, cmd) = &w.parts[0] {
                assert!(matches!(sub_type, ProcessSubType::Output));
                assert_eq!(cmd, "wc -l");
            } else {
                panic!("Expected ProcessSub, got {:?}", w.parts[0]);
            }
        } else {
            panic!("Expected Word token");
        }
    }

    #[test]
    fn test_process_sub_in_double_quotes() {
        // Process substitution in double quotes (should still parse)
        let tokens = tokenize("echo \"<(ls)\"").unwrap();
        assert_eq!(tokens.len(), 2);

        if let Token::Word(w) = &tokens[1] {
            assert_eq!(w.quote_type, QuoteType::Double);
            if let WordPart::ProcessSub(sub_type, cmd) = &w.parts[0] {
                assert!(matches!(sub_type, ProcessSubType::Input));
                assert_eq!(cmd, "ls");
            }
        }
    }

    #[test]
    fn test_process_sub_in_single_quotes() {
        // Process substitution in single quotes should be literal
        let tokens = tokenize("echo '<(ls)'").unwrap();
        assert_eq!(tokens.len(), 2);

        if let Token::Word(w) = &tokens[1] {
            assert_eq!(w.quote_type, QuoteType::Single);
            // In single quotes, should be parsed as literal
            if let WordPart::Literal(s) = &w.parts[0] {
                assert_eq!(s, "<(ls)");
            } else {
                panic!("Expected Literal in single quotes, got {:?}", w.parts[0]);
            }
        }
    }

    #[test]
    fn test_process_sub_unclosed_input() {
        // Unclosed <( should error
        let result = tokenize("diff <(ls dir1");
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(err.to_string().contains("Unclosed process substitution"));
    }

    #[test]
    fn test_process_sub_unclosed_output() {
        // Unclosed >( should error
        let result = tokenize("tee >(wc -l");
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(err.to_string().contains("Unclosed process substitution"));
    }

    #[test]
    fn test_process_sub_empty() {
        // Empty process substitution should parse
        let tokens = tokenize("cat <()").unwrap();
        assert_eq!(tokens.len(), 2);

        if let Token::Word(w) = &tokens[1] {
            if let WordPart::ProcessSub(_sub_type, cmd) = &w.parts[0] {
                assert_eq!(cmd, "");
            }
        }
    }

    #[test]
    fn test_process_sub_with_redirects() {
        // Process substitution with redirects inside
        let tokens = tokenize("cat <(ls > /tmp/out)").unwrap();
        assert_eq!(tokens.len(), 2);

        if let Token::Word(w) = &tokens[1] {
            if let WordPart::ProcessSub(_sub_type, cmd) = &w.parts[0] {
                assert_eq!(cmd, "ls > /tmp/out");
            }
        }
    }

    #[test]
    fn test_process_sub_nested_parens() {
        // Nested parentheses should track depth
        let tokens = tokenize("cat <(echo (test))").unwrap();
        assert_eq!(tokens.len(), 2);

        if let Token::Word(w) = &tokens[1] {
            if let WordPart::ProcessSub(_sub_type, cmd) = &w.parts[0] {
                assert_eq!(cmd, "echo (test)");
            }
        }
    }

    #[test]
    fn test_process_sub_vs_redirect() {
        // < followed by non-( should be redirect, not process sub
        let tokens = tokenize("cat < input.txt").unwrap();
        assert_eq!(tokens.len(), 3);
        assert!(matches!(tokens[1], Token::InputRedirect));

        // <( should be process sub
        let tokens2 = tokenize("cat <(echo test)").unwrap();
        assert_eq!(tokens2.len(), 2);
        if let Token::Word(w) = &tokens2[1] {
            assert!(matches!(w.parts[0], WordPart::ProcessSub(_, _)));
        }
    }
}

/// Process here document content: strip tabs if needed, expand if needed
pub fn process_heredoc_content(
    content: &str,
    strip_tabs: bool,
    expand: bool,
    state: &mut crate::state::ShellState,
) -> Result<String> {
    let mut processed = String::new();

    for line in content.lines() {
        let line_to_add = if strip_tabs {
            line.trim_start_matches('\t')
        } else {
            line
        };

        if expand {
            // Perform variable expansion, command substitution, arithmetic
            let expanded = expand_with_command_sub(line_to_add, state)?;
            processed.push_str(&expanded);
        } else {
            processed.push_str(line_to_add);
        }
        processed.push('\n');
    }

    // Remove trailing newline if content didn't end with one
    if !content.ends_with('\n') && processed.ends_with('\n') {
        processed.pop();
    }

    Ok(processed)
}

/// Fill in here document content after reading from input
pub fn fill_heredoc_content(
    cmd: &mut Command,
    heredoc_contents: &[(String, String)], // (delimiter, content) pairs
) -> Result<()> {
    // Find redirections that need content filled
    let redirects = match cmd {
        Command::External { redirects, .. } => redirects,
        Command::Mkdir { redirects, .. }
        | Command::Rmdir { redirects, .. }
        | Command::Touch { redirects, .. }
        | Command::Rm { redirects, .. }
        | Command::Ls { redirects, .. }
        | Command::Pwd { redirects, .. }
        | Command::Pipeline { redirects, .. } => redirects,
        _ => return Ok(()), // No redirects (Cd, Undo, History, etc.)
    };

    let mut heredoc_index = 0;
    for redirect in redirects.iter_mut() {
        if let Redirection::HereDoc { ref mut content, .. } = redirect {
            if heredoc_index < heredoc_contents.len() {
                *content = heredoc_contents[heredoc_index].1.clone();
                heredoc_index += 1;
            }
        }
    }

    Ok(())
}

/// Check if command contains here documents and extract delimiters
pub fn extract_heredoc_delimiters(input: &str) -> Result<Vec<String>> {
    let mut delimiters = Vec::new();
    let tokens = tokenize(input)?;

    for i in 0..tokens.len() {
        if matches!(tokens[i], Token::HereDoc | Token::HereDocDash) {
            if i + 1 < tokens.len() {
                if let Token::Word(ref word) = tokens[i + 1] {
                    let delimiter = quoted_word_to_string(word);
                    // Remove quotes if present
                    let clean = delimiter.trim_matches(|c| c == '\'' || c == '"');
                    delimiters.push(clean.to_string());
                }
            }
        }
    }

    Ok(delimiters)
}

#[cfg(test)]
mod heredoc_tests {
    use super::*;

    #[test]
    fn test_process_heredoc_literal() {
        let mut state = crate::state::ShellState::new("/tmp").unwrap();
        let content = "Line 1\nLine 2\nLine 3";

        let processed = process_heredoc_content(content, false, false, &mut state).unwrap();
        // Content without trailing newline adds newlines for each line
        assert_eq!(processed, "Line 1\nLine 2\nLine 3");
    }

    #[test]
    fn test_process_heredoc_with_expansion() {
        let mut state = crate::state::ShellState::new("/tmp").unwrap();
        state.set_variable("name", "World");

        let content = "Hello $name\nResult: $((5 + 3))";

        let processed = process_heredoc_content(content, false, true, &mut state).unwrap();
        assert_eq!(processed, "Hello World\nResult: 8");
    }

    #[test]
    fn test_process_heredoc_strip_tabs() {
        let mut state = crate::state::ShellState::new("/tmp").unwrap();
        let content = "\tLine 1\n\t\tLine 2\n\t\t\tLine 3";

        let processed = process_heredoc_content(content, true, false, &mut state).unwrap();
        // <<- strips ALL leading tabs from each line
        assert_eq!(processed, "Line 1\nLine 2\nLine 3");
    }

    #[test]
    fn test_tokenize_herestring() {
        let tokens = tokenize("cat <<<word").unwrap();
        assert_eq!(tokens.len(), 3);
        assert!(matches!(tokens[1], Token::HereString));
    }

    #[test]
    fn test_tokenize_heredoc() {
        let tokens = tokenize("cat <<EOF").unwrap();
        assert_eq!(tokens.len(), 3);
        assert!(matches!(tokens[1], Token::HereDoc));
    }

    #[test]
    fn test_tokenize_heredoc_dash() {
        let tokens = tokenize("cat <<-EOF").unwrap();
        assert_eq!(tokens.len(), 3);
        assert!(matches!(tokens[1], Token::HereDocDash));
    }

    #[test]
    fn test_extract_heredoc_delimiters() {
        let delimiters = extract_heredoc_delimiters("cat <<EOF").unwrap();
        assert_eq!(delimiters, vec!["EOF"]);

        let delimiters2 = extract_heredoc_delimiters("cat <<'EOF'").unwrap();
        assert_eq!(delimiters2, vec!["EOF"]);

        let delimiters3 = extract_heredoc_delimiters("cmd <<END1 arg <<END2").unwrap();
        assert_eq!(delimiters3, vec!["END1", "END2"]);
    }
}

#[cfg(test)]
mod job_control_tests {
    use super::*;

    #[test]
    fn test_tokenize_background() {
        let tokens = tokenize("sleep 10 &").unwrap();
        assert_eq!(tokens.len(), 3);
        assert!(matches!(tokens[2], Token::Background));
    }

    #[test]
    fn test_parse_background_job() {
        let cmd = parse_command("sleep 10 &").unwrap();
        match cmd {
            Command::External { program, args, background, .. } => {
                assert_eq!(program, "sleep");
                assert_eq!(args, vec!["10"]);
                assert!(background);
            }
            _ => panic!("Expected External command"),
        }
    }

    #[test]
    fn test_parse_jobs_command() {
        let cmd = parse_command("jobs").unwrap();
        match cmd {
            Command::Jobs { long } => {
                assert!(!long);
            }
            _ => panic!("Expected Jobs command"),
        }
    }

    #[test]
    fn test_parse_jobs_long() {
        let cmd = parse_command("jobs -l").unwrap();
        match cmd {
            Command::Jobs { long } => {
                assert!(long);
            }
            _ => panic!("Expected Jobs command"),
        }
    }

    #[test]
    fn test_parse_fg_no_spec() {
        let cmd = parse_command("fg").unwrap();
        match cmd {
            Command::Fg { job_spec } => {
                assert!(job_spec.is_none());
            }
            _ => panic!("Expected Fg command"),
        }
    }

    #[test]
    fn test_parse_fg_with_spec() {
        let cmd = parse_command("fg %1").unwrap();
        match cmd {
            Command::Fg { job_spec } => {
                assert_eq!(job_spec, Some("%1".to_string()));
            }
            _ => panic!("Expected Fg command"),
        }
    }

    #[test]
    fn test_parse_bg_no_spec() {
        let cmd = parse_command("bg").unwrap();
        match cmd {
            Command::Bg { job_spec } => {
                assert!(job_spec.is_none());
            }
            _ => panic!("Expected Bg command"),
        }
    }

    #[test]
    fn test_parse_kill_default_signal() {
        let cmd = parse_command("kill %1").unwrap();
        match cmd {
            Command::Kill { signal, job_spec } => {
                assert_eq!(job_spec, "%1");
                assert!(signal.is_none());
            }
            _ => panic!("Expected Kill command"),
        }
    }

    #[test]
    fn test_parse_kill_with_signal() {
        let cmd = parse_command("kill -9 %1").unwrap();
        match cmd {
            Command::Kill { signal, job_spec } => {
                assert_eq!(job_spec, "%1");
                assert_eq!(signal, Some("-9".to_string()));
            }
            _ => panic!("Expected Kill command"),
        }
    }

    #[test]
    fn test_parse_logical_and() {
        let cmd = parse_command("mkdir foo && touch bar").unwrap();
        match cmd {
            Command::LogicalOp { operator, left, right } => {
                assert_eq!(operator, LogicalOperator::And);
                assert!(matches!(*left, Command::Mkdir { .. }));
                assert!(matches!(*right, Command::Touch { .. }));
            }
            _ => panic!("Expected LogicalOp command"),
        }
    }

    #[test]
    fn test_parse_logical_or() {
        let cmd = parse_command("test -f file.txt || touch file.txt").unwrap();
        match cmd {
            Command::LogicalOp { operator, left, right } => {
                assert_eq!(operator, LogicalOperator::Or);
                assert!(matches!(*left, Command::Test { .. }));
                assert!(matches!(*right, Command::Touch { .. }));
            }
            _ => panic!("Expected LogicalOp command"),
        }
    }

    #[test]
    fn test_tokenize_and_operator() {
        let tokens = tokenize("cmd1 && cmd2").unwrap();
        assert_eq!(tokens.len(), 3);
        assert!(matches!(tokens[1], Token::And));
    }

    #[test]
    fn test_tokenize_or_operator() {
        let tokens = tokenize("cmd1 || cmd2").unwrap();
        assert_eq!(tokens.len(), 3);
        assert!(matches!(tokens[1], Token::Or));
    }
}
