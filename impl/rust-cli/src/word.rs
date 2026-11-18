// SPDX-License-Identifier: MPL-2.0
// Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//! Typed shell words and the word-expansion stage for simple-command arguments.
//!
//! The tokenizer used to flatten each word into a `String` in which quoted
//! glob metacharacters were marked with a backslash (`'*'` became `\*`).
//! Nothing removed those backslashes again, so `echo '*.txt'` printed
//! `\*.txt`, and glob expansion could not tell a quoted `*` from an unquoted
//! one without re-parsing that encoding.
//!
//! A [`Word`] keeps the quoting of every piece instead: each [`Segment`]
//! records whether it was written unquoted, in single or double quotes, or
//! after a backslash. [`expand_words`] then runs the POSIX word-expansion
//! steps on that structure, in this order:
//!
//! 1. tilde expansion (an unquoted `~`, `~/`, `~+`, `~-` at the start),
//!    parameter expansion, command substitution, arithmetic expansion and
//!    process substitution;
//! 2. brace expansion (`{a,b}`) of unquoted literal text;
//! 3. pathname (glob) expansion of the characters that are not quoted;
//! 4. quote removal.
//!
//! # Rules kept from the previous expansion code
//!
//! - A pattern that matches nothing, or is not a valid pattern, stays as the
//!   literal word.
//! - A pattern whose expansion reaches a [`GlobLimits`] limit fails the whole
//!   expansion with the [`GlobLimitExceeded`] error; the caller must not run
//!   the command.
//!
//! # Known differences from POSIX (not changed here)
//!
//! - No field splitting: an unquoted `$X` whose value is `a b` stays one
//!   argument.
//! - An empty word (`''`, or an unquoted expansion that is empty) is dropped
//!   by the tokenizer or kept as an empty argument, as before.
//! - Brace expansion runs after parameter expansion (bash runs it before);
//!   braces that come out of an expansion are not expanded.
//!
//! Only the arguments of external commands, pipeline stages, `echo` and
//! function calls go through this stage so far. Builtin operands, redirection
//! targets, assignments, `case` patterns and `test` arguments still use the
//! older string encoding.

use std::fmt;
use std::path::Path;

use anyhow::{Context, Result};

use crate::glob::{self, GlobLimitExceeded, GlobLimits, GlobUsage};
use crate::parser::ProcessSubType;
use crate::process_sub::ProcessSubstitution;
use crate::state::ShellState;

/// How a piece of a word was written in the source.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Quote {
    /// Not quoted: subject to tilde, brace and glob expansion.
    None,
    /// Inside `'...'`.
    Single,
    /// Inside `"..."`.
    Double,
    /// A single character after an unquoted `\`.
    Backslash,
}

impl Quote {
    fn is_quoted(self) -> bool {
        self != Quote::None
    }
}

/// One piece of a [`Word`].
#[derive(Debug, Clone, PartialEq)]
pub enum Segment {
    /// Literal text.
    Literal { text: String, quote: Quote },
    /// `$NAME` (`braced: false`) or `${EXPR}` (`braced: true`).
    Parameter {
        expr: String,
        braced: bool,
        quote: Quote,
    },
    /// `$(CMD)` or `` `CMD` ``; `$((EXPR))` is stored as the command `(EXPR)`.
    CommandSub { cmd: String, quote: Quote },
    /// `<(CMD)` or `>(CMD)`.
    ProcessSub { kind: ProcessSubType, cmd: String },
}

/// A shell word with the quoting of each of its pieces.
#[derive(Debug, Clone, PartialEq, Default)]
pub struct Word {
    segments: Vec<Segment>,
}

impl Word {
    /// An empty word.
    pub fn new() -> Self {
        Self::default()
    }

    /// A word that is a single unquoted literal.
    ///
    /// # Examples
    /// ```
    /// use vsh::word::Word;
    /// assert_eq!(Word::literal("a.txt").to_string(), "a.txt");
    /// ```
    pub fn literal(text: &str) -> Self {
        let mut word = Self::new();
        for ch in text.chars() {
            word.push_char(ch, Quote::None);
        }
        word
    }

    /// The pieces of the word, in order.
    pub fn segments(&self) -> &[Segment] {
        &self.segments
    }

    /// True when the word has no pieces.
    pub fn is_empty(&self) -> bool {
        self.segments.is_empty()
    }

    /// Append one literal character, merging it into the last piece when that
    /// piece is a literal with the same quoting.
    pub fn push_char(&mut self, ch: char, quote: Quote) {
        if quote != Quote::Backslash {
            if let Some(Segment::Literal { text, quote: last }) = self.segments.last_mut() {
                if *last == quote {
                    text.push(ch);
                    return;
                }
            }
        }
        self.segments.push(Segment::Literal {
            text: ch.to_string(),
            quote,
        });
    }

    /// Append literal text.
    pub fn push_str(&mut self, text: &str, quote: Quote) {
        for ch in text.chars() {
            self.push_char(ch, quote);
        }
    }

    /// Append a parameter expansion.
    pub fn push_parameter(&mut self, expr: String, braced: bool, quote: Quote) {
        self.segments.push(Segment::Parameter {
            expr,
            braced,
            quote,
        });
    }

    /// Append a command substitution.
    pub fn push_command_sub(&mut self, cmd: String, quote: Quote) {
        self.segments.push(Segment::CommandSub { cmd, quote });
    }

    /// Append a process substitution.
    pub fn push_process_sub(&mut self, kind: ProcessSubType, cmd: String) {
        self.segments.push(Segment::ProcessSub { kind, cmd });
    }
}

impl From<&str> for Word {
    fn from(text: &str) -> Self {
        Word::literal(text)
    }
}

/// Write one literal piece back as source with its quoting.
fn fmt_literal(f: &mut fmt::Formatter<'_>, text: &str, quote: Quote) -> fmt::Result {
    match quote {
        Quote::None => f.write_str(text),
        Quote::Backslash => text.chars().try_for_each(|ch| write!(f, "\\{ch}")),
        // `'` cannot appear inside single quotes.
        Quote::Single => write!(f, "'{}'", text.replace('\'', "'\\''")),
        Quote::Double => {
            let mut escaped = String::with_capacity(text.len() + 2);
            for ch in text.chars() {
                if matches!(ch, '"' | '$' | '`' | '\\') {
                    escaped.push('\\');
                }
                escaped.push(ch);
            }
            write!(f, "\"{escaped}\"")
        }
    }
}

/// Writes the word back as shell source that parses to the same word.
impl fmt::Display for Word {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for segment in &self.segments {
            match segment {
                Segment::Literal { text, quote } => fmt_literal(f, text, *quote)?,
                Segment::Parameter {
                    expr,
                    braced,
                    quote,
                } => {
                    let open = if quote.is_quoted() { "\"" } else { "" };
                    if *braced {
                        write!(f, "{open}${{{expr}}}{open}")?;
                    } else {
                        write!(f, "{open}${expr}{open}")?;
                    }
                }
                Segment::CommandSub { cmd, quote } => {
                    let open = if quote.is_quoted() { "\"" } else { "" };
                    write!(f, "{open}$({cmd}){open}")?;
                }
                Segment::ProcessSub { kind, cmd } => match kind {
                    ProcessSubType::Input => write!(f, "<({cmd})")?,
                    ProcessSubType::Output => write!(f, ">({cmd})")?,
                },
            }
        }
        Ok(())
    }
}

/// Compares the source form ([`fmt::Display`]) with `other`.
impl PartialEq<str> for Word {
    fn eq(&self, other: &str) -> bool {
        let source = self.to_string();
        source.as_str() == other
    }
}

impl PartialEq<&str> for Word {
    fn eq(&self, other: &&str) -> bool {
        *self == **other
    }
}

/// Whether process substitutions may be started while expanding.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ProcessSubs {
    /// Start them; the caller cleans them up after the command finishes.
    Allow,
    /// Fail on them, as the code paths without FIFO handling always have.
    Refuse,
}

/// The result of expanding a list of words.
pub struct Expansion {
    /// The arguments, after quote removal.
    pub fields: Vec<String>,
    /// Process substitutions started for these arguments.
    pub process_subs: Vec<ProcessSubstitution>,
}

impl Expansion {
    /// Wait for the process substitutions and remove their FIFOs.
    pub fn cleanup(self) {
        for proc_sub in self.process_subs {
            if let Err(e) = proc_sub.cleanup() {
                eprintln!("Warning: Failed to cleanup process substitution: {}", e);
            }
        }
    }
}

/// Expand words relative to the current directory under the default limits.
///
/// # Errors
/// Fails on an expansion error (a failing command substitution, a refused
/// process substitution) or when a glob reaches a limit
/// ([`GlobLimitExceeded`], reachable with `anyhow::Error::downcast_ref`).
pub fn expand_words(
    words: &[Word],
    state: &mut ShellState,
    process_subs: ProcessSubs,
) -> Result<Expansion> {
    let cwd = std::env::current_dir().context("Failed to get current working directory")?;
    expand_words_in(words, state, process_subs, &cwd, &GlobLimits::DEFAULT)
}

/// [`expand_words`] with an explicit directory for relative patterns and
/// explicit glob limits.
///
/// # Errors
/// As for [`expand_words`].
pub fn expand_words_in(
    words: &[Word],
    state: &mut ShellState,
    process_subs: ProcessSubs,
    cwd: &Path,
    limits: &GlobLimits,
) -> Result<Expansion> {
    let mut expansion = Expansion {
        fields: Vec::new(),
        process_subs: Vec::new(),
    };
    // One glob budget for the whole command: every word and every brace
    // alternative draws on the same limits.
    let mut spent = GlobUsage::default();
    for word in words {
        // On error the substitutions started so far are dropped, and Drop
        // stops them and removes their FIFOs.
        let chars = expand_segments(word, state, process_subs, &mut expansion.process_subs)?;
        glob_fields(&chars, cwd, limits, &mut spent, &mut expansion.fields)?;
    }
    Ok(expansion)
}

/// What later steps may do with a character produced by step 1.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Role {
    /// Quoted text or a tilde result: taken literally.
    Literal,
    /// Unquoted source text: brace and glob expansion apply.
    Source,
    /// Result of an unquoted expansion: glob expansion applies, braces do not.
    Expanded,
}

/// Step 1: tilde, parameter, command, arithmetic and process substitution.
fn expand_segments(
    word: &Word,
    state: &mut ShellState,
    process_subs: ProcessSubs,
    started: &mut Vec<ProcessSubstitution>,
) -> Result<Vec<(char, Role)>> {
    let mut out: Vec<(char, Role)> = Vec::new();
    let push = |out: &mut Vec<(char, Role)>, text: &str, role: Role| {
        out.extend(text.chars().map(|ch| (ch, role)));
    };

    for (index, segment) in word.segments.iter().enumerate() {
        match segment {
            Segment::Literal { text, quote } => {
                if !quote.is_quoted() {
                    if index == 0 && text.starts_with('~') {
                        let (prefix, rest) = text.split_at(text.find('/').unwrap_or(text.len()));
                        let expanded = crate::parser::expand_tilde(prefix);
                        if expanded != prefix {
                            push(&mut out, &expanded, Role::Literal);
                            push(&mut out, rest, Role::Source);
                            continue;
                        }
                    }
                    push(&mut out, text, Role::Source);
                } else {
                    push(&mut out, text, Role::Literal);
                }
            }
            Segment::Parameter {
                expr,
                braced,
                quote,
            } => {
                let source = if *braced {
                    format!("${{{expr}}}")
                } else {
                    format!("${expr}")
                };
                let value = crate::parser::expand_variables(&source, state);
                push(&mut out, &value, expansion_role(*quote));
            }
            Segment::CommandSub { cmd, quote } => {
                let value = crate::parser::expand_with_command_sub(&format!("$({cmd})"), state)?;
                push(&mut out, &value, expansion_role(*quote));
            }
            Segment::ProcessSub { kind, cmd } => {
                if process_subs == ProcessSubs::Refuse {
                    anyhow::bail!(
                        "Process substitution not yet implemented: execution requires FIFO support ({})",
                        Word {
                            segments: vec![segment.clone()]
                        }
                    );
                }
                let mut proc_sub = ProcessSubstitution::create(*kind, cmd.clone(), state)?;
                proc_sub.start(state)?;
                push(
                    &mut out,
                    &proc_sub.fifo_path.to_string_lossy(),
                    Role::Literal,
                );
                started.push(proc_sub);
            }
        }
    }
    Ok(out)
}

fn expansion_role(quote: Quote) -> Role {
    if quote.is_quoted() {
        Role::Literal
    } else {
        Role::Expanded
    }
}

/// Encode step-1 output for [`glob::expand_braces`] and
/// [`glob::contains_glob_pattern`], which both read `\x` as a literal `x`.
fn encode(chars: &[(char, Role)]) -> String {
    let mut out = String::with_capacity(chars.len() * 2);
    for &(ch, role) in chars {
        let literal = match role {
            Role::Literal => true,
            Role::Source => ch == '\\',
            Role::Expanded => matches!(ch, '\\' | '{' | '}' | ','),
        };
        if literal {
            out.push('\\');
        }
        out.push(ch);
    }
    out
}

/// Steps 2 to 4: brace expansion, glob expansion and quote removal.
fn glob_fields(
    chars: &[(char, Role)],
    cwd: &Path,
    limits: &GlobLimits,
    spent: &mut GlobUsage,
    fields: &mut Vec<String>,
) -> Result<()> {
    let encoded = encode(chars);
    for candidate in glob::expand_braces(&encoded) {
        match glob_pattern(&candidate) {
            None => fields.push(remove_quotes(&candidate)),
            Some(pattern) => match glob::expand_glob_continuing(&pattern, cwd, limits, *spent) {
                Ok(found) if !found.paths.is_empty() => {
                    *spent = found.usage;
                    fields.extend(
                        found
                            .paths
                            .iter()
                            .map(|path| path.to_string_lossy().into_owned()),
                    );
                }
                // No match still spent reads.
                Ok(found) => {
                    *spent = found.usage;
                    fields.push(remove_quotes(&candidate));
                }
                // A limit is not "no match": substituting the literal word
                // would run the command on the wrong arguments.
                Err(e) if e.is::<GlobLimitExceeded>() => return Err(e),
                // No match, or not a valid pattern: keep the word (POSIX).
                _ => fields.push(remove_quotes(&candidate)),
            },
        }
    }
    Ok(())
}

/// The pattern for the `glob` crate, or `None` when no `*`, `?` or `[` is
/// left unquoted. Quoted metacharacters are written as one-character classes
/// (`[*]`), the only escape that crate has.
fn glob_pattern(encoded: &str) -> Option<String> {
    let mut pattern = String::with_capacity(encoded.len());
    let mut active = false;
    let mut chars = encoded.chars();
    while let Some(ch) = chars.next() {
        if ch == '\\' {
            if let Some(next) = chars.next() {
                pattern.push_str(&::glob::Pattern::escape(&next.to_string()));
            }
        } else {
            active |= matches!(ch, '*' | '?' | '[');
            pattern.push(ch);
        }
    }
    active.then_some(pattern)
}

/// Quote removal: `\x` becomes `x`.
fn remove_quotes(encoded: &str) -> String {
    let mut out = String::with_capacity(encoded.len());
    let mut chars = encoded.chars();
    while let Some(ch) = chars.next() {
        if ch == '\\' {
            if let Some(next) = chars.next() {
                out.push(next);
            }
        } else {
            out.push(ch);
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    fn word(parts: &[(&str, Quote)]) -> Word {
        let mut w = Word::new();
        for (text, quote) in parts {
            w.push_str(text, *quote);
        }
        w
    }

    fn fixture(names: &[&str]) -> tempfile::TempDir {
        let dir = tempfile::TempDir::new().unwrap();
        for name in names {
            std::fs::write(dir.path().join(name), b"").unwrap();
        }
        dir
    }

    fn expand_in(dir: &Path, words: &[Word]) -> Vec<String> {
        let mut state = ShellState::new(dir.to_str().unwrap()).unwrap();
        expand_words_in(
            words,
            &mut state,
            ProcessSubs::Refuse,
            dir,
            &GlobLimits::DEFAULT,
        )
        .unwrap()
        .fields
    }

    #[test]
    fn unquoted_patterns_expand_and_quoted_ones_do_not() {
        let dir = fixture(&["a.txt", "b.txt", "c.log"]);
        let out = expand_in(
            dir.path(),
            &[
                Word::literal("*.txt"),
                word(&[("*.txt", Quote::Single)]),
                word(&[("*.txt", Quote::Double)]),
                word(&[("*", Quote::Backslash), (".txt", Quote::None)]),
            ],
        );
        assert_eq!(out, ["a.txt", "b.txt", "*.txt", "*.txt", "*.txt"]);
    }

    #[test]
    fn a_partly_quoted_pattern_matches_its_quoted_part_literally() {
        let dir = fixture(&["*x.txt", "ax.txt", "a.txt"]);
        // `'*'x*` : a literal star followed by `x` and a wildcard.
        let out = expand_in(
            dir.path(),
            &[word(&[("*", Quote::Single), ("x*", Quote::None)])],
        );
        assert_eq!(out, ["*x.txt"]);
    }

    #[test]
    fn no_match_and_invalid_patterns_stay_literal() {
        let dir = fixture(&["a.txt"]);
        let out = expand_in(
            dir.path(),
            &[
                Word::literal("*.txt"),
                Word::literal("*.none"),
                Word::literal("[z-"),
            ],
        );
        assert_eq!(out, ["a.txt", "*.none", "[z-"]);
    }

    #[test]
    fn braces_expand_only_when_unquoted() {
        let dir = fixture(&[]);
        let out = expand_in(
            dir.path(),
            &[Word::literal("a{1,2}"), word(&[("a{1,2}", Quote::Single)])],
        );
        assert_eq!(out, ["a1", "a2", "a{1,2}"]);
    }

    #[test]
    fn literal_backslashes_survive_quote_removal() {
        let dir = fixture(&["a.txt"]);
        let out = expand_in(
            dir.path(),
            &[
                word(&[("a\\*", Quote::Single)]),
                word(&[("\\", Quote::Backslash)]),
            ],
        );
        assert_eq!(out, ["a\\*", "\\"]);
    }

    #[test]
    fn a_quoted_backslash_is_a_literal_character_in_a_pattern() {
        let dir = fixture(&["a\\b.txt", "ab.txt"]);
        // `'a\'*` : names that start with `a\`.
        let out = expand_in(
            dir.path(),
            &[word(&[("a\\", Quote::Single), ("*", Quote::None)])],
        );
        assert_eq!(out, ["a\\b.txt"]);
    }

    #[test]
    fn unquoted_parameter_values_are_globbed_and_quoted_ones_are_not() {
        let dir = fixture(&["a.txt", "b.txt"]);
        let mut state = ShellState::new(dir.path().to_str().unwrap()).unwrap();
        state.set_variable("P", "*.txt");
        let mut unquoted = Word::new();
        unquoted.push_parameter("P".into(), false, Quote::None);
        let mut quoted = Word::new();
        quoted.push_parameter("P".into(), true, Quote::Double);
        let out = expand_words_in(
            &[unquoted, quoted],
            &mut state,
            ProcessSubs::Refuse,
            dir.path(),
            &GlobLimits::DEFAULT,
        )
        .unwrap()
        .fields;
        assert_eq!(out, ["a.txt", "b.txt", "*.txt"]);
    }

    #[test]
    fn a_glob_limit_fails_the_expansion_instead_of_substituting_the_literal() {
        let dir = fixture(&["f0.txt", "f1.txt", "f2.txt", "f3.txt", "f4.txt"]);
        let mut state = ShellState::new(dir.path().to_str().unwrap()).unwrap();
        let limits = GlobLimits {
            max_matches: 4,
            ..GlobLimits::DEFAULT
        };
        let words = [Word::literal("-l"), Word::literal("*.txt")];
        let err = expand_words_in(&words, &mut state, ProcessSubs::Refuse, dir.path(), &limits)
            .err()
            .expect("the limit must fail the expansion");
        let stopped = err
            .downcast_ref::<GlobLimitExceeded>()
            .expect("the limit error must reach the caller");
        assert_eq!(stopped.exceeded.axis, "matches held");
        assert!(err.to_string().contains("over the limit of 4"), "{err}");
    }

    /// The brace alternatives of one word, and the words of one command, share
    /// one glob budget: five patterns of one match each pass a limit of four.
    #[test]
    fn brace_alternatives_and_words_share_one_glob_budget() {
        let dir = fixture(&["f0.txt", "f1.txt", "f2.txt", "f3.txt", "f4.txt"]);
        let mut state = ShellState::new(dir.path().to_str().unwrap()).unwrap();
        let limits = GlobLimits {
            max_matches: 4,
            ..GlobLimits::DEFAULT
        };
        let braces = [Word::literal("{f0,f1,f2,f3,f4}*")];
        let words: Vec<Word> = (0..5).map(|i| Word::literal(&format!("f{i}*"))).collect();
        for case in [&braces[..], &words[..]] {
            let err = expand_words_in(case, &mut state, ProcessSubs::Refuse, dir.path(), &limits)
                .err()
                .expect("the shared budget must be exceeded");
            let stopped = err.downcast_ref::<GlobLimitExceeded>().unwrap();
            assert_eq!((stopped.exceeded.limit, stopped.exceeded.level), (4, 5));
        }
        // Within the budget the same words expand normally.
        let out = expand_words_in(
            &words[..4],
            &mut state,
            ProcessSubs::Refuse,
            dir.path(),
            &limits,
        )
        .unwrap()
        .fields;
        assert_eq!(out, ["f0.txt", "f1.txt", "f2.txt", "f3.txt"]);
    }

    #[test]
    fn refused_process_substitution_is_an_error() {
        let dir = fixture(&[]);
        let mut state = ShellState::new(dir.path().to_str().unwrap()).unwrap();
        let mut w = Word::new();
        w.push_process_sub(ProcessSubType::Input, "true".into());
        let err = expand_words_in(
            &[w],
            &mut state,
            ProcessSubs::Refuse,
            dir.path(),
            &GlobLimits::DEFAULT,
        )
        .err()
        .expect("refused");
        assert!(err.to_string().contains("<(true)"), "{err}");
    }

    #[test]
    fn display_round_trips_quoting() {
        let w = word(&[
            ("a b", Quote::Single),
            ("*", Quote::Backslash),
            ("x\"$", Quote::Double),
            ("y", Quote::None),
        ]);
        assert_eq!(w.to_string(), "'a b'\\*\"x\\\"\\$\"y");
        assert_eq!(Word::literal("plain"), "plain");
    }

    #[test]
    fn glob_pattern_escapes_quoted_metacharacters() {
        assert_eq!(glob_pattern("\\*a*"), Some("[*]a*".to_string()));
        assert_eq!(glob_pattern("\\*a"), None);
        assert_eq!(glob_pattern("\\[x?"), Some("[[]x?".to_string()));
    }
}
