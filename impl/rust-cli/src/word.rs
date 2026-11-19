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

use std::ffi::OsString;
use std::fmt;
use std::path::{Path, PathBuf};

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
        for (index, segment) in self.segments.iter().enumerate() {
            match segment {
                Segment::Literal { text, quote } => fmt_literal(f, text, *quote)?,
                Segment::Parameter {
                    expr,
                    braced,
                    quote,
                } => {
                    let open = if quote.is_quoted() { "\"" } else { "" };
                    // `$A''b` must not come back as `$Ab`: brace the name when
                    // the text after it could continue it.
                    let runs_on = self.segments.get(index + 1).is_some_and(|next| {
                        matches!(next, Segment::Literal { text, quote: Quote::None }
                            if text.starts_with(|c: char| c.is_alphanumeric() || c == '_'))
                    }) && expr.starts_with(|c: char| c.is_alphabetic() || c == '_');
                    if *braced || runs_on {
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
    /// The arguments, after quote removal. A glob match keeps the exact bytes
    /// of its file name, which need not be UTF-8.
    pub fields: Vec<OsString>,
    /// Process substitutions started for these arguments.
    pub process_subs: Vec<ProcessSubstitution>,
}

impl Expansion {
    /// The arguments as text, for a builtin or a function that works on
    /// strings. Bytes that are not UTF-8 are replaced; external commands get
    /// [`Expansion::fields`] unchanged.
    pub fn lossy_fields(&self) -> Vec<String> {
        self.fields
            .iter()
            .map(|field| field.to_string_lossy().into_owned())
            .collect()
    }

    /// Wait for the process substitutions and remove their FIFOs.
    pub fn cleanup(self) {
        for proc_sub in self.process_subs {
            if let Err(e) = proc_sub.cleanup() {
                eprintln!("Warning: Failed to cleanup process substitution: {}", e);
            }
        }
    }

    /// Hand the process substitutions of a background job to a detached
    /// thread, which waits for each one to end and then removes its FIFO.
    /// The job may open a FIFO at any later time, so nothing is released and
    /// the shell does not wait.
    // snip: a substitution that the job never opens stays blocked until the
    // shell exits, and a FIFO is left in the temp directory when the shell
    // exits first (`vsh -c 'cmd <(x) &'`). Release and remove them once the
    // job table reaps background jobs.
    pub fn cleanup_when_consumed(self) {
        if self.process_subs.is_empty() {
            return;
        }
        std::thread::spawn(move || {
            for proc_sub in self.process_subs {
                if let Err(e) = proc_sub.cleanup_when_consumed() {
                    eprintln!("Warning: Failed to cleanup process substitution: {}", e);
                }
            }
        });
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
                    // The tilde prefix runs to the first unquoted `/`. It ends in this
                    // segment only if the segment has a `/` or is the whole word;
                    // otherwise a quoted piece or an expansion is part of the
                    // prefix, and the tilde stays literal (`~'local'/x`).
                    if index == 0
                        && text.starts_with('~')
                        && (text.contains('/') || word.segments.len() == 1)
                    {
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
    fields: &mut Vec<OsString>,
) -> Result<()> {
    let encoded = encode(chars);
    for candidate in glob::expand_braces(&encoded) {
        match glob_pattern(&candidate) {
            None => fields.push(remove_quotes(&candidate).into()),
            Some(pattern) => match glob::expand_glob_continuing(&pattern, cwd, limits, *spent) {
                Ok(found) if !found.paths.is_empty() => {
                    *spent = found.usage;
                    fields.extend(found.paths.into_iter().map(PathBuf::into_os_string));
                }
                // No match still spent reads.
                Ok(found) => {
                    *spent = found.usage;
                    fields.push(remove_quotes(&candidate).into());
                }
                // A limit is not "no match": substituting the literal word
                // would run the command on the wrong arguments.
                Err(e) if e.is::<GlobLimitExceeded>() => return Err(e),
                // No match, or not a valid pattern: keep the word (POSIX).
                _ => fields.push(remove_quotes(&candidate).into()),
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
    // Inside an unquoted `[...]`: how many members so far, and whether a
    // quoted `-` waits to be written last, where it cannot form a range.
    let mut class: Option<usize> = None;
    let mut hyphen = false;
    let mut chars = encoded.chars();
    while let Some(ch) = chars.next() {
        if ch == '\\' {
            let Some(next) = chars.next() else { continue };
            match (class.as_mut(), next) {
                (Some(members), '-') => {
                    *members += 1;
                    hyphen = true;
                }
                // `*`, `?` and `[` are already literal inside a class.
                (Some(members), '*' | '?' | '[') => {
                    *members += 1;
                    pattern.push(next);
                }
                (members, _) => {
                    if let Some(members) = members {
                        *members += 1;
                    }
                    pattern.push_str(&::glob::Pattern::escape(&next.to_string()));
                }
            }
            continue;
        }
        active |= matches!(ch, '*' | '?' | '[');
        match class.as_mut() {
            None if ch == '[' => class = Some(0),
            None => {}
            // `]` first in a class (after `!` or `^`) is a member, not the end.
            Some(members) if ch == ']' && *members > 0 => {
                if std::mem::take(&mut hyphen) {
                    pattern.push('-');
                }
                class = None;
            }
            Some(members) if *members == 0 && matches!(ch, '!' | '^') && pattern.ends_with('[') => {
            }
            Some(members) => *members += 1,
        }
        pattern.push(ch);
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
        .lossy_fields()
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
        .lossy_fields();
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
        .lossy_fields();
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
    fn display_keeps_a_literal_out_of_an_unbraced_name() {
        let mut w = Word::new();
        w.push_parameter("A".to_string(), false, Quote::None);
        w.push_str("suffix", Quote::None);
        assert_eq!(w.to_string(), "${A}suffix");

        std::env::remove_var("Asuffix");
        let dir = fixture(&[]);
        let mut state = ShellState::new(dir.path().to_str().unwrap()).unwrap();
        state.set_variable("A", "x");
        let out = expand_words_in(
            &[w],
            &mut state,
            ProcessSubs::Refuse,
            dir.path(),
            &GlobLimits::DEFAULT,
        )
        .unwrap();
        assert_eq!(out.lossy_fields(), ["xsuffix"]);
    }

    #[test]
    fn a_quoted_hyphen_in_a_bracket_is_not_a_range() {
        // [a'-'z]*.txt
        assert_eq!(glob_pattern("[a\\-z]*.txt"), Some("[az-]*.txt".to_string()));
        let dir = fixture(&["-.txt", "a.txt", "m.txt", "z.txt"]);
        let w = word(&[
            ("[a", Quote::None),
            ("-", Quote::Single),
            ("z]*.txt", Quote::None),
        ]);
        assert_eq!(expand_in(dir.path(), &[w]), ["-.txt", "a.txt", "z.txt"]);
    }

    #[test]
    fn a_sole_quoted_hyphen_closes_a_bracket_class() {
        // ['-']*.txt
        let dir = fixture(&["-.txt", "a.txt"]);
        let w = word(&[
            ("[", Quote::None),
            ("-", Quote::Single),
            ("]*.txt", Quote::None),
        ]);
        assert_eq!(expand_in(dir.path(), &[w]), ["-.txt"]);
    }

    #[test]
    fn a_tilde_with_a_quoted_prefix_is_not_expanded() {
        let dir = fixture(&[]);
        let quoted = word(&[
            ("~", Quote::None),
            ("local", Quote::Single),
            ("/x", Quote::None),
        ]);
        assert_eq!(expand_in(dir.path(), &[quoted]), ["~local/x"]);
        // An unquoted slash ends the prefix, so this one still expands.
        let slash = word(&[
            ("~/", Quote::None),
            ("local", Quote::Single),
            ("/x", Quote::None),
        ]);
        let got = expand_in(dir.path(), &[slash]);
        assert!(
            got[0].ends_with("/local/x") && !got[0].starts_with('~'),
            "{got:?}"
        );
    }

    #[test]
    fn a_non_ascii_character_before_a_brace_does_not_panic() {
        let dir = fixture(&[]);
        let w = word(&[("é", Quote::Single), ("{a,b}", Quote::None)]);
        assert_eq!(expand_in(dir.path(), &[w]), ["éa", "éb"]);
    }

    #[test]
    fn glob_pattern_escapes_quoted_metacharacters() {
        assert_eq!(glob_pattern("\\*a*"), Some("[*]a*".to_string()));
        assert_eq!(glob_pattern("\\*a"), None);
        assert_eq!(glob_pattern("\\[x?"), Some("[[]x?".to_string()));
    }
}
