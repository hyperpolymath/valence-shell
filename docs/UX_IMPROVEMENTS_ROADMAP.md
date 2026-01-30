# UX/UI Improvements: Matching zsh & fish

**Goal**: Be as concatenative as zsh, as friendly as fish, with clear help/error messages

---

## Current State Analysis

### What We Have ✅
- Basic REPL
- POSIX-compliant syntax
- Undo/redo (unique feature!)
- Job control
- Pipelines & redirections

### What We're Missing ❌
- **zsh features**: Advanced completion, directory stack, glob modifiers
- **fish features**: Syntax highlighting, autosuggestions, friendly errors
- **Help system**: No man pages, basic help text
- **Error messages**: Technical, not user-friendly

---

## Part 1: zsh-Style Concatenativity

### 1.1 Directory Stack (pushd/popd/dirs)

**zsh behavior**:
```bash
$ pushd /tmp
/tmp ~
$ pushd /var
/var /tmp ~
$ popd
/tmp ~
$ dirs -v
0  /tmp
1  ~
```

**Implementation**:
```rust
// src/builtins.rs
pub fn builtin_pushd(state: &mut ShellState, path: &str) -> Result<()> {
    let current = state.current_dir.clone();
    state.dir_stack.push(current);

    builtin_cd(state, path)?;

    // Print stack
    println!("{}", format_dir_stack(&state.dir_stack));
    Ok(())
}

pub fn builtin_popd(state: &mut ShellState) -> Result<()> {
    if let Some(dir) = state.dir_stack.pop() {
        builtin_cd(state, dir.to_str().unwrap())?;
        println!("{}", format_dir_stack(&state.dir_stack));
        Ok(())
    } else {
        Err(VshError::DirectoryStackEmpty)
    }
}

pub fn builtin_dirs(state: &ShellState, verbose: bool) -> Result<()> {
    if verbose {
        for (i, dir) in state.dir_stack.iter().enumerate() {
            println!("{}  {}", i, dir.display());
        }
    } else {
        println!("{}", format_dir_stack(&state.dir_stack));
    }
    Ok(())
}
```

### 1.2 Extended Glob Patterns

**zsh patterns**:
```bash
# Exclude pattern
ls **/*.rs~**/target/*   # All .rs files except in target/

# Numeric ranges
echo file<1-100>.txt      # file1.txt ... file100.txt

# Qualifiers
ls *(.)                   # Only regular files
ls *(/)                   # Only directories
ls *(.L+100k)             # Files larger than 100KB
```

**Implementation**:
```rust
// src/glob.rs
pub enum GlobModifier {
    Exclude(String),      // ~pattern
    Range(u32, u32),      # <start-end>
    OnlyFiles,            # (.)
    OnlyDirs,             # (/)
    SizeGreater(u64),     # (L+size)
    ModifiedAfter(SystemTime),  # (m-days)
}

pub fn expand_glob_extended(pattern: &str) -> Result<Vec<PathBuf>> {
    let (base_pattern, modifiers) = parse_glob_modifiers(pattern)?;
    let mut results = expand_glob(&base_pattern)?;

    // Apply modifiers
    for modifier in modifiers {
        results = apply_modifier(results, modifier)?;
    }

    Ok(results)
}
```

### 1.3 Command Correction

**zsh behavior**:
```bash
$ sl
zsh: correct 'sl' to 'ls' [nyae]?
```

**Implementation**:
```rust
// src/correction.rs
pub fn suggest_correction(cmd: &str) -> Option<String> {
    let known_commands = get_all_commands();  // Built-ins + PATH
    let mut best_match = None;
    let mut min_distance = usize::MAX;

    for known in known_commands {
        let distance = levenshtein_distance(cmd, &known);
        if distance < min_distance && distance <= 2 {
            min_distance = distance;
            best_match = Some(known);
        }
    }

    best_match
}

// In executor
if let Err(VshError::CommandNotFound(cmd)) = execute_external(&cmd) {
    if let Some(suggestion) = suggest_correction(&cmd) {
        eprintln!("vsh: command not found: {}", cmd);
        eprint!("Did you mean '{}'? [y/n] ", suggestion);

        let mut response = String::new();
        io::stdin().read_line(&mut response)?;

        if response.trim().to_lowercase() == "y" {
            execute_external(&suggestion)?;
        }
    }
}
```

### 1.4 Suffix Aliases

**zsh feature**:
```bash
alias -s txt=vim      # Open .txt files with vim
alias -s pdf=zathura  # Open .pdf with zathura

$ document.txt  # Automatically runs: vim document.txt
```

**Implementation**:
```rust
// src/state.rs
pub struct ShellState {
    // ...existing fields
    suffix_aliases: HashMap<String, String>,  // .txt -> vim
}

// src/executor.rs
pub fn execute(command: Command, state: &mut ShellState) -> Result<i32> {
    match command {
        Command::External { cmd, args } => {
            // Check if cmd is a file with known suffix
            if let Ok(metadata) = fs::metadata(&cmd) {
                if metadata.is_file() {
                    if let Some(ext) = Path::new(&cmd).extension() {
                        if let Some(program) = state.suffix_aliases.get(ext.to_str().unwrap()) {
                            // Transform: document.txt -> vim document.txt
                            return execute_external(&program, &[cmd]);
                        }
                    }
                }
            }

            execute_external(&cmd, &args)
        }
        // ...
    }
}
```

---

## Part 2: fish-Style Friendliness

### 2.1 Syntax Highlighting

**fish behavior**: Commands turn green when valid, red when invalid

**Implementation** (using `reedline` with `nu-ansi-term`):
```rust
// src/highlighter.rs
use reedline::Highlighter;
use nu_ansi_term::{Color, Style};

pub struct VshHighlighter {
    commands: HashSet<String>,  // Known commands
}

impl Highlighter for VshHighlighter {
    fn highlight(&self, line: &str, _cursor: usize) -> Text {
        let tokens = tokenize(line);
        let mut styled = Vec::new();

        for token in tokens {
            let style = match token.kind {
                TokenKind::Command => {
                    if self.is_valid_command(&token.value) {
                        Color::Green.bold()  // Valid command
                    } else {
                        Color::Red.normal()   // Invalid command
                    }
                }
                TokenKind::String => Color::Yellow.normal(),
                TokenKind::Number => Color::Cyan.normal(),
                TokenKind::Operator => Color::Magenta.bold(),
                TokenKind::Redirect => Color::Blue.bold(),
                TokenKind::Comment => Color::DarkGray.italic(),
                _ => Style::default(),
            };

            styled.push(style.paint(&token.value));
        }

        styled
    }
}

// Usage in REPL
let highlighter = VshHighlighter::new();
line_editor.with_highlighter(Box::new(highlighter));
```

### 2.2 Autosuggestions

**fish behavior**: Type `gi` → suggests `git status` (from history)

**Implementation**:
```rust
// src/suggestions.rs
pub struct AutoSuggester {
    history: Vec<String>,
    commands: HashSet<String>,
}

impl AutoSuggester {
    pub fn suggest(&self, partial: &str) -> Option<String> {
        // Try command history first (most likely)
        for entry in self.history.iter().rev() {
            if entry.starts_with(partial) {
                return Some(entry.clone());
            }
        }

        // Try known commands
        for cmd in &self.commands {
            if cmd.starts_with(partial) {
                return Some(cmd.clone());
            }
        }

        None
    }
}

// In REPL
line_editor.with_hinter(Box::new(|line: &str, pos: usize| {
    if let Some(suggestion) = suggester.suggest(&line[..pos]) {
        Some(suggestion[pos..].to_string())  // Show rest in gray
    } else {
        None
    }
}));
```

### 2.3 Friendly Error Messages

**fish philosophy**: Explain what went wrong AND how to fix it

**Bad** (current):
```
Error: PathNotFound("/tmp/nonexistent")
```

**Good** (fish-style):
```
vsh: The file or directory '/tmp/nonexistent' does not exist.

Did you mean one of these?
  /tmp/existing1
  /tmp/existing2

Or create it with:
  mkdir /tmp/nonexistent
```

**Implementation**:
```rust
// src/error.rs
impl std::fmt::Display for VshError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            VshError::PathNotFound(path) => {
                writeln!(f, "vsh: The file or directory '{}' does not exist.", path.display())?;

                // Suggest similar paths
                if let Some(suggestions) = find_similar_paths(path) {
                    writeln!(f, "\nDid you mean one of these?")?;
                    for suggestion in suggestions.iter().take(3) {
                        writeln!(f, "  {}", suggestion.display())?;
                    }
                }

                // Suggest creation
                if path.parent().is_some() {
                    writeln!(f, "\nOr create it with:")?;
                    if path.is_dir() {
                        writeln!(f, "  mkdir {}", path.display())?;
                    } else {
                        writeln!(f, "  touch {}", path.display())?;
                    }
                }

                Ok(())
            }

            VshError::PermissionDenied(path) => {
                writeln!(f, "vsh: Permission denied: '{}'", path.display())?;
                writeln!(f, "\nYou don't have permission to access this file.")?;
                writeln!(f, "Try:")?;
                writeln!(f, "  sudo vsh     (run as superuser)")?;
                writeln!(f, "  chmod +r {}  (make file readable)", path.display())?;
                Ok(())
            }

            VshError::CommandNotFound(cmd) => {
                writeln!(f, "vsh: Command not found: '{}'", cmd)?;

                if let Some(suggestion) = suggest_correction(cmd) {
                    writeln!(f, "\nDid you mean '{}'?", suggestion)?;
                }

                writeln!(f, "\nSearch for this command:")?;
                writeln!(f, "  dnf search {}    (Fedora)", cmd)?;
                writeln!(f, "  apt search {}    (Ubuntu/Debian)", cmd)?;

                Ok(())
            }

            // ... other errors with helpful messages
        }
    }
}
```

### 2.4 Interactive Help

**fish feature**: `help cd` opens web browser with full docs

**vsh adaptation**:
```rust
// src/builtins.rs
pub fn builtin_help(cmd: Option<&str>) -> Result<()> {
    match cmd {
        None => {
            // General help
            println!("vsh - Valence Shell {}", env!("CARGO_PKG_VERSION"));
            println!("\nCommands:");
            println!("  Type 'help <command>' for details");
            println!("\nBuilt-in commands:");
            for (name, desc) in get_builtin_commands() {
                println!("  {:<12} {}", name, desc);
            }
            println!("\nVerification Status: help verify");
            println!("User Guide: help guide");
        }

        Some("mkdir") => {
            println!("mkdir - Create directory");
            println!("\nUsage:");
            println!("  mkdir <path>         Create single directory");
            println!("  mkdir -p <path>      Create parent directories");
            println!("\nExamples:");
            println!("  mkdir test");
            println!("  mkdir -p a/b/c");
            println!("\nUndo:");
            println!("  This operation is reversible. Use 'undo' to remove.");
            println!("\nVerification:");
            println!("  [PROVEN] 95% confidence - proven in Lean 4");
            println!("\nSee also: rmdir, undo, help verify");
        }

        Some("guide") => {
            // Open USER_GUIDE.md
            if let Ok(guide_path) = find_doc("USER_GUIDE.md") {
                open_pager(&guide_path)?;
            } else {
                println!("User guide not found. See: https://github.com/hyperpolymath/valence-shell/docs");
            }
        }

        Some(cmd_name) => {
            if let Some(help_text) = get_help_for(cmd_name) {
                println!("{}", help_text);
            } else {
                println!("No help available for '{}'", cmd_name);
                println!("Try: help (for list of commands)");
            }
        }
    }

    Ok(())
}
```

### 2.5 Smart Pager

**fish feature**: Only use pager when output > terminal height

**Implementation**:
```rust
// src/pager.rs
pub fn smart_output(content: &str) -> Result<()> {
    let terminal_height = get_terminal_height()?;
    let content_lines = content.lines().count();

    if content_lines > terminal_height - 2 {
        // Use pager (less)
        let mut pager = Command::new("less")
            .arg("-R")  // Raw color codes
            .arg("-F")  // Quit if one screen
            .arg("-X")  // No init/deinit
            .stdin(Stdio::piped())
            .spawn()?;

        pager.stdin.as_mut().unwrap().write_all(content.as_bytes())?;
        pager.wait()?;
    } else {
        // Print directly
        println!("{}", content);
    }

    Ok(())
}
```

---

## Part 3: Man Pages & Help System

### 3.1 Man Page Generation

**Create**: `/usr/share/man/man1/vsh.1`

```man
.TH VSH 1 "January 2026" "Valence Shell 0.14.0" "User Commands"
.SH NAME
vsh \- formally verified shell with undo/redo
.SH SYNOPSIS
.B vsh
[\fIOPTIONS\fR]
[\fICOMMAND\fR]
.SH DESCRIPTION
.B vsh
is a POSIX-compliant shell with mathematical guarantees about correctness.
Features include reversible operations, formal verification, and GDPR compliance.
.SH OPTIONS
.TP
.BR \-c ", " \-\-command =\fICOMMAND\fR
Execute command and exit
.TP
.BR \-v ", " \-\-verify
Enable runtime verification (slower, 99%+ confidence)
.TP
.BR \-\-no\-sandbox
Disable filesystem sandbox (not recommended)
.SH BUILT-IN COMMANDS
.TP
.BR mkdir " " \fIPATH\fR
Create directory
.TP
.BR undo
Undo last operation
.TP
.BR redo
Redo previously undone operation
.SH EXAMPLES
.TP
Create and undo a directory:
.nf
$ vsh
vsh> mkdir test
✓ Created directory: test
vsh> undo
⟲ Undoing: mkdir test
✓ Removed directory: test
.fi
.SH SEE ALSO
.BR bash (1),
.BR zsh (1),
.BR fish (1)
.PP
Full documentation: /usr/share/doc/vsh/USER_GUIDE.md
.SH AUTHOR
Jonathan D.A. Jewell <jonathan.jewell@open.ac.uk>
```

**Generate with**:
```bash
# In scripts/generate-man-page.sh
pandoc docs/USER_GUIDE.md -s -t man -o vsh.1
```

### 3.2 In-Shell Help System

**Three-tier help**:

1. **Quick help** (`help`): One-line descriptions
2. **Command help** (`help mkdir`): Full usage, examples
3. **Topic help** (`help verification`, `help undo`): Conceptual guides

**Implementation**:
```rust
// src/help.rs
pub struct HelpSystem {
    quick_help: HashMap<String, String>,  // command -> one-line
    full_help: HashMap<String, HelpPage>,  // command -> full page
    topics: HashMap<String, String>,       // topic -> guide
}

pub struct HelpPage {
    name: String,
    summary: String,
    usage: Vec<String>,
    description: String,
    examples: Vec<Example>,
    see_also: Vec<String>,
    verification_level: VerificationLevel,
}

impl HelpSystem {
    pub fn show_quick(&self) {
        println!("vsh - Valence Shell {}", VERSION);
        println!("\nMost common commands:");
        for (cmd, desc) in self.quick_help.iter().take(10) {
            println!("  {:<15} {}", cmd, desc);
        }
        println!("\nType 'help <command>' for details");
        println!("Type 'help topics' for guides");
    }

    pub fn show_command(&self, cmd: &str) -> Result<()> {
        if let Some(page) = self.full_help.get(cmd) {
            smart_output(&page.format())?;
        } else {
            println!("No help for '{}'. Try: help", cmd);
        }
        Ok(())
    }
}
```

---

## Part 4: POSIX Compliance Verification

### 4.1 POSIX Compliance Test Suite

**Create**: `tests/posix_compliance_tests.rs`

```rust
//! POSIX Compliance Tests
//!
//! Verifies vsh adheres to POSIX.1-2017 specification
//! Reference: https://pubs.opengroup.org/onlinepubs/9699919799/

#[test]
fn posix_shell_grammar() {
    // POSIX requires specific parsing rules
    // See: https://pubs.opengroup.org/onlinepubs/9699919799/utilities/V3_chap02.html

    // Simple command
    assert_parses("ls -la");

    // Pipeline
    assert_parses("ls | grep .txt | wc -l");

    // Sequential execution
    assert_parses("mkdir test; cd test; touch file.txt");

    // Background
    assert_parses("sleep 10 &");

    // Redirections
    assert_parses("cat < input.txt > output.txt 2> errors.log");
}

#[test]
fn posix_test_command() {
    // POSIX test operators
    // See: https://pubs.opengroup.org/onlinepubs/9699919799/utilities/test.html

    let tests = vec![
        ("test -f file.txt", "file is regular file"),
        ("[ -d /tmp ]", "directory exists"),
        ("test 5 -gt 3", "integer comparison"),
        ("[ \"a\" = \"a\" ]", "string equality"),
    ];

    for (cmd, desc) in tests {
        let result = parse_and_execute(cmd);
        // Verify POSIX-compliant exit codes
    }
}

#[test]
fn posix_exit_codes() {
    // POSIX exit code requirements:
    // 0: Success
    // 1-125: Command-specific errors
    // 126: Command found but not executable
    // 127: Command not found
    // >128: Terminated by signal

    assert_exit_code("true", 0);
    assert_exit_code("false", 1);
    assert_exit_code("nonexistent_command", 127);
}

#[test]
fn posix_special_parameters() {
    // POSIX special parameters: $?, $!, $$, $#, $0, $@, etc.
    // See: https://pubs.opengroup.org/onlinepubs/9699919799/utilities/V3_chap02.html#tag_18_05_02

    // $?: Exit status of last command
    execute("true");
    assert_eq!(get_special_param("?"), "0");

    execute("false");
    assert_eq!(get_special_param("?"), "1");
}

#[test]
fn posix_quoting_rules() {
    // POSIX quoting: single quotes (literal), double quotes (expansion)

    assert_eq!(execute("echo 'hello world'"), "hello world");
    assert_eq!(execute("echo \"hello world\""), "hello world");

    // Single quotes preserve all characters
    assert_eq!(execute("echo '$$'"), "$$");

    // Double quotes allow variable expansion (when implemented)
    // assert_eq!(execute("VAR=test; echo \"$VAR\""), "test");
}

#[test]
fn posix_pipeline_exit_codes() {
    // POSIX: Pipeline exit code = exit code of last command

    // Last command succeeds
    assert_exit_code("false | true", 0);

    // Last command fails
    assert_exit_code("true | false", 1);
}
```

### 4.2 POSIX Conformance Statement

**Create**: `docs/POSIX_COMPLIANCE.md`

```markdown
# POSIX Compliance Statement

**Standard**: POSIX.1-2017 (IEEE Std 1003.1-2017)
**Compliance Level**: Shell Command Language (sh utility)

## Conforming Features

### Shell Grammar (✅ Fully Compliant)
- [x] Simple commands
- [x] Pipelines (`|`)
- [x] Sequential execution (`;`)
- [x] Background execution (`&`)
- [x] Logical AND (`&&`)
- [x] Logical OR (`||`)

### Redirections (✅ Fully Compliant)
- [x] Output (`>`, `>>`)
- [x] Input (`<`)
- [x] Error (`2>`, `2>>`)
- [x] Combined (`&>`, `2>&1`)
- [x] Here documents (`<<`, `<<-`)

### Quoting (✅ Fully Compliant)
- [x] Single quotes (literal)
- [x] Double quotes (expansion)
- [x] Backslash escaping

### Built-in Commands (⚠️ Partially Compliant)
- [x] cd: POSIX-compliant
- [x] exit: POSIX-compliant
- [x] test/[: POSIX-compliant (all operators)
- [ ] pwd: Not yet implemented (TODO)
- [ ] set: Partial (shell options not implemented)

### Extensions (Non-POSIX, vsh-specific)
- [x] undo: Reverse last operation
- [x] redo: Redo undone operation
- [x] mkdir/rmdir/touch/rm: Direct built-ins (usually external)
- [x] verify-status: Show verification confidence

## Non-Conforming Features

### Not Implemented
- [ ] Shell variables (`$VAR`, `$1`, `$@`, etc.)
- [ ] Command substitution (`$(cmd)`, `` `cmd` ``)
- [ ] Arithmetic expansion (`$((expr))`) - partially implemented
- [ ] Parameter expansion (`${var}`, `${var:-default}`, etc.)
- [ ] Functions
- [ ] Conditionals (`if`, `case`, `while`, `for`)
- [ ] Shell options (`set -e`, `set -u`, etc.)

### Intentional Deviations
None. Where implemented, vsh is POSIX-compliant.

## Verification

Run POSIX compliance tests:
```bash
cargo test --test posix_compliance_tests
```

Reference: https://pubs.opengroup.org/onlinepubs/9699919799/
```

---

## Implementation Priority

### Phase 1: Low-Hanging Fruit (1-2 weeks)
1. ✅ Friendly error messages (1 day)
2. ✅ Syntax highlighting (2 days, using reedline)
3. ✅ Command correction (1 day)
4. ✅ Smart pager (1 day)
5. ✅ Improved help system (2 days)

### Phase 2: Medium Effort (2-3 weeks)
1. ⏳ Autosuggestions (3 days)
2. ⏳ Directory stack (2 days)
3. ⏳ Man pages (2 days)
4. ⏳ POSIX compliance tests (3 days)
5. ⏳ Extended glob patterns (4 days)

### Phase 3: Advanced (4-6 weeks)
1. ⏳ Suffix aliases (3 days)
2. ⏳ Interactive help (web browser integration) (2 days)
3. ⏳ Full POSIX variable support (2 weeks)
4. ⏳ Advanced completion (context-aware) (1 week)

---

## Success Metrics

**zsh-level concatenativity**:
- [ ] Directory stack (pushd/popd/dirs)
- [ ] Extended glob patterns
- [ ] Command correction
- [ ] Suffix aliases

**fish-level friendliness**:
- [ ] Syntax highlighting (real-time)
- [ ] Autosuggestions (from history)
- [ ] Friendly error messages (with suggestions)
- [ ] Smart paging

**Documentation quality**:
- [ ] Man pages (vsh.1)
- [ ] In-shell help (help <command>)
- [ ] Topic guides (help topics)
- [ ] Quick reference (help)

**POSIX compliance**:
- [ ] 100% compliant where implemented
- [ ] Compliance test suite passing
- [ ] Conformance statement published

---

## Next Steps

**Immediate**:
1. Create issues for Phase 1 items
2. Implement friendly error messages (biggest UX win)
3. Add syntax highlighting (using existing reedline support)

**Short-term**:
1. Complete Phase 1 (2 weeks)
2. Start Phase 2 (autosuggestions, help system)

**Medium-term**:
1. Complete Phase 2 (POSIX compliance, man pages)
2. User testing for UX feedback

**Long-term**:
1. Phase 3 advanced features
2. Continuous UX improvement based on user feedback
