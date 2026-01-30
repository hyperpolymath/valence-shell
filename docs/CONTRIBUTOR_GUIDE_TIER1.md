# Contributor Guide (Tier 1): Feature Contributors

**Target Audience**: Rust developers (no verification knowledge needed)

**You can contribute without knowing proof assistants!** This guide shows you how.

---

## TL;DR

```bash
1. Fork the repo
2. Write Rust code
3. Write property tests (we provide templates)
4. Run: cargo test
5. Submit PR

Maintainers handle verification.
```

---

## What You Need to Know

### Required Skills
- ✅ Rust (intermediate level)
- ✅ Unix/Linux basics
- ✅ Git

### NOT Required
- ❌ Lean 4 / Coq / Proof assistants
- ❌ Formal verification
- ❌ Theorem proving

---

## Contribution Tiers

**Tier 1 (You)**: Features, bug fixes, tests (no proofs)
**Tier 2**: Core modifications (some spec awareness)
**Tier 3**: Verification experts (proof updates)

**Most contributions are Tier 1!**

---

## What Can I Contribute?

### Easy (No verification needed)

- 🟢 New built-in commands (`pwd`, `cd`, `echo`)
- 🟢 UI improvements (better error messages, colors, formatting)
- 🟢 Tab completion improvements
- 🟢 Help text / documentation
- 🟢 Bug fixes in non-core code
- 🟢 Performance optimizations
- 🟢 New tests

### Medium (Template-based verification)

- 🟡 New reversible operations (chmod, chown, ln -s)
- 🟡 Extended file operations
- 🟡 New glob patterns

### Hard (Tier 2, see other guide)

- 🔴 State machine changes
- 🔴 Undo/redo algorithm modifications
- 🔴 Core safety changes

**Start with 🟢 Easy contributions!**

---

## Development Setup

### 1. Clone and Build

```bash
git clone https://github.com/hyperpolymath/valence-shell
cd valence-shell/impl/rust-cli

# Build
cargo build

# Run tests
cargo test

# Run the shell
cargo run
```

### 2. IDE Setup

**VS Code** (recommended):
```bash
# Install Rust Analyzer
code --install-extension rust-lang.rust-analyzer

# Open project
code .
```

**IntelliJ IDEA**:
- Install Rust plugin
- Import as Cargo project

---

## Example Contribution: Add `pwd` Command

Full walkthrough of adding a built-in command:

### Step 1: Add to Command Enum

**File**: `impl/rust-cli/src/parser.rs`

```rust
pub enum Command {
    // ... existing commands
    Pwd,  // ← ADD THIS
}
```

### Step 2: Implement the Command

**File**: `impl/rust-cli/src/builtins.rs`

```rust
/// Print working directory
pub fn builtin_pwd(state: &ShellState) -> Result<(), VshError> {
    println!("{}", state.current_dir.display());
    Ok(())
}
```

### Step 3: Wire Up Parser

**File**: `impl/rust-cli/src/parser.rs`, in `parse_builtin()`:

```rust
fn parse_builtin(&mut self) -> Result<Command> {
    match self.current_token() {
        "cd" => self.parse_cd(),
        "exit" => Ok(Command::Exit),
        // ... existing builtins
        "pwd" => Ok(Command::Pwd),  // ← ADD THIS
        _ => Err(ParseError::UnknownBuiltin),
    }
}
```

### Step 4: Wire Up Executor

**File**: `impl/rust-cli/src/executable.rs`, in `execute()`:

```rust
pub fn execute(command: Command, state: &mut ShellState) -> Result<i32> {
    match command {
        Command::Cd { path } => builtin_cd(state, &path)?,
        Command::Exit => std::process::exit(0),
        // ... existing commands
        Command::Pwd => builtin_pwd(state)?,  // ← ADD THIS
        _ => execute_external(command, state)?,
    }
    Ok(0)
}
```

### Step 5: Add description() Support

**File**: `impl/rust-cli/src/parser.rs`, in `impl Command`:

```rust
impl Command {
    pub fn description(&self) -> String {
        match self {
            Command::Cd { .. } => "cd".to_string(),
            Command::Exit => "exit".to_string(),
            // ... existing
            Command::Pwd => "pwd".to_string(),  // ← ADD THIS
        }
    }
}
```

### Step 6: Write Tests

**File**: `impl/rust-cli/tests/builtin_tests.rs`:

```rust
#[test]
fn test_pwd() {
    let temp = TempDir::new().unwrap();
    let state = ShellState::new(temp.path()).unwrap();

    // Capture stdout
    let output = test_utils::capture_stdout(|| {
        builtin_pwd(&state).unwrap();
    });

    // Should print current directory
    assert!(output.contains(temp.path().to_str().unwrap()));
}

#[test]
fn test_pwd_in_subdir() {
    let temp = TempDir::new().unwrap();
    let mut state = ShellState::new(temp.path()).unwrap();

    // Create and enter subdirectory
    std::fs::create_dir(temp.path().join("subdir")).unwrap();
    builtin_cd(&mut state, "subdir").unwrap();

    // pwd should show subdir
    let output = test_utils::capture_stdout(|| {
        builtin_pwd(&state).unwrap();
    });

    assert!(output.contains("subdir"));
}
```

### Step 7: Run Tests

```bash
cargo test test_pwd
```

### Step 8: Submit PR

```bash
git checkout -b add-pwd-command
git add impl/rust-cli/src/parser.rs impl/rust-cli/src/builtins.rs impl/rust-cli/src/executable.rs impl/rust-cli/tests/builtin_tests.rs
git commit -m "Add pwd built-in command

- Implements pwd command to print working directory
- Adds tests for basic functionality and subdirectory behavior
- No verification needed (read-only command)"

git push origin add-pwd-command
gh pr create
```

**That's it!** No proofs needed for read-only commands.

---

## Example Contribution: Add Reversible Operation

This is slightly more complex, but we provide templates.

### Use the Template Generator

```bash
# Generate template for chmod command
./scripts/new-operation-template.sh chmod
```

This creates:
- `impl/rust-cli/src/commands/chmod.rs` (skeleton)
- Property test template in `tests/property_tests.rs`

### Fill in the Template

**File**: `impl/rust-cli/src/commands/chmod.rs`

```rust
// Template provides structure, you fill in logic:

pub fn chmod(
    state: &mut ShellState,
    path: &str,
    mode: u32,  // ← ADD: permission mode
) -> Result<(), VshError> {
    let full_path = state.root.join(path);

    // Save old permissions for undo
    let old_perms = fs::metadata(&full_path)?.permissions();

    // Apply new permissions
    let mut perms = old_perms.clone();
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        perms.set_mode(mode);
    }
    fs::set_permissions(&full_path, perms)?;

    // Record in history for undo
    state.push_history(Operation::Chmod {
        path: path.to_string(),
        old_mode: old_perms.mode(),  // Save for undo
        new_mode: mode,
    });

    Ok(())
}
```

### Fill in Property Test

**File**: `impl/rust-cli/tests/property_tests.rs`

```rust
/// Property: chmod is reversible
#[test]
fn prop_chmod_reversible() {
    proptest!(|(
        path in valid_path_strategy(),
        mode in 0o000u32..=0o777u32
    )| {
        let temp = TempDir::new().unwrap();
        let mut state = ShellState::new(temp.path()).unwrap();

        // Create file
        let file_path = temp.path().join(&path);
        fs::write(&file_path, b"test").unwrap();

        // Capture initial permissions
        let before_mode = fs::metadata(&file_path).unwrap().permissions().mode();

        // Perform chmod
        chmod(&mut state, &path, mode).unwrap();

        // Verify changed
        let after_mode = fs::metadata(&file_path).unwrap().permissions().mode();
        prop_assert_ne!(before_mode & 0o777, after_mode & 0o777);

        // Undo
        state.pop_undo().unwrap();

        // Verify restored
        let restored_mode = fs::metadata(&file_path).unwrap().permissions().mode();
        prop_assert_eq!(before_mode & 0o777, restored_mode & 0o777);
    });
}
```

### Run Property Tests

```bash
cargo test prop_chmod_reversible
```

If the property test passes, your implementation is likely correct!

**Why?** Property tests are derived from the formal specifications. If your Rust code passes the property tests, it probably matches the proofs.

### Submit PR

```bash
git commit -m "Add chmod operation with undo support

- Implements chmod with permission mode parameter
- Saves old permissions for reversibility
- Property test validates undo correctness
- Passes all tests (1000+ iterations)"

gh pr create
```

Maintainers will verify the proof correspondence before merging.

---

## Property Test Writing Guide

Property tests are derived from formal specs. Here's the pattern:

### Template

```rust
#[test]
fn prop_OPERATION_NAME_reversible() {
    proptest!(|(/* random inputs */)| {
        // Setup
        let temp = TempDir::new().unwrap();
        let mut state = ShellState::new(temp.path()).unwrap();

        // Capture initial state
        let before = get_state_snapshot();

        // Perform operation
        OPERATION(&mut state, args).unwrap();

        // Verify operation succeeded
        prop_assert!(/* operation effect */);

        // Undo
        state.pop_undo().unwrap();

        // Verify restored to initial state
        let after = get_state_snapshot();
        prop_assert_eq!(before, after);
    });
}
```

### Common Assertions

```rust
// File exists
prop_assert!(path.exists());

// File doesn't exist
prop_assert!(!path.exists());

// File contents match
prop_assert_eq!(fs::read_to_string(&path)?, expected);

// Directory is empty
prop_assert_eq!(fs::read_dir(&path)?.count(), 0);

// Permissions match
prop_assert_eq!(
    fs::metadata(&path)?.permissions().mode() & 0o777,
    expected_mode
);
```

### Strategies for Random Inputs

```rust
use proptest::prelude::*;

// Valid path (no /, .., etc.)
fn valid_path_strategy() -> impl Strategy<Value = String> {
    "[a-z][a-z0-9_]{0,20}"
}

// File content
fn file_content_strategy() -> impl Strategy<Value = Vec<u8>> {
    prop::collection::vec(any::<u8>(), 0..1000)
}

// Permission mode
fn permission_strategy() -> impl Strategy<Value = u32> {
    0o000u32..=0o777u32
}
```

---

## Testing Best Practices

### Run All Tests

```bash
# Unit tests
cargo test

# Integration tests
cargo test --test '*'

# Property tests (slow, 1000+ iterations each)
cargo test prop_

# Stress tests (very slow, ignored by default)
cargo test --test stress_tests -- --ignored

# Security tests
cargo test --test security_tests
```

### Before Submitting PR

```bash
# Format code
cargo fmt

# Lint
cargo clippy --all-targets --all-features -- -D warnings

# All tests
cargo test --all-targets --all-features

# Build release (ensure no warnings)
cargo build --release
```

---

## Code Style

### Follow Existing Patterns

Look at similar code:
- `impl/rust-cli/src/commands/mkdir.rs` - Reversible operation example
- `impl/rust-cli/src/builtins.rs` - Built-in command example
- `impl/rust-cli/tests/property_tests.rs` - Property test example

### Error Handling

```rust
// Good: Specific error types
if !path.exists() {
    return Err(VshError::PathNotFound(path.clone()));
}

// Good: Context with anyhow
fs::write(&path, data)
    .with_context(|| format!("Failed to write to {}", path.display()))?;

// Bad: Generic errors
if !path.exists() {
    return Err("Path not found".into());  // ❌ Too generic
}
```

### Documentation

```rust
/// Brief description (one line)
///
/// Longer explanation if needed. Describe:
/// - What the function does
/// - Important preconditions
/// - Side effects
/// - Undo behavior (if applicable)
///
/// # Examples
///
/// ```
/// let mut state = ShellState::new("/tmp")?;
/// chmod(&mut state, "file.txt", 0o644)?;
/// ```
///
/// # Errors
///
/// Returns `VshError::PathNotFound` if path doesn't exist.
///
/// # Formal Specification
///
/// See: `proofs/lean4/Operations/Chmod.lean`
pub fn chmod(state: &mut ShellState, path: &str, mode: u32) -> Result<()> {
    // ...
}
```

---

## Common Pitfalls

### ❌ Forgetting to Record in History

```rust
// Bad: Operation not undoable
pub fn my_operation(state: &mut ShellState) -> Result<()> {
    fs::write("file.txt", "data")?;
    Ok(())  // ❌ No history tracking!
}

// Good: Recorded for undo
pub fn my_operation(state: &mut ShellState) -> Result<()> {
    // Save undo information
    let old_content = fs::read("file.txt").ok();

    fs::write("file.txt", "data")?;

    // Record in history
    state.push_history(Operation::MyOperation {
        path: "file.txt".into(),
        old_content,
    });

    Ok(())
}
```

### ❌ Hardcoded Paths

```rust
// Bad: Hardcoded paths
pub fn my_operation() -> Result<()> {
    fs::write("/tmp/file.txt", "data")?;  // ❌
}

// Good: Relative to shell state
pub fn my_operation(state: &ShellState, path: &str) -> Result<()> {
    let full_path = state.root.join(path);
    fs::write(full_path, "data")?;  // ✅
}
```

### ❌ No Error Handling

```rust
// Bad: Panics on error
pub fn my_operation() {
    fs::write("file.txt", "data").unwrap();  // ❌ Will panic
}

// Good: Returns Result
pub fn my_operation() -> Result<()> {
    fs::write("file.txt", "data")?;  // ✅ Propagates error
    Ok(())
}
```

---

## Getting Help

### Discord / Chat

Join our community: [Discord invite link]

### GitHub Discussions

Ask questions: https://github.com/hyperpolymath/valence-shell/discussions

### Pair Programming

Need help? Request pairing with a maintainer in your PR.

---

## PR Checklist

Before submitting:

- [ ] Code compiles: `cargo build`
- [ ] Tests pass: `cargo test`
- [ ] Formatted: `cargo fmt`
- [ ] Linted: `cargo clippy -- -D warnings`
- [ ] Property tests added (for reversible operations)
- [ ] Documentation updated (if needed)
- [ ] Commit message follows format:
  ```
  Short description (imperative, <50 chars)

  - Longer explanation (what and why)
  - Tests included
  - No verification needed (if applicable)
  ```

---

## What Happens After I Submit?

1. **Automated Checks** (5-10 min):
   - CI runs tests
   - Clippy checks code quality
   - Correspondence validation (non-blocking)

2. **Maintainer Review** (1-3 days):
   - Code review
   - Test coverage check
   - If reversible operation: Check formal spec

3. **Verification** (Only if needed, Tier 2/3):
   - Maintainers update proofs (you don't do this!)
   - Correspondence validation

4. **Merge**:
   - Your code is in main!
   - Included in next release
   - You're in CONTRIBUTORS.md

---

## Progression Path

### Start Here (Tier 1)
1. Fix typos, improve docs
2. Add simple built-ins (pwd, echo)
3. Fix UI bugs
4. Add tests

### Level Up (Tier 2)
1. Add reversible operations (chmod, ln -s)
2. Modify parser
3. Optimize performance

### Advanced (Tier 3)
1. Learn Lean 4 (if interested)
2. Update proofs
3. Correspondence checking

**Most contributors stay at Tier 1, and that's perfect!**

---

## Examples to Learn From

Good first PRs to read:
- [PR #123: Add pwd command](https://github.com/hyperpolymath/valence-shell/pull/123) (Simple)
- [PR #145: Add chmod operation](https://github.com/hyperpolymath/valence-shell/pull/145) (Medium)
- [PR #167: Improve error messages](https://github.com/hyperpolymath/valence-shell/pull/167) (Easy)

---

## Next Steps

**Ready to contribute?**

1. Read: `docs/ARCHITECTURE.md` (understand the codebase)
2. Browse: Open issues labeled "good first issue"
3. Try: Add a simple command (pwd, echo, etc.)
4. Ask: Questions in GitHub Discussions

**Welcome to Valence Shell!** 🎉
