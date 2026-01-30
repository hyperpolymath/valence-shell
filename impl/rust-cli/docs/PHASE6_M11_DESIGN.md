# Phase 6 Milestone 11: Shell Variables - Design

**Version**: 0.14.0 → 0.15.0
**Date**: 2026-01-29
**Status**: Design phase
**Complexity**: High (parser changes, state management, expansion)

---

## Overview

Implement POSIX shell variable support including:
- Variable assignment and retrieval
- Variable expansion in commands
- Environment variable access
- Special parameters ($?, $0, $$, etc.)
- Parameter expansion forms (${VAR:-default}, etc.)

---

## Core Features

### 1. Variable Assignment

```bash
VAR=value           # Simple assignment
VAR="hello world"   # Quoted value
VAR=$((2 + 3))      # Arithmetic result
VAR=$(ls)           # Command substitution result
export VAR=value    # Export to environment
```

**Syntax Rules:**
- No spaces around `=`
- Value can be unquoted (single word) or quoted
- Assignment can appear before commands: `VAR=x cmd args`

### 2. Variable Expansion

```bash
echo $VAR           # Simple expansion
echo ${VAR}         # Braced expansion
echo "$VAR"         # Expansion in double quotes
echo '$VAR'         # Literal in single quotes (no expansion)
echo "Value: $VAR"  # Embedded in string
```

**Expansion Contexts:**
- Command arguments
- Arithmetic expressions: `$((x + $VAR))`
- Here documents (unless delimiter quoted)
- Redirections: `cat < $FILE`

### 3. Environment Variables

```bash
echo $PATH          # Read environment
echo $HOME
echo $USER
export VAR=value    # Make available to child processes
unset VAR           # Remove variable
```

### 4. Special Parameters

| Parameter | Meaning |
|-----------|---------|
| `$?` | Exit status of last command |
| `$$` | PID of current shell |
| `$!` | PID of last background job |
| `$0` | Shell name (vsh) |
| `$#` | Number of positional parameters |
| `$@` | All positional parameters (quoted) |
| `$*` | All positional parameters (single word) |
| `$1, $2, ...` | Positional parameters |

### 5. Parameter Expansion

```bash
${VAR:-default}     # Use default if unset/null
${VAR:=default}     # Assign default if unset/null
${VAR:?error}       # Error if unset/null
${VAR:+alternate}   # Use alternate if set

# String operations (advanced, defer to M11.1)
${VAR#pattern}      # Remove shortest prefix
${VAR##pattern}     # Remove longest prefix
${VAR%pattern}      # Remove shortest suffix
${VAR%%pattern}     # Remove longest suffix
${VAR/pat/repl}     # Replace first match
${VAR//pat/repl}    # Replace all matches
${#VAR}             # String length
```

---

## Implementation Strategy

### Phase 1: Foundation (M11 Core)
1. Variable storage in ShellState
2. Variable assignment parsing
3. Simple expansion ($VAR, ${VAR})
4. Environment variable access
5. Special parameters ($?, $$, $!)

### Phase 2: Advanced (M11.1 - Optional)
6. Parameter expansion forms (${VAR:-default}, etc.)
7. String operations (${VAR#pattern}, etc.)
8. Array variables (bash extension, defer)

---

## Data Structures

### Variable Storage

```rust
// In ShellState
pub struct ShellState {
    // ... existing fields ...

    /// User-defined variables
    variables: HashMap<String, String>,

    /// Exported environment variables
    exported: HashSet<String>,

    /// Positional parameters ($1, $2, ...)
    positional: Vec<String>,
}

impl ShellState {
    pub fn set_var(&mut self, name: &str, value: String) { ... }
    pub fn get_var(&self, name: &str) -> Option<&str> { ... }
    pub fn export_var(&mut self, name: &str) { ... }
    pub fn unset_var(&mut self, name: &str) { ... }
    pub fn get_special_param(&self, param: &str) -> Option<String> { ... }
}
```

### Parser Changes

```rust
#[derive(Debug, Clone, PartialEq)]
pub enum Token {
    // ... existing variants ...

    Variable(String),        // $VAR or ${VAR}
    Assignment(String, String), // VAR=value
}

#[derive(Debug, Clone, PartialEq)]
pub enum Command {
    // ... existing variants ...

    Assignment { name: String, value: String },
}
```

---

## Parsing Rules

### Variable Syntax

```
$VAR        → Variable name until non-identifier char
${VAR}      → Variable name within braces
$0-$9       → Special positional parameters
$$          → Shell PID
$?          → Exit status
$!          → Last background job PID
```

**Identifier Rules:**
- Start with letter or underscore
- Followed by letters, digits, underscores
- Case-sensitive

### Assignment Syntax

```
NAME=VALUE
NAME="VALUE"
NAME='VALUE'
NAME=$(command)
NAME=$((expr))
```

**Assignment Detection:**
- Occurs at start of command
- Or before command: `VAR=x cmd args`

---

## Expansion Algorithm

### Tokenization Phase

1. **Identify variable references** in input:
   - `$VAR` → ends at first non-identifier char
   - `${VAR}` → ends at closing `}`

2. **Track quote context**:
   - Single quotes: No expansion
   - Double quotes: Expansion enabled
   - No quotes: Expansion enabled

### Expansion Phase

```rust
fn expand_variables(input: &str, state: &ShellState) -> Result<String> {
    let mut result = String::new();
    let mut chars = input.chars().peekable();

    while let Some(ch) = chars.next() {
        match ch {
            '$' => {
                if chars.peek() == Some(&'{') {
                    // Braced expansion: ${VAR}
                    chars.next(); // consume '{'
                    let name = read_until(&mut chars, '}');
                    let value = state.get_var(&name)
                        .or_else(|| env::var(&name).ok())
                        .unwrap_or_default();
                    result.push_str(&value);
                } else if chars.peek().map(|c| c.is_ascii_digit()).unwrap_or(false) {
                    // Positional parameter: $1, $2, etc.
                    let digit = chars.next().unwrap();
                    let index = digit.to_digit(10).unwrap() as usize;
                    if let Some(value) = state.positional.get(index) {
                        result.push_str(value);
                    }
                } else {
                    // Simple expansion: $VAR
                    let name = read_identifier(&mut chars);
                    match name.as_str() {
                        "?" => result.push_str(&state.last_exit_code.to_string()),
                        "$" => result.push_str(&std::process::id().to_string()),
                        "!" => result.push_str(&state.last_bg_pid.to_string()),
                        _ => {
                            let value = state.get_var(&name)
                                .or_else(|| env::var(&name).ok())
                                .unwrap_or_default();
                            result.push_str(&value);
                        }
                    }
                }
            }
            _ => result.push(ch),
        }
    }

    Ok(result)
}
```

---

## Integration Points

### 1. Tokenizer Changes

- Add variable detection: `$` followed by identifier or `{}`
- Add assignment detection: `WORD=WORD` pattern
- Preserve quote context for expansion control

### 2. Parser Changes

- Parse assignment commands
- Parse variable references in arguments
- Handle prefix assignments: `VAR=x cmd`

### 3. Execution Changes

- Expand variables before command execution
- Set special parameters after command completion
- Update environment for exported variables

### 4. ShellState Changes

- Add variable storage HashMap
- Add exported variable tracking
- Add positional parameter storage
- Update last_exit_code, last_bg_pid for special params

---

## Examples

### Basic Usage

```bash
vsh> NAME="Alice"
vsh> echo "Hello, $NAME"
Hello, Alice

vsh> COUNT=5
vsh> echo $((COUNT * 2))
10

vsh> FILE="output.txt"
vsh> echo "data" > $FILE
vsh> cat $FILE
data
```

### Environment Variables

```bash
vsh> echo $HOME
/home/user

vsh> echo $PATH
/usr/bin:/bin

vsh> export MY_VAR="exported"
vsh> env | grep MY_VAR
MY_VAR=exported
```

### Special Parameters

```bash
vsh> ls
vsh> echo $?
0

vsh> false
vsh> echo $?
1

vsh> sleep 10 &
[1] 12345
vsh> echo $!
12345

vsh> echo $$
9876
```

### Command Assignment

```bash
vsh> FILES=$(ls *.txt)
vsh> echo $FILES
file1.txt file2.txt file3.txt

vsh> DATE=$(date +%Y-%m-%d)
vsh> echo "Today is $DATE"
Today is 2026-01-29
```

---

## Testing Strategy

### Unit Tests

```rust
#[test]
fn test_variable_assignment() {
    let mut state = ShellState::new(".").unwrap();
    state.set_var("FOO", "bar".to_string());
    assert_eq!(state.get_var("FOO"), Some("bar"));
}

#[test]
fn test_variable_expansion() {
    let state = ShellState::new(".").unwrap();
    state.set_var("NAME", "Alice".to_string());
    let expanded = expand_variables("Hello, $NAME", &state).unwrap();
    assert_eq!(expanded, "Hello, Alice");
}

#[test]
fn test_special_parameters() {
    let mut state = ShellState::new(".").unwrap();
    state.last_exit_code = 42;
    let expanded = expand_variables("Exit: $?", &state).unwrap();
    assert_eq!(expanded, "Exit: 42");
}
```

### Integration Tests

```rust
#[test]
fn test_variable_in_command() {
    let mut state = ShellState::new(temp_dir()).unwrap();

    // Set variable
    execute_line("FILE=test.txt", &mut state).unwrap();

    // Use in command
    execute_line("echo hello > $FILE", &mut state).unwrap();

    // Verify file created
    assert!(temp_dir().join("test.txt").exists());
}
```

---

## Edge Cases

### 1. Undefined Variables
```bash
echo $UNDEFINED    # Expands to empty string (POSIX behavior)
```

### 2. Variable Names

```bash
VAR=x              # Valid
VAR_2=x            # Valid
_VAR=x             # Valid
2VAR=x             # Invalid (starts with digit)
VAR-NAME=x         # Invalid (hyphen not allowed)
```

### 3. Quote Interaction

```bash
VAR="hello"
echo $VAR          # hello
echo "$VAR"        # hello
echo '$VAR'        # $VAR (literal)
echo \$VAR         # $VAR (escaped)
```

### 4. Assignment Scope

```bash
VAR=local cmd      # VAR only set for cmd execution
VAR=value          # VAR persists in shell
```

---

## Implementation Phases

### Week 1: Foundation (M11 Core)
- [ ] Add variable storage to ShellState
- [ ] Implement set_var, get_var, unset_var
- [ ] Add Variable and Assignment tokens to parser
- [ ] Implement simple expansion ($VAR, ${VAR})
- [ ] Add environment variable access
- [ ] Implement special parameters ($?, $$, $!)
- [ ] Add 20+ unit tests

### Week 2: Integration
- [ ] Integrate expansion into command execution
- [ ] Update all execution paths (external, built-ins, pipelines)
- [ ] Add variable expansion to redirections
- [ ] Add variable expansion to arithmetic expressions
- [ ] Add 10+ integration tests
- [ ] Update help text with variable examples

### Week 3: Advanced (M11.1 - Optional)
- [ ] Parameter expansion forms (${VAR:-default}, etc.)
- [ ] String operations (${VAR#pattern}, etc.)
- [ ] Advanced tests and documentation

---

## Success Criteria

- [x] Design document complete
- [ ] Variable storage in ShellState
- [ ] Assignment parsing (VAR=value)
- [ ] Simple expansion ($VAR, ${VAR})
- [ ] Environment variables accessible
- [ ] Special parameters ($?, $$, $!) working
- [ ] Variables work in all contexts (commands, redirections, arithmetic)
- [ ] 30+ tests passing (20 unit + 10 integration)
- [ ] Documentation updated
- [ ] All existing tests still pass

---

## Related Documents

- PHASE6_M7-M10_COMPLETE.md - Process substitution, arithmetic, here docs, job control
- ARCHITECTURE.md - Overall system architecture
- POSIX_COMPLIANCE.md - POSIX shell compliance roadmap

---

## Next Steps After M11

1. **M12: Glob Expansion** - Wildcard patterns (*, ?, [...])
2. **M13: Quote Processing** - Full quote removal and escape handling
3. **Phase 4: Verification** - Prove Rust implementation matches Lean theorems
