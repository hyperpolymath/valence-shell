# SIGINT Handling Test Guide

## Overview

Phase 0 sealing includes proper SIGINT (Ctrl+C) handling for external commands.

---

## Implementation Details

**File**: `impl/rust-cli/src/external.rs`

```rust
// Check if terminated by signal
if let Some(signal) = status.signal() {
    // Convention: 128 + signal number
    // SIGINT (2) → exit code 130
    // SIGTERM (15) → exit code 143
    let exit_code = 128 + signal;
    return Ok(exit_code);
}
```

### Signal Exit Codes

| Signal | Number | Exit Code | Meaning |
|--------|--------|-----------|---------|
| SIGINT | 2 | 130 | Ctrl+C pressed |
| SIGTERM | 15 | 143 | Termination requested |
| SIGKILL | 9 | 137 | Force killed |

---

## Manual Testing

### Test 1: Interrupt Long-Running Command

```bash
$ vsh
vsh> sleep 100
^C
# Should return immediately, exit code 130
```

**Expected behavior**:
- Command terminates immediately on Ctrl+C
- Shell displays "^C" or similar
- Shell remains responsive
- Exit code stored: 130

### Test 2: Normal Command Completion

```bash
vsh> echo "test"
test
# Exit code: 0
```

**Expected behavior**:
- Command completes normally
- Output displayed
- Exit code: 0

### Test 3: Failed Command

```bash
vsh> false
# Exit code: 1
```

**Expected behavior**:
- Command fails normally
- Exit code: 1 (not signal-related)

### Test 4: Multiple Interrupts

```bash
vsh> sleep 10
^C
vsh> sleep 10
^C
vsh> echo "still works"
still works
```

**Expected behavior**:
- Each Ctrl+C terminates only the running command
- Shell continues functioning after each interrupt
- No zombie processes
- No state corruption

---

## Automated Testing

Currently tested via unit tests:

```rust
#[test]
fn test_external_command_success() {
    let exit_code = execute_external("true", &[]).unwrap();
    assert_eq!(exit_code, 0);
}

#[test]
fn test_external_command_failure() {
    let exit_code = execute_external("false", &[]).unwrap();
    assert_eq!(exit_code, 1);
}
```

**Future test** (requires process control):
```rust
// Spawn sleep, send SIGINT, verify exit code 130
// Currently difficult to test in unit tests
```

---

## Known Behavior

### What Works ✅
- Ctrl+C terminates external commands
- Shell remains responsive after interrupt
- Exit codes correctly set (130 for SIGINT)
- No zombie processes
- Works with any external command

### Platform Differences

**Unix/Linux**: Full signal support
- SIGINT, SIGTERM, SIGKILL all handled
- Exit codes: 128 + signal number

**Windows**: Limited signal support
- Ctrl+C works but exit codes may differ
- `#[cfg(unix)]` guards Unix-specific code

---

## Troubleshooting

### Issue: Ctrl+C Doesn't Work

**Possible causes**:
1. Command ignoring SIGINT (rare)
2. Process not in correct process group
3. Terminal in wrong mode

**Solution**: Use `Ctrl+\` (SIGQUIT) as fallback

### Issue: Shell Exits on Ctrl+C

**Not expected** - shell should catch SIGINT in REPL

**Check**: rustyline or similar should handle this

### Issue: Zombie Processes

**Should not happen** - `.status()` waits for child

**Verify**: `ps aux | grep defunct`

---

## Implementation Notes

### Why 128 + signal?

Unix convention for reporting signal-terminated processes:
- Normal exit: 0-127 (command's exit code)
- Signal: 128 + N (where N is signal number)
- Examples:
  - 128 + 2 = 130 (SIGINT)
  - 128 + 15 = 143 (SIGTERM)
  - 128 + 9 = 137 (SIGKILL)

### Why Check `status.signal()`?

On Unix, `status.code()` returns `None` if terminated by signal.
We must check `status.signal()` explicitly to get the signal number.

### Process Groups

`std::process::Command` automatically puts the child in its own process group on Unix, which means:
- Ctrl+C in terminal sends SIGINT to **foreground process group**
- Both shell and child receive the signal
- Child terminates, shell's REPL catches and continues

---

## Future Enhancements

### Job Control (Phase 6 M10+)
- Background processes (`&`)
- Suspend/resume (Ctrl+Z, `fg`, `bg`)
- Multiple jobs
- Process group management

### Better Error Messages
```bash
vsh> sleep 100
^C
Command interrupted (SIGINT)
vsh>
```

### Exit Code Variable
```bash
vsh> false
vsh> echo $?
1
vsh> sleep 10
^C
vsh> echo $?
130
```

Planned for Phase 6 M4 (Variables).

---

**Version**: 0.7.1 (Phase 0 Sealing)
**Author**: Jonathan D.A. Jewell <jonathan.jewell@open.ac.uk>
**License**: PMPL-1.0-or-later
**Date**: 2026-01-28
