# Phase 6 Milestone 8: Arithmetic Expansion

**Version**: 0.12.0
**Status**: In Progress
**Date**: 2026-01-29

---

## Overview

Implement POSIX arithmetic expansion using `$((expression))` syntax. This allows integer arithmetic operations within command arguments and variable assignments.

## Syntax

```bash
# Basic arithmetic
echo $((5 + 3))           # 8
echo $((10 - 4))          # 6
echo $((6 * 7))           # 42
echo $((20 / 4))          # 5
echo $((17 % 5))          # 2
echo $((2 ** 10))         # 1024

# With variables
x=5
y=10
echo $((x + y))           # 15
echo $((x * 2 + y))       # 20

# Nested expressions
echo $(( (5 + 3) * 2 ))   # 16
echo $(( 2 ** (3 + 1) ))  # 16

# Comparisons (return 0 or 1)
echo $((5 > 3))           # 1 (true)
echo $((5 < 3))           # 0 (false)
echo $((5 == 5))          # 1
echo $((5 != 3))          # 1

# Logical operations
echo $((1 && 1))          # 1 (true)
echo $((1 && 0))          # 0 (false)
echo $((1 || 0))          # 1 (true)
echo $((! 0))             # 1 (true)

# Bitwise operations
echo $((5 & 3))           # 1 (binary AND)
echo $((5 | 3))           # 7 (binary OR)
echo $((5 ^ 3))           # 6 (binary XOR)
echo $((~5))              # -6 (bitwise NOT)
echo $((8 << 2))          # 32 (left shift)
echo $((8 >> 2))          # 2 (right shift)

# Assignment (optional for now - defer to later)
echo $(( x = 5 + 3 ))     # 8 (and sets x=8)
```

## POSIX Compliance

**From POSIX.1-2017 Section 2.6.4:**

> The shell shall expand all tokens in the expression for parameter expansion, command substitution, and quote removal.
>
> The arithmetic expansion can be nested. To specify nesting, the inner expansion shall be enclosed in parentheses.
>
> Arithmetic expansion provides a mechanism for evaluating an arithmetic expression and substituting its value.

**Operators (precedence order, highest to lowest):**

1. `( )`            - Parentheses (grouping)
2. `**`             - Exponentiation (right-associative)
3. `! ~ + -`        - Logical NOT, bitwise NOT, unary plus/minus
4. `* / %`          - Multiplication, division, modulo
5. `+ -`            - Addition, subtraction
6. `<< >>`          - Bitwise shift left/right
7. `< <= > >=`      - Comparison operators
8. `== !=`          - Equality operators
9. `&`              - Bitwise AND
10. `^`             - Bitwise XOR
11. `|`             - Bitwise OR
12. `&&`            - Logical AND
13. `||`            - Logical OR
14. `= += -= *= /= %= <<= >>= &= ^= |=` - Assignment (optional)

**Integer Arithmetic:**
- All values are **signed integers** (i64 in Rust)
- Division by zero is an error
- Overflow behavior: wrap around (Rust default)

## Implementation Plan

### 1. Parser Extensions

**Add to `parser.rs`:**

```rust
#[derive(Debug, Clone, PartialEq)]
pub enum ArithOp {
    // Arithmetic
    Add, Sub, Mul, Div, Mod, Pow,

    // Bitwise
    BitAnd, BitOr, BitXor, BitNot,
    ShiftLeft, ShiftRight,

    // Comparison
    Lt, Le, Gt, Ge, Eq, Ne,

    // Logical
    LogAnd, LogOr, LogNot,

    // Unary
    UnaryPlus, UnaryMinus,
}

#[derive(Debug, Clone, PartialEq)]
pub enum ArithExpr {
    Literal(i64),
    Variable(String),
    UnaryOp(ArithOp, Box<ArithExpr>),
    BinaryOp(ArithOp, Box<ArithExpr>, Box<ArithExpr>),
}

pub fn parse_arithmetic(input: &str) -> Result<ArithExpr> {
    // Recursive descent parser for arithmetic expressions
    // Handles operator precedence and associativity
}

pub fn parse_arith_expansion(chars: &mut Peekable<Chars>) -> Result<String> {
    // Detect $(( ... ))
    // Call parse_arithmetic() on inner content
    // Evaluate expression
    // Return result as string
}
```

**Add to `WordPart` enum:**

```rust
pub enum WordPart {
    // ... existing variants ...
    ArithmeticExpansion(ArithExpr),
}
```

### 2. Evaluator

**Add `arith.rs` module:**

```rust
use anyhow::{anyhow, Result};
use crate::parser::{ArithExpr, ArithOp};
use crate::state::ShellState;

/// Evaluate arithmetic expression
pub fn eval_arith(expr: &ArithExpr, state: &ShellState) -> Result<i64> {
    match expr {
        ArithExpr::Literal(n) => Ok(*n),

        ArithExpr::Variable(name) => {
            let value = state.get_var(name)
                .unwrap_or("0");
            value.parse::<i64>()
                .map_err(|_| anyhow!("Invalid integer: {}", value))
        }

        ArithExpr::UnaryOp(op, expr) => {
            let val = eval_arith(expr, state)?;
            match op {
                ArithOp::UnaryPlus => Ok(val),
                ArithOp::UnaryMinus => Ok(-val),
                ArithOp::LogNot => Ok(if val == 0 { 1 } else { 0 }),
                ArithOp::BitNot => Ok(!val),
                _ => Err(anyhow!("Invalid unary operator")),
            }
        }

        ArithExpr::BinaryOp(op, left, right) => {
            let lval = eval_arith(left, state)?;
            let rval = eval_arith(right, state)?;

            match op {
                ArithOp::Add => Ok(lval.wrapping_add(rval)),
                ArithOp::Sub => Ok(lval.wrapping_sub(rval)),
                ArithOp::Mul => Ok(lval.wrapping_mul(rval)),
                ArithOp::Div => {
                    if rval == 0 {
                        Err(anyhow!("Division by zero"))
                    } else {
                        Ok(lval / rval)
                    }
                }
                ArithOp::Mod => {
                    if rval == 0 {
                        Err(anyhow!("Modulo by zero"))
                    } else {
                        Ok(lval % rval)
                    }
                }
                ArithOp::Pow => {
                    if rval < 0 {
                        Err(anyhow!("Negative exponent not supported"))
                    } else {
                        Ok(lval.wrapping_pow(rval as u32))
                    }
                }

                // Bitwise
                ArithOp::BitAnd => Ok(lval & rval),
                ArithOp::BitOr => Ok(lval | rval),
                ArithOp::BitXor => Ok(lval ^ rval),
                ArithOp::ShiftLeft => Ok(lval << rval),
                ArithOp::ShiftRight => Ok(lval >> rval),

                // Comparison (return 0 or 1)
                ArithOp::Lt => Ok(if lval < rval { 1 } else { 0 }),
                ArithOp::Le => Ok(if lval <= rval { 1 } else { 0 }),
                ArithOp::Gt => Ok(if lval > rval { 1 } else { 0 }),
                ArithOp::Ge => Ok(if lval >= rval { 1 } else { 0 }),
                ArithOp::Eq => Ok(if lval == rval { 1 } else { 0 }),
                ArithOp::Ne => Ok(if lval != rval { 1 } else { 0 }),

                // Logical (short-circuit evaluation)
                ArithOp::LogAnd => Ok(if lval != 0 && rval != 0 { 1 } else { 0 }),
                ArithOp::LogOr => Ok(if lval != 0 || rval != 0 { 1 } else { 0 }),

                _ => Err(anyhow!("Invalid binary operator")),
            }
        }
    }
}
```

### 3. Integration with Expansion

**Update `expand()` function in `parser.rs`:**

```rust
pub fn expand(word: &str, state: &mut ShellState) -> Result<String> {
    let mut result = String::new();
    let mut chars = word.chars().peekable();

    while let Some(ch) = chars.next() {
        if ch == '$' {
            if chars.peek() == Some(&'(') {
                chars.next(); // consume '('
                if chars.peek() == Some(&'(') {
                    // Arithmetic expansion: $(( ... ))
                    chars.next(); // consume second '('
                    let expr_str = consume_until(&mut chars, "))")?;
                    let expr = parse_arithmetic(&expr_str)?;
                    let value = eval_arith(&expr, state)?;
                    result.push_str(&value.to_string());
                } else {
                    // Command substitution: $( ... )
                    // ... existing logic ...
                }
            }
            // ... rest of expansion ...
        }
        // ... rest of expansion ...
    }

    Ok(result)
}
```

### 4. Parser Implementation (Recursive Descent)

**Operator precedence parser:**

```rust
// Entry point
fn parse_arithmetic(input: &str) -> Result<ArithExpr> {
    let tokens = tokenize_arith(input)?;
    let mut parser = ArithParser::new(tokens);
    parser.parse_or()
}

// Precedence levels (lowest to highest precedence)
impl ArithParser {
    fn parse_or(&mut self) -> Result<ArithExpr> {
        let mut left = self.parse_and()?;
        while self.match_op(&[ArithOp::LogOr]) {
            let op = self.prev_op();
            let right = self.parse_and()?;
            left = ArithExpr::BinaryOp(op, Box::new(left), Box::new(right));
        }
        Ok(left)
    }

    fn parse_and(&mut self) -> Result<ArithExpr> {
        let mut left = self.parse_bitor()?;
        while self.match_op(&[ArithOp::LogAnd]) {
            let op = self.prev_op();
            let right = self.parse_bitor()?;
            left = ArithExpr::BinaryOp(op, Box::new(left), Box::new(right));
        }
        Ok(left)
    }

    // ... similar methods for each precedence level ...

    fn parse_primary(&mut self) -> Result<ArithExpr> {
        // Literals, variables, parentheses, unary operators
        match self.peek() {
            Token::Number(n) => {
                self.advance();
                Ok(ArithExpr::Literal(*n))
            }
            Token::Ident(name) => {
                self.advance();
                Ok(ArithExpr::Variable(name.clone()))
            }
            Token::LeftParen => {
                self.advance();
                let expr = self.parse_or()?;
                self.expect(Token::RightParen)?;
                Ok(expr)
            }
            Token::Op(op) if op.is_unary() => {
                self.advance();
                let expr = self.parse_unary()?;
                Ok(ArithExpr::UnaryOp(op.clone(), Box::new(expr)))
            }
            _ => Err(anyhow!("Unexpected token in arithmetic expression")),
        }
    }
}
```

## Testing Strategy

### Unit Tests

**Test cases in `arith.rs`:**

```rust
#[cfg(test)]
mod tests {
    #[test]
    fn test_arith_literals() {
        assert_eq!(eval_arith("42"), Ok(42));
        assert_eq!(eval_arith("-10"), Ok(-10));
    }

    #[test]
    fn test_arith_basic_ops() {
        assert_eq!(eval_arith("5 + 3"), Ok(8));
        assert_eq!(eval_arith("10 - 4"), Ok(6));
        assert_eq!(eval_arith("6 * 7"), Ok(42));
        assert_eq!(eval_arith("20 / 4"), Ok(5));
        assert_eq!(eval_arith("17 % 5"), Ok(2));
    }

    #[test]
    fn test_arith_precedence() {
        assert_eq!(eval_arith("2 + 3 * 4"), Ok(14));
        assert_eq!(eval_arith("(2 + 3) * 4"), Ok(20));
        assert_eq!(eval_arith("2 ** 3 + 1"), Ok(9));
        assert_eq!(eval_arith("2 ** (3 + 1)"), Ok(16));
    }

    #[test]
    fn test_arith_comparison() {
        assert_eq!(eval_arith("5 > 3"), Ok(1));
        assert_eq!(eval_arith("5 < 3"), Ok(0));
        assert_eq!(eval_arith("5 == 5"), Ok(1));
        assert_eq!(eval_arith("5 != 3"), Ok(1));
    }

    #[test]
    fn test_arith_logical() {
        assert_eq!(eval_arith("1 && 1"), Ok(1));
        assert_eq!(eval_arith("1 && 0"), Ok(0));
        assert_eq!(eval_arith("1 || 0"), Ok(1));
        assert_eq!(eval_arith("!0"), Ok(1));
        assert_eq!(eval_arith("!5"), Ok(0));
    }

    #[test]
    fn test_arith_bitwise() {
        assert_eq!(eval_arith("5 & 3"), Ok(1));
        assert_eq!(eval_arith("5 | 3"), Ok(7));
        assert_eq!(eval_arith("5 ^ 3"), Ok(6));
        assert_eq!(eval_arith("~5"), Ok(-6));
        assert_eq!(eval_arith("8 << 2"), Ok(32));
        assert_eq!(eval_arith("8 >> 2"), Ok(2));
    }

    #[test]
    fn test_arith_variables() {
        let mut state = ShellState::new("/tmp").unwrap();
        state.set_var("x", "5");
        state.set_var("y", "10");

        assert_eq!(eval_arith_with_state("x + y", &state), Ok(15));
        assert_eq!(eval_arith_with_state("x * 2 + y", &state), Ok(20));
    }

    #[test]
    fn test_arith_division_by_zero() {
        assert!(eval_arith("5 / 0").is_err());
        assert!(eval_arith("5 % 0").is_err());
    }

    #[test]
    fn test_arith_nested() {
        assert_eq!(eval_arith("((5 + 3) * 2) + 1"), Ok(17));
        assert_eq!(eval_arith("2 ** (3 ** 2)"), Ok(512));
    }
}
```

### Integration Tests

**Test in shell execution:**

```bash
# Basic arithmetic
vsh> echo $((5 + 3))
8

# With variables
vsh> x=10
vsh> echo $((x * 2))
20

# In command arguments
vsh> mkdir dir_$((1 + 2))
vsh> ls
dir_3

# Nested in strings
vsh> echo "Result: $((5 * 6))"
Result: 30
```

## Edge Cases

1. **Whitespace handling**: `$(( 5 + 3 ))` same as `$((5+3))`
2. **Nested parentheses**: `$(( (( 5 + 3 )) * 2 ))`
3. **Variable names**: `$((foo))`, `$((foo_bar_123))`
4. **Undefined variables**: Treat as 0 (POSIX behavior)
5. **Overflow**: Wrap around (Rust i64 behavior)
6. **Division by zero**: Error with message
7. **Negative exponents**: Error (not supported in POSIX)
8. **Shift overflow**: Undefined behavior (limit shift amount?)

## Deferred Features

**For later milestones:**

1. **Assignment operators**: `$(( x = 5 ))`, `$(( x += 3 ))`
2. **Increment/decrement**: `$(( ++x ))`, `$(( x-- ))`
3. **Ternary operator**: `$(( x > 0 ? 1 : -1 ))`
4. **Octal/hex literals**: `$((010))` (octal), `$((0x10))` (hex)
5. **Comma operator**: `$(( x = 5, y = 10, x + y ))`

## Success Criteria

- [ ] Parse `$((expression))` correctly
- [ ] Support all arithmetic operators (+, -, *, /, %, **)
- [ ] Support all bitwise operators (&, |, ^, ~, <<, >>)
- [ ] Support all comparison operators (<, >, <=, >=, ==, !=)
- [ ] Support all logical operators (&&, ||, !)
- [ ] Correct operator precedence and associativity
- [ ] Handle parentheses for grouping
- [ ] Variable references work correctly
- [ ] Division by zero produces error
- [ ] All unit tests pass
- [ ] Integration tests pass
- [ ] Documentation complete

## Proven Integration (Future)

When Zig FFI is ready, replace Rust arithmetic with proven module:

**Current** (Rust):
```rust
fn eval_arith(expr: &ArithExpr, state: &ShellState) -> Result<i64>
```

**Future** (Proven SafeArith):
```rust
extern "C" {
    fn idris_eval_arith(expr: *const u8, len: usize) -> i64;
}
```

**Benefits**:
- ✅ Division by zero proven impossible (dependent types)
- ✅ Overflow behavior proven correct
- ✅ Operator precedence proven to match POSIX
- ✅ All edge cases formally verified

See: `proven/src/Proven/SafeArith.idr` (to be created)

---

**Next Steps:**
1. Create `src/arith.rs` with evaluator
2. Add arithmetic parsing to `parser.rs`
3. Integrate with expansion pipeline
4. Write comprehensive tests
5. Update version to 0.12.0
