// SPDX-License-Identifier: PLMP-1.0-or-later
//! Arithmetic Expression Evaluation
//!
//! Implements POSIX arithmetic expansion for `$((expression))` syntax.
//!
//! # Features
//!
//! - Integer arithmetic: +, -, *, /, %, **
//! - Bitwise operations: &, |, ^, ~, <<, >>
//! - Comparisons: <, >, <=, >=, ==, !=
//! - Logical operations: &&, ||, !
//! - Operator precedence and associativity
//! - Variable references
//!
//! # Examples
//!
//! ```
//! use vsh::arith::{parse_arithmetic, eval_arith};
//! use vsh::state::ShellState;
//!
//! let mut state = ShellState::new("/tmp").unwrap();
//! state.set_variable("x", "5");
//!
//! let expr = parse_arithmetic("x + 10").unwrap();
//! let result = eval_arith(&expr, &state).unwrap();
//! assert_eq!(result, 15);
//! ```

use anyhow::{anyhow, Result};
use crate::state::ShellState;

/// Arithmetic operators
#[derive(Debug, Clone, PartialEq)]
pub enum ArithOp {
    // Arithmetic
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Pow,

    // Bitwise
    BitAnd,
    BitOr,
    BitXor,
    BitNot,
    ShiftLeft,
    ShiftRight,

    // Comparison
    Lt,
    Le,
    Gt,
    Ge,
    Eq,
    Ne,

    // Logical
    LogAnd,
    LogOr,
    LogNot,

    // Unary
    UnaryPlus,
    UnaryMinus,
}

/// Arithmetic expression AST
#[derive(Debug, Clone, PartialEq)]
pub enum ArithExpr {
    /// Literal integer
    Literal(i64),
    /// Variable reference
    Variable(String),
    /// Unary operation
    UnaryOp(ArithOp, Box<ArithExpr>),
    /// Binary operation
    BinaryOp(ArithOp, Box<ArithExpr>, Box<ArithExpr>),
}

/// Tokens for arithmetic expressions
#[derive(Debug, Clone, PartialEq)]
enum Token {
    Number(i64),
    Ident(String),
    Op(ArithOp),
    LeftParen,
    RightParen,
    End,
}

/// Tokenizer for arithmetic expressions
struct Tokenizer {
    input: Vec<char>,
    pos: usize,
}

impl Tokenizer {
    fn new(input: &str) -> Self {
        Self {
            input: input.chars().collect(),
            pos: 0,
        }
    }

    fn peek(&self) -> Option<char> {
        if self.pos < self.input.len() {
            Some(self.input[self.pos])
        } else {
            None
        }
    }

    fn advance(&mut self) -> Option<char> {
        if self.pos < self.input.len() {
            let ch = self.input[self.pos];
            self.pos += 1;
            Some(ch)
        } else {
            None
        }
    }

    fn skip_whitespace(&mut self) {
        while let Some(ch) = self.peek() {
            if ch.is_whitespace() {
                self.advance();
            } else {
                break;
            }
        }
    }

    fn read_number(&mut self) -> Result<i64> {
        let mut num_str = String::new();

        while let Some(ch) = self.peek() {
            if ch.is_ascii_digit() {
                num_str.push(ch);
                self.advance();
            } else {
                break;
            }
        }

        num_str.parse::<i64>()
            .map_err(|_| anyhow!("Invalid number: {}", num_str))
    }

    fn read_ident(&mut self) -> String {
        let mut ident = String::new();

        while let Some(ch) = self.peek() {
            if ch.is_alphanumeric() || ch == '_' {
                ident.push(ch);
                self.advance();
            } else {
                break;
            }
        }

        ident
    }

    fn next_token(&mut self) -> Result<Token> {
        self.skip_whitespace();

        match self.peek() {
            None => Ok(Token::End),

            Some('(') => {
                self.advance();
                Ok(Token::LeftParen)
            }

            Some(')') => {
                self.advance();
                Ok(Token::RightParen)
            }

            Some(ch) if ch.is_ascii_digit() => {
                let num = self.read_number()?;
                Ok(Token::Number(num))
            }

            Some(ch) if ch.is_alphabetic() || ch == '_' => {
                let ident = self.read_ident();
                Ok(Token::Ident(ident))
            }

            Some('+') => {
                self.advance();
                Ok(Token::Op(ArithOp::Add))
            }

            Some('-') => {
                self.advance();
                Ok(Token::Op(ArithOp::Sub))
            }

            Some('*') => {
                self.advance();
                if self.peek() == Some('*') {
                    self.advance();
                    Ok(Token::Op(ArithOp::Pow))
                } else {
                    Ok(Token::Op(ArithOp::Mul))
                }
            }

            Some('/') => {
                self.advance();
                Ok(Token::Op(ArithOp::Div))
            }

            Some('%') => {
                self.advance();
                Ok(Token::Op(ArithOp::Mod))
            }

            Some('&') => {
                self.advance();
                if self.peek() == Some('&') {
                    self.advance();
                    Ok(Token::Op(ArithOp::LogAnd))
                } else {
                    Ok(Token::Op(ArithOp::BitAnd))
                }
            }

            Some('|') => {
                self.advance();
                if self.peek() == Some('|') {
                    self.advance();
                    Ok(Token::Op(ArithOp::LogOr))
                } else {
                    Ok(Token::Op(ArithOp::BitOr))
                }
            }

            Some('^') => {
                self.advance();
                Ok(Token::Op(ArithOp::BitXor))
            }

            Some('~') => {
                self.advance();
                Ok(Token::Op(ArithOp::BitNot))
            }

            Some('!') => {
                self.advance();
                if self.peek() == Some('=') {
                    self.advance();
                    Ok(Token::Op(ArithOp::Ne))
                } else {
                    Ok(Token::Op(ArithOp::LogNot))
                }
            }

            Some('<') => {
                self.advance();
                if self.peek() == Some('<') {
                    self.advance();
                    Ok(Token::Op(ArithOp::ShiftLeft))
                } else if self.peek() == Some('=') {
                    self.advance();
                    Ok(Token::Op(ArithOp::Le))
                } else {
                    Ok(Token::Op(ArithOp::Lt))
                }
            }

            Some('>') => {
                self.advance();
                if self.peek() == Some('>') {
                    self.advance();
                    Ok(Token::Op(ArithOp::ShiftRight))
                } else if self.peek() == Some('=') {
                    self.advance();
                    Ok(Token::Op(ArithOp::Ge))
                } else {
                    Ok(Token::Op(ArithOp::Gt))
                }
            }

            Some('=') => {
                self.advance();
                if self.peek() == Some('=') {
                    self.advance();
                    Ok(Token::Op(ArithOp::Eq))
                } else {
                    Err(anyhow!("Assignment operator not supported yet"))
                }
            }

            Some(ch) => Err(anyhow!("Unexpected character in arithmetic expression: {}", ch)),
        }
    }
}

/// Recursive descent parser for arithmetic expressions
struct Parser {
    tokens: Vec<Token>,
    pos: usize,
}

impl Parser {
    fn new(tokens: Vec<Token>) -> Self {
        Self { tokens, pos: 0 }
    }

    fn peek(&self) -> &Token {
        if self.pos < self.tokens.len() {
            &self.tokens[self.pos]
        } else {
            &Token::End
        }
    }

    fn advance(&mut self) -> &Token {
        if self.pos < self.tokens.len() {
            let token = &self.tokens[self.pos];
            self.pos += 1;
            token
        } else {
            &Token::End
        }
    }

    fn expect(&mut self, expected: Token) -> Result<()> {
        let token = self.advance().clone();
        if token == expected {
            Ok(())
        } else {
            Err(anyhow!("Expected {:?}, got {:?}", expected, token))
        }
    }

    // Entry point: parse || (lowest precedence)
    fn parse_or(&mut self) -> Result<ArithExpr> {
        let mut left = self.parse_and()?;

        while matches!(self.peek(), Token::Op(ArithOp::LogOr)) {
            self.advance();
            let right = self.parse_and()?;
            left = ArithExpr::BinaryOp(ArithOp::LogOr, Box::new(left), Box::new(right));
        }

        Ok(left)
    }

    // Parse &&
    fn parse_and(&mut self) -> Result<ArithExpr> {
        let mut left = self.parse_bitor()?;

        while matches!(self.peek(), Token::Op(ArithOp::LogAnd)) {
            self.advance();
            let right = self.parse_bitor()?;
            left = ArithExpr::BinaryOp(ArithOp::LogAnd, Box::new(left), Box::new(right));
        }

        Ok(left)
    }

    // Parse |
    fn parse_bitor(&mut self) -> Result<ArithExpr> {
        let mut left = self.parse_bitxor()?;

        while matches!(self.peek(), Token::Op(ArithOp::BitOr)) {
            self.advance();
            let right = self.parse_bitxor()?;
            left = ArithExpr::BinaryOp(ArithOp::BitOr, Box::new(left), Box::new(right));
        }

        Ok(left)
    }

    // Parse ^
    fn parse_bitxor(&mut self) -> Result<ArithExpr> {
        let mut left = self.parse_bitand()?;

        while matches!(self.peek(), Token::Op(ArithOp::BitXor)) {
            self.advance();
            let right = self.parse_bitand()?;
            left = ArithExpr::BinaryOp(ArithOp::BitXor, Box::new(left), Box::new(right));
        }

        Ok(left)
    }

    // Parse &
    fn parse_bitand(&mut self) -> Result<ArithExpr> {
        let mut left = self.parse_equality()?;

        while matches!(self.peek(), Token::Op(ArithOp::BitAnd)) {
            self.advance();
            let right = self.parse_equality()?;
            left = ArithExpr::BinaryOp(ArithOp::BitAnd, Box::new(left), Box::new(right));
        }

        Ok(left)
    }

    // Parse == !=
    fn parse_equality(&mut self) -> Result<ArithExpr> {
        let mut left = self.parse_comparison()?;

        loop {
            let op = match self.peek() {
                Token::Op(ArithOp::Eq) => ArithOp::Eq,
                Token::Op(ArithOp::Ne) => ArithOp::Ne,
                _ => break,
            };

            self.advance();
            let right = self.parse_comparison()?;
            left = ArithExpr::BinaryOp(op, Box::new(left), Box::new(right));
        }

        Ok(left)
    }

    // Parse < <= > >=
    fn parse_comparison(&mut self) -> Result<ArithExpr> {
        let mut left = self.parse_shift()?;

        loop {
            let op = match self.peek() {
                Token::Op(ArithOp::Lt) => ArithOp::Lt,
                Token::Op(ArithOp::Le) => ArithOp::Le,
                Token::Op(ArithOp::Gt) => ArithOp::Gt,
                Token::Op(ArithOp::Ge) => ArithOp::Ge,
                _ => break,
            };

            self.advance();
            let right = self.parse_shift()?;
            left = ArithExpr::BinaryOp(op, Box::new(left), Box::new(right));
        }

        Ok(left)
    }

    // Parse << >>
    fn parse_shift(&mut self) -> Result<ArithExpr> {
        let mut left = self.parse_additive()?;

        loop {
            let op = match self.peek() {
                Token::Op(ArithOp::ShiftLeft) => ArithOp::ShiftLeft,
                Token::Op(ArithOp::ShiftRight) => ArithOp::ShiftRight,
                _ => break,
            };

            self.advance();
            let right = self.parse_additive()?;
            left = ArithExpr::BinaryOp(op, Box::new(left), Box::new(right));
        }

        Ok(left)
    }

    // Parse + -
    fn parse_additive(&mut self) -> Result<ArithExpr> {
        let mut left = self.parse_multiplicative()?;

        loop {
            let op = match self.peek() {
                Token::Op(ArithOp::Add) => ArithOp::Add,
                Token::Op(ArithOp::Sub) => ArithOp::Sub,
                _ => break,
            };

            self.advance();
            let right = self.parse_multiplicative()?;
            left = ArithExpr::BinaryOp(op, Box::new(left), Box::new(right));
        }

        Ok(left)
    }

    // Parse * / %
    fn parse_multiplicative(&mut self) -> Result<ArithExpr> {
        let mut left = self.parse_power()?;

        loop {
            let op = match self.peek() {
                Token::Op(ArithOp::Mul) => ArithOp::Mul,
                Token::Op(ArithOp::Div) => ArithOp::Div,
                Token::Op(ArithOp::Mod) => ArithOp::Mod,
                _ => break,
            };

            self.advance();
            let right = self.parse_power()?;
            left = ArithExpr::BinaryOp(op, Box::new(left), Box::new(right));
        }

        Ok(left)
    }

    // Parse ** (right-associative)
    fn parse_power(&mut self) -> Result<ArithExpr> {
        let left = self.parse_unary()?;

        if matches!(self.peek(), Token::Op(ArithOp::Pow)) {
            self.advance();
            let right = self.parse_power()?; // Right-associative recursion
            Ok(ArithExpr::BinaryOp(ArithOp::Pow, Box::new(left), Box::new(right)))
        } else {
            Ok(left)
        }
    }

    // Parse unary operators: ! ~ + -
    fn parse_unary(&mut self) -> Result<ArithExpr> {
        match self.peek() {
            Token::Op(ArithOp::LogNot) => {
                self.advance();
                let expr = self.parse_unary()?;
                Ok(ArithExpr::UnaryOp(ArithOp::LogNot, Box::new(expr)))
            }
            Token::Op(ArithOp::BitNot) => {
                self.advance();
                let expr = self.parse_unary()?;
                Ok(ArithExpr::UnaryOp(ArithOp::BitNot, Box::new(expr)))
            }
            Token::Op(ArithOp::Add) => {
                self.advance();
                let expr = self.parse_unary()?;
                Ok(ArithExpr::UnaryOp(ArithOp::UnaryPlus, Box::new(expr)))
            }
            Token::Op(ArithOp::Sub) => {
                self.advance();
                let expr = self.parse_unary()?;
                Ok(ArithExpr::UnaryOp(ArithOp::UnaryMinus, Box::new(expr)))
            }
            _ => self.parse_primary(),
        }
    }

    // Parse primary: literals, variables, parentheses
    fn parse_primary(&mut self) -> Result<ArithExpr> {
        match self.advance().clone() {
            Token::Number(n) => Ok(ArithExpr::Literal(n)),

            Token::Ident(name) => Ok(ArithExpr::Variable(name)),

            Token::LeftParen => {
                let expr = self.parse_or()?;
                self.expect(Token::RightParen)?;
                Ok(expr)
            }

            token => Err(anyhow!("Unexpected token in arithmetic expression: {:?}", token)),
        }
    }
}

/// Parse arithmetic expression from string
pub fn parse_arithmetic(input: &str) -> Result<ArithExpr> {
    let mut tokenizer = Tokenizer::new(input);
    let mut tokens = Vec::new();

    loop {
        let token = tokenizer.next_token()?;
        if token == Token::End {
            break;
        }
        tokens.push(token);
    }

    let mut parser = Parser::new(tokens);
    parser.parse_or()
}

/// Evaluate arithmetic expression
pub fn eval_arith(expr: &ArithExpr, state: &ShellState) -> Result<i64> {
    match expr {
        ArithExpr::Literal(n) => Ok(*n),

        ArithExpr::Variable(name) => {
            let value = state.get_variable(name).unwrap_or("0");
            value
                .parse::<i64>()
                .map_err(|_| anyhow!("Variable {} is not a valid integer: {}", name, value))
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

            // Short-circuit evaluation for logical operators
            match op {
                ArithOp::LogAnd => {
                    if lval == 0 {
                        return Ok(0);
                    }
                    let rval = eval_arith(right, state)?;
                    return Ok(if rval != 0 { 1 } else { 0 });
                }
                ArithOp::LogOr => {
                    if lval != 0 {
                        return Ok(1);
                    }
                    let rval = eval_arith(right, state)?;
                    return Ok(if rval != 0 { 1 } else { 0 });
                }
                _ => {}
            }

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

                // Logical handled above with short-circuit
                ArithOp::LogAnd | ArithOp::LogOr => unreachable!(),

                _ => Err(anyhow!("Invalid binary operator")),
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_arith_literals() {
        let expr = parse_arithmetic("42").unwrap();
        assert_eq!(expr, ArithExpr::Literal(42));

        let state = ShellState::new("/tmp").unwrap();
        assert_eq!(eval_arith(&expr, &state).unwrap(), 42);
    }

    #[test]
    fn test_arith_basic_ops() {
        let state = ShellState::new("/tmp").unwrap();

        assert_eq!(eval_arith(&parse_arithmetic("5 + 3").unwrap(), &state).unwrap(), 8);
        assert_eq!(eval_arith(&parse_arithmetic("10 - 4").unwrap(), &state).unwrap(), 6);
        assert_eq!(eval_arith(&parse_arithmetic("6 * 7").unwrap(), &state).unwrap(), 42);
        assert_eq!(eval_arith(&parse_arithmetic("20 / 4").unwrap(), &state).unwrap(), 5);
        assert_eq!(eval_arith(&parse_arithmetic("17 % 5").unwrap(), &state).unwrap(), 2);
    }

    #[test]
    fn test_arith_precedence() {
        let state = ShellState::new("/tmp").unwrap();

        assert_eq!(eval_arith(&parse_arithmetic("2 + 3 * 4").unwrap(), &state).unwrap(), 14);
        assert_eq!(eval_arith(&parse_arithmetic("(2 + 3) * 4").unwrap(), &state).unwrap(), 20);
        assert_eq!(eval_arith(&parse_arithmetic("2 ** 3 + 1").unwrap(), &state).unwrap(), 9);
        assert_eq!(eval_arith(&parse_arithmetic("2 ** (3 + 1)").unwrap(), &state).unwrap(), 16);
    }

    #[test]
    fn test_arith_power_right_associative() {
        let state = ShellState::new("/tmp").unwrap();

        // 2 ** 3 ** 2 = 2 ** (3 ** 2) = 2 ** 9 = 512
        assert_eq!(eval_arith(&parse_arithmetic("2 ** 3 ** 2").unwrap(), &state).unwrap(), 512);
    }

    #[test]
    fn test_arith_comparison() {
        let state = ShellState::new("/tmp").unwrap();

        assert_eq!(eval_arith(&parse_arithmetic("5 > 3").unwrap(), &state).unwrap(), 1);
        assert_eq!(eval_arith(&parse_arithmetic("5 < 3").unwrap(), &state).unwrap(), 0);
        assert_eq!(eval_arith(&parse_arithmetic("5 == 5").unwrap(), &state).unwrap(), 1);
        assert_eq!(eval_arith(&parse_arithmetic("5 != 3").unwrap(), &state).unwrap(), 1);
        assert_eq!(eval_arith(&parse_arithmetic("5 >= 5").unwrap(), &state).unwrap(), 1);
        assert_eq!(eval_arith(&parse_arithmetic("5 <= 4").unwrap(), &state).unwrap(), 0);
    }

    #[test]
    fn test_arith_logical() {
        let state = ShellState::new("/tmp").unwrap();

        assert_eq!(eval_arith(&parse_arithmetic("1 && 1").unwrap(), &state).unwrap(), 1);
        assert_eq!(eval_arith(&parse_arithmetic("1 && 0").unwrap(), &state).unwrap(), 0);
        assert_eq!(eval_arith(&parse_arithmetic("1 || 0").unwrap(), &state).unwrap(), 1);
        assert_eq!(eval_arith(&parse_arithmetic("0 || 0").unwrap(), &state).unwrap(), 0);
        assert_eq!(eval_arith(&parse_arithmetic("!0").unwrap(), &state).unwrap(), 1);
        assert_eq!(eval_arith(&parse_arithmetic("!5").unwrap(), &state).unwrap(), 0);
    }

    #[test]
    fn test_arith_bitwise() {
        let state = ShellState::new("/tmp").unwrap();

        assert_eq!(eval_arith(&parse_arithmetic("5 & 3").unwrap(), &state).unwrap(), 1);
        assert_eq!(eval_arith(&parse_arithmetic("5 | 3").unwrap(), &state).unwrap(), 7);
        assert_eq!(eval_arith(&parse_arithmetic("5 ^ 3").unwrap(), &state).unwrap(), 6);
        assert_eq!(eval_arith(&parse_arithmetic("~5").unwrap(), &state).unwrap(), -6);
        assert_eq!(eval_arith(&parse_arithmetic("8 << 2").unwrap(), &state).unwrap(), 32);
        assert_eq!(eval_arith(&parse_arithmetic("8 >> 2").unwrap(), &state).unwrap(), 2);
    }

    #[test]
    fn test_arith_variables() {
        let mut state = ShellState::new("/tmp").unwrap();
        state.set_variable("x", "5");
        state.set_variable("y", "10");

        assert_eq!(eval_arith(&parse_arithmetic("x + y").unwrap(), &state).unwrap(), 15);
        assert_eq!(eval_arith(&parse_arithmetic("x * 2 + y").unwrap(), &state).unwrap(), 20);
    }

    #[test]
    fn test_arith_undefined_variable() {
        let state = ShellState::new("/tmp").unwrap();

        // Undefined variables should be treated as 0
        assert_eq!(eval_arith(&parse_arithmetic("undefined_var + 5").unwrap(), &state).unwrap(), 5);
    }

    #[test]
    fn test_arith_division_by_zero() {
        let state = ShellState::new("/tmp").unwrap();

        assert!(eval_arith(&parse_arithmetic("5 / 0").unwrap(), &state).is_err());
        assert!(eval_arith(&parse_arithmetic("5 % 0").unwrap(), &state).is_err());
    }

    #[test]
    fn test_arith_nested() {
        let state = ShellState::new("/tmp").unwrap();

        assert_eq!(eval_arith(&parse_arithmetic("((5 + 3) * 2) + 1").unwrap(), &state).unwrap(), 17);
        assert_eq!(eval_arith(&parse_arithmetic("2 ** (3 ** 2)").unwrap(), &state).unwrap(), 512);
    }

    #[test]
    fn test_arith_unary_minus() {
        let state = ShellState::new("/tmp").unwrap();

        assert_eq!(eval_arith(&parse_arithmetic("-5").unwrap(), &state).unwrap(), -5);
        assert_eq!(eval_arith(&parse_arithmetic("-(5 + 3)").unwrap(), &state).unwrap(), -8);
        assert_eq!(eval_arith(&parse_arithmetic("10 + -5").unwrap(), &state).unwrap(), 5);
    }

    #[test]
    fn test_arith_whitespace() {
        let state = ShellState::new("/tmp").unwrap();

        assert_eq!(eval_arith(&parse_arithmetic("  5  +  3  ").unwrap(), &state).unwrap(), 8);
        assert_eq!(eval_arith(&parse_arithmetic("( ( 5 + 3 ) * 2 )").unwrap(), &state).unwrap(), 16);
    }
}
