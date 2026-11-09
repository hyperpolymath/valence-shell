// SPDX-License-Identifier: MPL-2.0
// Minimal Agda-style encoding: a type of types, naturals, addition by
// rewrite rules (how Agda2Dedukti encodes pattern-matching definitions),
// propositional equality, and a theorem whose proof needs the rules to fire.
constant symbol Univ : TYPE;
injective symbol El : Univ → TYPE;

constant symbol Nat : Univ;
constant symbol zero : El Nat;
constant symbol succ : El Nat → El Nat;

symbol add : El Nat → El Nat → El Nat;
rule add zero $n ↪ $n
with add (succ $m) $n ↪ succ (add $m $n);

constant symbol Eq : El Nat → El Nat → Univ;
constant symbol refl : Π x, El (Eq x x);

// Needs `add (succ zero) zero ↪ succ zero` to type-check.
symbol one_plus_zero : El (Eq (add (succ zero) zero) (succ zero)) ≔ refl (succ zero);
