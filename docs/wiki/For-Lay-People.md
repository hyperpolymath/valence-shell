<!--
SPDX-License-Identifier: CC-BY-SA-4.0
Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
-->
# Valence Shell, explained without jargon

*This page assumes no computing background. If you're comfortable with a
command line, you may prefer [For Users](For-Users) or
[For Developers](For-Developers).*

---

## What is a "shell", first of all?

When you use a computer, you usually click on things. Underneath the clicking,
there's an older, more direct way to tell a computer what to do: you **type
commands**, one line at a time — "make a folder called *taxes*", "copy this file
into it", "delete that one". The program that reads those typed commands and
carries them out is called a **shell**. Professionals use shells all day because
typing exact instructions is fast, precise, and repeatable.

The most common shells are called **bash** and **zsh**. You've been near one if
you've ever seen a black window full of green or white text in a film about
hackers. It's far less dramatic than that — it's just a very literal assistant.

## So what's different about *this* shell?

Here is the uncomfortable truth about ordinary shells: **they trust themselves.**

When you tell a normal shell "delete this folder", it assumes its own delete
button works. When you undo something, it *hopes* the undo puts everything back
exactly as it was. Usually it does. But "usually" is doing a lot of work in that
sentence, and when it's your only copy of something important, "usually" isn't
good enough.

Valence Shell replaces "hope" with **proof**.

## What does "proof" mean here?

Think about the difference between two kinds of statement:

- *"I tested this bridge by driving a few trucks over it, and it held."*
- *"I calculated, from the laws of physics, that this bridge holds any truck up
  to 40 tonnes — and here's the math, check it yourself."*

The first is **testing**. It's useful, but it only tells you about the trucks
you actually tried. The second is a **proof**. It covers every truck, including
ones nobody has driven yet.

Almost all software in the world is built the first way: tested, not proven.
Valence Shell is built the second way — at least for its most important
operations. The claim "undoing a *make-folder* gives you back exactly what you
started with" isn't something the authors merely tried a few times. It's
something they **proved mathematically**, the way you'd prove a theorem in a
geometry class — except the proof is checked by a computer program that is very,
very hard to fool.

## Why six proofs instead of one?

Valence Shell doesn't prove things once. It proves the same facts **six separate
times, using six different mathematical "languages"** (they have names like Coq,
Lean, and Agda — you don't need to remember them).

Why the repetition? For the same reason important contracts get read by several
independent lawyers. If one person makes a subtle mistake, the others are likely
to catch it. If all six independent systems — built by different people, on
different principles — agree that a fact is true, the chance that they *all* made
the *same* mistake is vanishingly small. This "prove it several ways" approach is
used for the software inside things like verified aircraft and secure government
systems.

## The two big ideas, in kitchen terms

Valence Shell is organised around two promises:

1. **"You can always undo this."** *(The proven, working part.)*
   Like a pencil with a perfect eraser. Made a folder by mistake? Copied the
   wrong file? The shell can step backwards and put the world back exactly as it
   was — and it can *prove* the eraser leaves no smudge. This is the part that
   works today.

2. **"When you destroy something, it's *really* gone — and you can prove it."**
   *(Designed and mathematically worked out, but not yet built into the running
   program.)*
   Sometimes you *want* permanent deletion — think of the legal "right to be
   forgotten", where a company must genuinely erase your personal data, not just
   hide it. The hard part isn't deleting; it's being able to **prove to an
   outside inspector** that the data is truly unrecoverable. Valence Shell has
   the mathematics for this worked out, but has **not yet finished building it
   into the actual software.**

The project's name for holding both promises honestly is **Mutually Assured
Accountability**: both you *and* an independent checker end up with hard evidence
of what really happened — nobody has to just take anybody's word for it.

## Is it finished? Can I rely on it?

**No, not yet — and the authors are unusually upfront about this.**

- The shell **runs** and does a great deal already.
- The "you can always undo this" proofs are **real and reproducible** — you can
  re-run them on your own computer.
- But the bridge between the *proven math* and the *actual running program* is
  not yet fully mechanically checked — right now it's confirmed by heavy testing
  (roughly 85% confidence), not by an end-to-end proof.
- The "provably destroyed" (right-to-be-forgotten) feature is **designed but not
  built yet**.

So: it's a serious, honest **research prototype**, wonderful for learning,
experimenting, and academic work — but **not something to trust with your only
copy of anything important, and not a replacement for your everyday shell.**

The project publishes its own "here's exactly what is and isn't finished" pages,
which is a good sign of trustworthy engineering rather than marketing:

- [Verification Status & Honest Limits](Verification-Status)
- The [FAQ](https://github.com/hyperpolymath/valence-shell/blob/main/FAQ.adoc)

## Why does any of this matter?

Because we increasingly ask software to do things that *really* matter — handle
medical records, financial transactions, legal evidence, personal data protected
by law. For those jobs, "we tested it and it seemed fine" is a weak foundation.
Valence Shell is part of a small but growing movement that says: for the
operations that truly matter, we should be able to **prove** the software behaves
— and let anyone check the proof.

It's a research project exploring what that future could look like, starting with
one of the oldest and most fundamental tools in computing: the humble shell.

---

## Where to go next

- Curious what it actually looks like to use? → [For Users](For-Users)
- Want the honest "what works / what doesn't" list? → [Verification Status](Verification-Status)
- Writing an article about it? → [For Marketers & Journalists](For-Marketers-and-Journalists)
