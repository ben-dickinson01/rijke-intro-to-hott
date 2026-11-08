[![Typecheck](https://github.com/ben-dickinson01/rijke-intro-to-hott/actions/workflows/typecheck.yml/badge.svg)](https://github.com/ben-dickinson01/rijke-intro-to-hott/actions/workflows/typecheck.yml)

# Rijke's *Introduction to Homotopy Type Theory* in Agda

A formalisation in Agda of Egbert Rijke's *Introduction to Homotopy Type Theory*, following the version on arXiv ([arXiv:2212.11082](https://arxiv.org/abs/2212.11082)). I started it to learn homotopy type theory and Agda together, and I am adding to it as I work through the book.  
Generative AI (Claude) has been used for clarifying parts of the book and asking related questions to help understanding. Claude Code has been used for organisational and setup tasks only (project setup, renaming and reorganising definitions, removing duplicates, formatting). All of the mathematics was written by me.    

## Progress

| File | Chapter | Status |
|---|---|---|
| [ch02.agda](ch02.agda) | 2 Dependent function types | done |
| [ch03.agda](ch03.agda) | 3 The natural numbers | done |
| [ch04.agda](ch04.agda) | 4 More inductive types | done |
| [ch05.agda](ch05.agda) | 5 Identity types | done |
| [ch06.agda](ch06.agda) | 6 Universes | done |
| [ch07.agda](ch07.agda) | 7 Modular arithmetic via the Curry–Howard interpretation | done |
| [ch08.agda](ch08.agda) | 8 Decidability in elementary number theory | done |
| [ch09.agda](ch09.agda) | 9 Equivalences | done |
| [ch10.agda](ch10.agda) | 10 Contractible types and contractible maps | done |
| [ch11.agda](ch11.agda) | 11 The fundamental theorem of identity types | done |
| [ch12.agda](ch12.agda) | 12 Propositions, sets, and the higher truncation levels | done |
| [ch13.agda](ch13.agda) | 13 Function extensionality | done |
| [ch14.agda](ch14.agda) | 14 Propositional truncations | done |
| [ch15.agda](ch15.agda) | 15 Image factorizations | §15.1–15.3, Exercises 15.1–15.2 |

Chapter 1 sets out the rules of dependent type theory, which Agda provides, so it has no file.

## Selected results

- **Infinitely many primes p ≡ 3 mod 4** (Exercise 8.13), in elementary number theory with decidability — [ch08.agda](ch08.agda), `infinitely-many-4k+3-primesℕ`
- **The fundamental theorem of identity types** (Theorem 11.2.2) — [ch11.agda](ch11.agda), `total-contr-to-fam-equiv`
- **The structure identity principle** (Theorem 11.6.2), for identity systems on Σ-types — [ch11.agda](ch11.agda), `dep-id-sys-to-Σ-id-sys` and `Σ-id-sys-to-dep-id-sys`
- **Hedberg's theorem**: types with decidable equality are sets — [ch12.agda](ch12.agda), `Hedberg`
- **Equivalent forms of function extensionality** (Theorem 13.1.2) — [ch13.agda](ch13.agda)
- **Kraus's theorem** (Theorem 14.4.6): weakly constant maps into a set factor through the propositional truncation — [ch14.agda](ch14.agda)
- **The surjection–embedding factorisation** (Theorem 15.2.5, Corollary 15.2.6): every map factors uniquely as a surjection followed by an embedding — [ch15.agda](ch15.agda), `surj-emb-fact-uniq`
- **Cantor's theorem** (Theorem 15.3.2): there is no surjection from a type onto its power set — [ch15.agda](ch15.agda), `no-surj-to-pow-set`

## Setup

- Every file uses `--without-K`, and definitions are universe-polymorphic (`Set ℓ`) throughout.
- Each chapter imports the previous one, so `ch15.agda` checks the whole development.
- Comments label each definition with the book's numbering (e.g. `-- Theorem 15.2.5`), so the code can be read alongside the book.

### Postulates

The development assumes only the following, each matching an axiom or construction the book introduces at that point:

- **Function extensionality** (`fun-ext`, ch13): `htpy-eq` is an equivalence (Chapter 13).
- **Propositional truncation** (`∥_∥`, `η`, `α` and its induction principle, ch14): the book's higher inductive type (Section 14.2).
- **The interval** (`𝕀`, `source`, `target`, `path`, ch14): used only in Exercise 14.9.

Further higher inductive types will be postulated in their relevant chapter.

## Checking

Tested with Agda 2.8.0. To typecheck everything:

```
agda ch15.agda
```

CI typechecks every chapter on each push.
