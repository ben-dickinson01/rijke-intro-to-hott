# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

Agda formalization of exercises from Rijke's *Introduction to Homotopy Type Theory* (arXiv:2212.11082). Each chapter's definitions and exercises are in a corresponding `chN.agda` file.

## Commands

Type-check a file (also type-checks all its dependencies):
```
agda ch6.agda
```

Load a specific file in interactive mode (emacs agda-mode or VS Code with the Agda extension):
- Emacs: `C-c C-l` to load/type-check the current buffer
- VS Code: the Agda extension loads on file open

There is no separate build step or test runner — Agda's type checker is the correctness mechanism.

## Module Architecture

Each chapter module imports all prior chapters via `open import chN public`, forming a linear dependency chain:

| File | Contents |
|------|----------|
| `ch2.agda` | Identity function, composition (`_∘_`) |
| `ch3.agda` | Natural numbers (`ℕ`), arithmetic (`+ℕ`, `·ℕ`, `^ℕ`), combinatorics (`choose`, `fibℕ`, etc.) |
| `ch4.agda` | `Unit`/`Empty`, coproducts (`_⊎_`), integers (`ℤ`), sigma types (`Σ`), products (`_×_`), booleans (`𝟚`), logical connectives (`_↔_`, `¬`) |
| `ch5.agda` | Identity type (`_≡_`), path operations (`concat`, `inv`, `ap`, `tr`, `apd`), arithmetic laws for `ℕ` and `ℤ` |
| `ch6.agda` | Observational equality (`Eq-ℕ`, `Eq-𝟚`), ordering (`_≤ℕ_`), universe levels via `Agda.Primitive` |

## Conventions

- Unicode subscripts are used throughout: `0ℕ`, `succℕ`, `+ℕ`, `·ℤ`, `𝟙`, `𝟘`, `𝟚`
- Exercises are marked with comments like `-- Exercises` and `-- N.M`
- Path concatenation uses `concat` (not `_∙_`); path inversion uses `inv`
- `ch6.agda` is the only file that imports `Agda.Primitive` for universe polymorphism (`Level`, `lzero`, `lsuc`, `_⊔_`)
- Incomplete proofs use Agda holes (`{! !}`) — do not remove these without filling them
