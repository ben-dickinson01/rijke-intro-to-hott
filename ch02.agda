{-# OPTIONS --without-K #-}
module ch02 where

open import Agda.Primitive public

-- universe levels, generalised implicitly in every chapter
variable
  ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ : Level

-- Def 2.2.3

id : {A : Set ℓ} → A → A
id a = a

-- Def 2.2.5

infixr 9 _∘_
_∘_ : {A : Set ℓ} {B : Set ℓ₁} {C : Set ℓ₂} → (g : B → C) → (f : A → B) → (A → C)
(g ∘ f) a = g (f a)


-- Exercises
-- 2.3
const : {A : Set ℓ} {B : Set ℓ₁} → {b : B} → A → B
const {A = A} {B = B} {b = b} x = b

-- 2.4
σ : {A : Set ℓ} {B : Set ℓ₁} → {C : A → B → Set ℓ₂} → ((a : A) → (b : B) → Set ℓ₂) → (b : B) → (a : A) → Set ℓ₂
σ x b a = x a b
