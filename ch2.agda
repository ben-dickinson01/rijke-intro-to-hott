module ch2 where

-- Def 2.2.3

id : {A : Set} → A → A
id a = a

-- Def 2.2.5

infixr 9 _∘_
_∘_ : {A B C : Set} → (g : B → C) → (f : A → B) → (A → C)
(g ∘ f) a = g (f a)  


-- Exercises
-- 2.3
const : {A B : Set} → {b : B} → A → B
const {A} {B} {b} x = b

-- 2.4
σ : {A B : Set} → {C : A → B → Set} → ((a : A) → (b : B) → Set) → (b : B) → (a : A) → Set
σ x b a = x a b
