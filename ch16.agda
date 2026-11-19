{-# OPTIONS --without-K #-}
module ch16 where

open import ch15 public

-- 15.1 Counting in type theory
count : (A : Set ℓ) → Set _
count A = Σ ℕ (λ k → Fin k ≃ A)

-- Example 16.1.2
count-Fin : (k : ℕ) → count (Fin k)
count-Fin k = k , (id , is-equiv-id (Fin k))

-- Example 16.1.3
count-zero-iff-empty : {A : Set ℓ} → (c : count A) → (proj₁ c ≡ 0ℕ) ↔ ¬ A
count-zero-iff-empty (k , (f , (_ , (r , _)))) =
  (λ { refl a → r a }) , λ na → empty-Fin-zero k (λ x → na (f x))
  where
    empty-Fin-zero : (n : ℕ) → ¬ (Fin n) → n ≡ 0ℕ
    empty-Fin-zero 0ℕ _ = refl
    empty-Fin-zero (succℕ n) ne = ex-falso (ne (inr *))
