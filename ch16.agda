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

count-1-to-contr : (A : Set ℓ) → (c : count A) → proj₁ c ≡ 1ℕ → is-contr A
count-1-to-contr A (.1ℕ , f) refl =
  is-contr-codomain-equiv (proj₁ f) (inr * , λ { (inl ()) ; (inr *) → refl }) (proj₂ f)

contr-to-count-1 : (A : Set ℓ) → (c : count A) → is-contr A → proj₁ c ≡ 1ℕ
contr-to-count-1 A (0ℕ , f) (a , xeqa) = ex-falso (proj₁ (proj₁ (proj₂ f)) a)
contr-to-count-1 A (succℕ 0ℕ , f) (a , xeqa) = refl
contr-to-count-1 A (succℕ (succℕ n) , e) (a , xeqa) = ex-falso (Fin-2+-not-contr n (is-contr-domain-equiv (proj₁ e) (a , xeqa) (proj₂ e)))

