module ch6 where

open import ch5 public
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_) public

Eq-ℕ : ℕ → ℕ → Set (lzero)
Eq-ℕ 0ℕ 0ℕ = Unit
Eq-ℕ (succℕ n) 0ℕ = Empty
Eq-ℕ 0ℕ (succℕ m) = Empty
Eq-ℕ (succℕ n) (succℕ m) = Eq-ℕ n m

rfl-Eqℕ : (n : ℕ) → Eq-ℕ n n
rfl-Eqℕ 0ℕ = *
rfl-Eqℕ (succℕ n) = rfl-Eqℕ n

≡-iff-Eqℕ : (m n : ℕ) → (m ≡ n) ↔ (Eq-ℕ m n)
≡-iff-Eqℕ m n = (to m n , from m n) where
  to : (m n : ℕ) → (m ≡ n) → (Eq-ℕ m n)
  to 0ℕ n refl = *
  to (succℕ m) n refl = to m m refl

  from : (m n : ℕ) → Eq-ℕ m n → (m ≡ n)
  from 0ℕ 0ℕ p = refl
  from (succℕ m) (succℕ n) p = ap succℕ (from m n p)

succ-injℕ : (m n : ℕ) → (m ≡ n) ↔ (succℕ m ≡ succℕ n)
succ-injℕ m n = (to m n , from m n) where
  to : (m n : ℕ) → (m ≡ n) → (succℕ m ≡ succℕ n)
  to m n refl = refl

  from : (m n : ℕ) → (succℕ m ≡ succℕ n) → (m ≡ n)
  from m n refl = refl

0-ne-succℕ : (m : ℕ) → ¬ (0ℕ ≡ succℕ m)
0-ne-succℕ 0ℕ ()
0-ne-succℕ (succℕ m) ()

-- Exercises
add-injℕ : (m n k : ℕ) → (m ≡ n) ↔ (m +ℕ k ≡ n +ℕ k)
add-injℕ m n k = (to m n k , from m n k) where
  to : (m n k : ℕ) → (m ≡ n) → (m +ℕ k ≡ n +ℕ k)
  to 0ℕ n k refl = refl
  to (succℕ m) n k refl = refl

  from : (m n k : ℕ) → (m +ℕ k ≡ n +ℕ k) → (m ≡ n)
  from m n 0ℕ p = p
  from m n (succℕ k) p = from m n k ((proj₂ (succ-injℕ (m +ℕ k) (n +ℕ k))) p)

mul-injℕ : (m n k : ℕ) → (m ≡ n) ↔ (m ·ℕ (succℕ k)) ≡ (n ·ℕ (succℕ k))
mul-injℕ m n k = (to m n k , from m n k) where
  to : (m n k : ℕ) → (m ≡ n) → (m ·ℕ (succℕ k)) ≡ (n ·ℕ (succℕ k))
  to m n k refl = refl

  from : (m n k : ℕ) → (m ·ℕ (succℕ k)) ≡ (n ·ℕ (succℕ k)) → m ≡ n
  from m n 0ℕ refl = refl
  from m n (succℕ k) p = from m n k {!!}
