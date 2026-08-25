{-# OPTIONS --without-K #-}
module ch06 where

open import ch05 public
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_) public

Eq-ℕ : ℕ → ℕ → Set (lzero)
Eq-ℕ 0ℕ 0ℕ = Unit
Eq-ℕ (succℕ n) 0ℕ = Empty
Eq-ℕ 0ℕ (succℕ m) = Empty
Eq-ℕ (succℕ n) (succℕ m) = Eq-ℕ n m

rfl-Eq-ℕ : (n : ℕ) → Eq-ℕ n n
rfl-Eq-ℕ 0ℕ = *
rfl-Eq-ℕ (succℕ n) = rfl-Eq-ℕ n

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

zero-ne-succℕ : (m : ℕ) → ¬ (0ℕ ≡ succℕ m)
zero-ne-succℕ 0ℕ ()
zero-ne-succℕ (succℕ m) ()

-- Exercises
add-injℕ : (m n k : ℕ) → (m ≡ n) ↔ (m +ℕ k ≡ n +ℕ k)
add-injℕ m n k = (to m n k , from m n k) where
  to : (m n k : ℕ) → (m ≡ n) → (m +ℕ k ≡ n +ℕ k)
  to 0ℕ n k refl = refl
  to (succℕ m) n k refl = refl

  from : (m n k : ℕ) → (m +ℕ k ≡ n +ℕ k) → (m ≡ n)
  from m n 0ℕ p = p
  from m n (succℕ k) p = from m n k ((proj₂ (succ-injℕ (m +ℕ k) (n +ℕ k))) p)

eq-add-eqℕ : (m n k l : ℕ) → (m ≡ n) → (k ≡ l) → (m +ℕ k ≡ n +ℕ l)
eq-add-eqℕ m n k l refl refl = refl

mul-injℕ : (m n k : ℕ) → (m ≡ n) ↔ (m ·ℕ (succℕ k)) ≡ (n ·ℕ (succℕ k))
mul-injℕ m n k = (to m n k , from m n k) where
  to : (m n k : ℕ) → (m ≡ n) → (m ·ℕ (succℕ k)) ≡ (n ·ℕ (succℕ k))
  to m n k refl = refl

  from : (m n k : ℕ) → (m ·ℕ (succℕ k)) ≡ (n ·ℕ (succℕ k)) → m ≡ n
  from 0ℕ 0ℕ k _ = refl
  from 0ℕ (succℕ n) k p = ex-falso (zero-ne-succℕ (n +ℕ succℕ n ·ℕ k) (concat (inv (zero-mulℕ k)) (concat (inv (zero-addℕ (0ℕ ·ℕ k))) (concat p (succ-addℕ n (succℕ n ·ℕ k))))))
  from (succℕ m) 0ℕ k p = ex-falso (zero-ne-succℕ (m +ℕ succℕ m ·ℕ k) (concat (inv (zero-mulℕ k)) (concat (inv (zero-addℕ (0ℕ ·ℕ k))) (concat (inv p) (succ-addℕ m (succℕ m ·ℕ k))))))
  from (succℕ m) (succℕ n) k p = ap succℕ (from m n k (proj₂ (add-injℕ (m ·ℕ succℕ k) (n ·ℕ succℕ k) (succℕ k)) (concat (inv (succ-mulℕ m (succℕ k))) (concat p (succ-mulℕ n (succℕ k))))))

add-to-zeroℕ : (m n : ℕ) → (m +ℕ n ≡ 0ℕ) → (m ≡ 0ℕ) × (n ≡ 0ℕ)
add-to-zeroℕ 0ℕ 0ℕ refl = (refl , refl)
add-to-zeroℕ 0ℕ (succℕ n) ()
add-to-zeroℕ (succℕ m) 0ℕ ()
add-to-zeroℕ (succℕ m) (succℕ n) ()

mul-to-zeroℕ : (m n : ℕ) → (m ·ℕ n ≡ 0ℕ) → (m ≡ 0ℕ) ⊎ (n ≡ 0ℕ)
mul-to-zeroℕ 0ℕ 0ℕ refl = inl refl
mul-to-zeroℕ 0ℕ (succℕ n) p = inl refl
mul-to-zeroℕ (succℕ m) 0ℕ refl = inr refl
mul-to-zeroℕ (succℕ m) (succℕ n) p = ex-falso (zero-ne-succℕ (m +ℕ succℕ m ·ℕ n) (inv (concat (inv (succ-addℕ m (succℕ m ·ℕ n))) p)) )

mul-to-oneℕ : (m n : ℕ) → (m ·ℕ n ≡ 1ℕ) → (m ≡ 1ℕ) × (n ≡ 1ℕ)
mul-to-oneℕ 0ℕ (succℕ n) p = ex-falso (zero-ne-succℕ (0ℕ) (concat (inv (zero-mulℕ n)) (concat (inv (zero-addℕ (0ℕ ·ℕ n))) p)))
mul-to-oneℕ (succℕ m) (succℕ n) p = (ap succℕ (proj₁ (add-to-zeroℕ m (succℕ m ·ℕ n) (proj₂ (succ-injℕ (m +ℕ succℕ m ·ℕ n) 0ℕ) (concat (inv (succ-addℕ m (succℕ m ·ℕ n))) p)))) , ap succℕ (proj₁ (add-to-zeroℕ n (succℕ n ·ℕ m) (proj₂ (succ-injℕ (n +ℕ succℕ n ·ℕ m) 0ℕ) (concat (inv (succ-addℕ n (succℕ n ·ℕ m))) (inv (concat (inv p) (inv (mul-commℕ (succℕ n) (succℕ m))))))))))

add-ne-selfℕ : (m n : ℕ) → ¬ (m ≡ (m +ℕ (n +ℕ 1ℕ)))
add-ne-selfℕ (succℕ m) (succℕ n) p = add-ne-selfℕ m (succℕ n) (proj₂ (succ-injℕ m (m +ℕ (succℕ n +ℕ 1ℕ))) (concat p (succ-addℕ m (succℕ n +ℕ 1ℕ))))

mul-ne-selfℕ : (m n : ℕ) → ¬ ((m +ℕ 1ℕ) ≡ (m +ℕ 1ℕ) ·ℕ (n +ℕ 2ℕ))
mul-ne-selfℕ 0ℕ (succℕ n) p = zero-ne-succℕ (n +ℕ 1ℕ) (proj₂ (succ-injℕ 0ℕ (n +ℕ 2ℕ)) (concat p (concat (ap (λ x → x ·ℕ (succℕ n +ℕ 2ℕ)) (zero-addℕ 1ℕ)) (concat (one-mulℕ (succℕ n +ℕ 2ℕ)) (succ-addℕ n 2ℕ)))) )
mul-ne-selfℕ (succℕ m) 0ℕ p = ex-falso (zero-ne-succℕ (succℕ m) (proj₂ (add-injℕ 0ℕ (succℕ (succℕ m)) m) (concat (zero-addℕ m) (proj₂ (succ-injℕ m (succℕ (succℕ m) +ℕ m)) (proj₂ (succ-injℕ (succℕ m) (succℕ (succℕ (succℕ m) +ℕ m))) (concat p (concat (ap (λ x → (succℕ m +ℕ 1ℕ) ·ℕ x) (zero-addℕ 2ℕ)) (inv (concat (inv (ap succℕ (add-succℕ (succℕ (succℕ m)) m))) (add-succℕ (succℕ (succℕ m)) (succℕ m))))))) ))))
mul-ne-selfℕ (succℕ m) (succℕ n) p = ex-falso (zero-ne-succℕ (succℕ m +ℕ (succℕ (succℕ m) +ℕ succℕ (succℕ m) ·ℕ n)) (proj₂ (add-injℕ 0ℕ (succℕ (succℕ m +ℕ (succℕ (succℕ m) +ℕ succℕ (succℕ m) ·ℕ n))) (succℕ (succℕ m))) (concat (zero-addℕ (succℕ (succℕ m))) (concat p (concat (ap (λ x → (succℕ m +ℕ 1ℕ) ·ℕ x) (succ-addℕ n 2ℕ)) (concat (add-commℕ (succℕ m +ℕ 1ℕ) ((succℕ m +ℕ 1ℕ) ·ℕ (n +ℕ 2ℕ))) (proj₁ (add-injℕ ((succℕ m +ℕ 1ℕ) ·ℕ (n +ℕ 2ℕ)) (succℕ (succℕ m +ℕ (succℕ (succℕ m) +ℕ succℕ (succℕ m) ·ℕ n))) (succℕ (succℕ m))) (inv (concat (inv (succ-addℕ (succℕ m) (succℕ (succℕ m) +ℕ succℕ (succℕ m) ·ℕ n))) (concat (add-commℕ (succℕ (succℕ m)) (succℕ (succℕ m) +ℕ succℕ (succℕ m) ·ℕ n)) (inv (concat (add-commℕ (succℕ m +ℕ 1ℕ) ((succℕ m +ℕ 1ℕ) ·ℕ (n +ℕ 1ℕ))) (proj₁ (add-injℕ ((succℕ m +ℕ 1ℕ) ·ℕ (n +ℕ 1ℕ)) (succℕ (succℕ m) +ℕ succℕ (succℕ m) ·ℕ n) (succℕ (succℕ m))) refl)))))))))))))

Eq-𝟚 : 𝟚 → 𝟚 → Set
Eq-𝟚 true true = 𝟙
Eq-𝟚 true false = 𝟘
Eq-𝟚 false true = 𝟘
Eq-𝟚 false false = 𝟙

≡-iff-Eq𝟚 : (x y : 𝟚) → (x ≡ y) ↔ (Eq-𝟚 x y)
≡-iff-Eq𝟚 x y = (to x y , from x y)
  where
  to : (x y : 𝟚) → (x ≡ y) → (Eq-𝟚 x y)
  to true true refl = *
  to false false refl = *

  from : (x y : 𝟚) → (Eq-𝟚 x y) → (x ≡ y)
  from true true * = refl
  from false false * = refl

neg-ne-self𝟚 : (b : 𝟚) → ¬ (b ≡ neg𝟚 b)
neg-ne-self𝟚 true ()
neg-ne-self𝟚 false ()

𝟚-cases : (b : 𝟚) → (b ≡ false) ⊎ (b ≡ true)
𝟚-cases true = inr refl
𝟚-cases false = inl refl

infix 4 _≤ℕ_
_≤ℕ_ : ℕ → ℕ → Set
0ℕ ≤ℕ 0ℕ = 𝟙
0ℕ ≤ℕ succℕ y = 𝟙
succℕ x ≤ℕ 0ℕ = 𝟘
succℕ x ≤ℕ succℕ y = x ≤ℕ y

≤-rflℕ : (x : ℕ) → (x ≤ℕ x)
≤-rflℕ 0ℕ = *
≤-rflℕ (succℕ x) = ≤-rflℕ x

≤-antisymℕ : (x y : ℕ) → (x ≤ℕ y) → (y ≤ℕ x) → (x ≡ y)
≤-antisymℕ 0ℕ 0ℕ * * = refl
≤-antisymℕ (succℕ x) (succℕ y) x≤y y≤x = ap succℕ (≤-antisymℕ x y x≤y y≤x)

≤-transℕ : {x y z : ℕ} → (x ≤ℕ y) → (y ≤ℕ z) → (x ≤ℕ z)
≤-transℕ {0ℕ} {0ℕ} {0ℕ} * * = *
≤-transℕ {0ℕ} {0ℕ} {succℕ z} * * = *
≤-transℕ {0ℕ} {succℕ y} {succℕ z} * yz = *
≤-transℕ {succℕ x} {succℕ y} {succℕ z} xy yz = ≤-transℕ {x} {y} {z} xy yz

≤-dichotomyℕ : (x y : ℕ) → (x ≤ℕ y) ⊎ (y ≤ℕ x)
≤-dichotomyℕ 0ℕ 0ℕ = inl *
≤-dichotomyℕ 0ℕ (succℕ y) = inl *
≤-dichotomyℕ (succℕ x) 0ℕ = inr *
≤-dichotomyℕ (succℕ x) (succℕ y) = ≤-dichotomyℕ x y

succ-≰-zeroℕ : (x : ℕ) → ¬ (succℕ x ≤ℕ 0ℕ)
succ-≰-zeroℕ 0ℕ ()
succ-≰-zeroℕ (succℕ x) ()

0ℕ-leℕ : (x : ℕ) → 0ℕ ≤ℕ x
0ℕ-leℕ 0ℕ = *
0ℕ-leℕ (succℕ x) = *

≤-addℕ : (m n k : ℕ) → (m ≤ℕ n) ↔ ((m +ℕ k) ≤ℕ (n +ℕ k))
≤-addℕ m n k = (to m n k , from m n k)
  where
  to : (m n k : ℕ) → (m ≤ℕ n) → ((m +ℕ k) ≤ℕ (n +ℕ k))
  to 0ℕ 0ℕ 0ℕ * = *
  to 0ℕ 0ℕ (succℕ k) * = ≤-rflℕ (0ℕ +ℕ succℕ k)
  to 0ℕ (succℕ n) 0ℕ p = *
  to 0ℕ (succℕ n) (succℕ k) * = to 0ℕ (succℕ n) k *
  to (succℕ m) (succℕ n) 0ℕ p = p
  to (succℕ m) (succℕ n) (succℕ k) p = to (succℕ m) (succℕ n) k p

  from : (m n k : ℕ) → ((m +ℕ k) ≤ℕ (n +ℕ k)) → (m ≤ℕ n)
  from 0ℕ 0ℕ 0ℕ * = *
  from 0ℕ 0ℕ (succℕ k) p = *
  from 0ℕ (succℕ n) 0ℕ * = *
  from 0ℕ (succℕ n) (succℕ k) p = *
  from (succℕ m) 0ℕ (succℕ k) p = ex-falso (succ-≰-zeroℕ m (from (succℕ m) 0ℕ k p))
  from (succℕ m) (succℕ n) 0ℕ p = p
  from (succℕ m) (succℕ n) (succℕ k) p = from (succℕ m) (succℕ n) k p

≡-to-≤ℕ : {m n : ℕ} → m ≡ n → m ≤ℕ n
≡-to-≤ℕ {0ℕ} {n} refl = *
≡-to-≤ℕ {succℕ m} {n} refl = ≤-rflℕ m

add-≤ℕ : (m n k : ℕ) → (n ≤ℕ k) → (m +ℕ n) ≤ℕ (m +ℕ k)
add-≤ℕ m n k p = ≤-transℕ {m +ℕ n} {n +ℕ m} {m +ℕ k} (≡-to-≤ℕ (add-commℕ m n)) (≤-transℕ {n +ℕ m} {k +ℕ m} {m +ℕ k} (proj₁ (≤-addℕ n k m) p) (≡-to-≤ℕ (add-commℕ k m)))

≤-succℕ : (x : ℕ) → x ≤ℕ succℕ x
≤-succℕ 0ℕ = *
≤-succℕ (succℕ x) = ≤-succℕ x

≤-mulℕ : (m n k : ℕ) → (m ≤ℕ n) ↔ ((m ·ℕ (k +ℕ 1ℕ)) ≤ℕ (n ·ℕ (k +ℕ 1ℕ)))
≤-mulℕ m n k = (to m n k , from m n k)
  where
  to : (m n k : ℕ) → (m ≤ℕ n) → ((m ·ℕ (k +ℕ 1ℕ)) ≤ℕ (n ·ℕ (k +ℕ 1ℕ)))
  to 0ℕ 0ℕ 0ℕ * = *
  to 0ℕ (succℕ n) 0ℕ * = *
  to (succℕ m) (succℕ n) 0ℕ p = p
  to 0ℕ 0ℕ (succℕ k) * = ≤-rflℕ (0ℕ ·ℕ (succℕ k +ℕ 1ℕ))
  to 0ℕ (succℕ n) (succℕ k) * = ≤-transℕ {0ℕ ·ℕ (succℕ k +ℕ 1ℕ)} {0ℕ} (≡-to-≤ℕ (zero-mulℕ (succℕ k +ℕ 1ℕ))) (0ℕ-leℕ (succℕ n ·ℕ (succℕ k +ℕ 1ℕ)))
  to (succℕ m) (succℕ n) (succℕ k) p = ≤-transℕ {succℕ m ·ℕ (succℕ k +ℕ 1ℕ)} {(succℕ k +ℕ 1ℕ) +ℕ  m ·ℕ (succℕ k +ℕ 1ℕ)} {succℕ n ·ℕ (succℕ k +ℕ 1ℕ)} (≡-to-≤ℕ {succℕ m ·ℕ (succℕ k +ℕ 1ℕ)} {(succℕ k +ℕ 1ℕ) +ℕ (m ·ℕ (succℕ k +ℕ 1ℕ))} (concat (succ-mulℕ m (succℕ k +ℕ 1ℕ)) (add-commℕ (m ·ℕ (succℕ k +ℕ 1ℕ)) (succℕ k +ℕ 1ℕ)))) (≤-transℕ {succℕ k +ℕ 1ℕ +ℕ m ·ℕ (succℕ k +ℕ 1ℕ)} {succℕ k +ℕ 1ℕ +ℕ n ·ℕ (succℕ k +ℕ 1ℕ)} {succℕ n ·ℕ (succℕ k +ℕ 1ℕ)} (add-≤ℕ (succℕ k +ℕ 1ℕ) (m ·ℕ (succℕ k +ℕ 1ℕ)) (n ·ℕ (succℕ k +ℕ 1ℕ)) (to m n (succℕ k) p)) (≡-to-≤ℕ {succℕ k +ℕ 1ℕ +ℕ n ·ℕ (succℕ k +ℕ 1ℕ)} {succℕ n ·ℕ (succℕ k +ℕ 1ℕ)} (inv (concat (succ-mulℕ n (succℕ k +ℕ 1ℕ)) (add-commℕ (n ·ℕ (succℕ k +ℕ 1ℕ)) (succℕ k +ℕ 1ℕ))))))

  from : (m n k : ℕ) → ((m ·ℕ (k +ℕ 1ℕ)) ≤ℕ (n ·ℕ (k +ℕ 1ℕ))) →  (m ≤ℕ n)
  from 0ℕ 0ℕ 0ℕ * = *
  from 0ℕ 0ℕ (succℕ k) x = *
  from 0ℕ (succℕ n) 0ℕ * = *
  from 0ℕ (succℕ n) (succℕ k) x = *
  from (succℕ m) 0ℕ (succℕ k) x = ex-falso (succ-≰-zeroℕ (m +ℕ (succℕ m +ℕ succℕ m ·ℕ k)) (≤-transℕ {succℕ (m +ℕ (succℕ m +ℕ succℕ m ·ℕ k))} {0ℕ +ℕ (0ℕ +ℕ (0ℕ ·ℕ k))} {0ℕ} (≤-transℕ {succℕ (m +ℕ (succℕ m +ℕ succℕ m ·ℕ k))} {succℕ m +ℕ (succℕ m +ℕ succℕ m ·ℕ k)} {0ℕ +ℕ (0ℕ +ℕ (0ℕ ·ℕ k))} (≡-to-≤ℕ (inv (succ-addℕ m (succℕ m +ℕ succℕ m ·ℕ k)))) x) (≡-to-≤ℕ (concat (zero-addℕ (0ℕ +ℕ 0ℕ ·ℕ k)) (concat (zero-addℕ (0ℕ ·ℕ k)) (zero-mulℕ k))))))
  from (succℕ m) (succℕ n) 0ℕ x = x
  from (succℕ m) (succℕ n) (succℕ k) x = from m n (succℕ k) (proj₂ (≤-addℕ (m ·ℕ (succℕ k +ℕ 1ℕ)) (n ·ℕ (succℕ k +ℕ 1ℕ)) (succℕ k +ℕ 1ℕ)) (≤-transℕ {m ·ℕ (succℕ k +ℕ 1ℕ) +ℕ (succℕ k +ℕ 1ℕ)} {succℕ m ·ℕ (succℕ k +ℕ 1ℕ)} {n ·ℕ (succℕ k +ℕ 1ℕ) +ℕ (succℕ k +ℕ 1ℕ)} (≡-to-≤ℕ {m ·ℕ (succℕ k +ℕ 1ℕ) +ℕ (succℕ k +ℕ 1ℕ)} {succℕ m ·ℕ (succℕ k +ℕ 1ℕ)} (inv (succ-mulℕ m (succℕ k +ℕ 1ℕ)))) (≤-transℕ {succℕ m ·ℕ (succℕ k +ℕ 1ℕ)} {succℕ n ·ℕ (succℕ k +ℕ 1ℕ)} {n ·ℕ (succℕ k +ℕ 1ℕ) +ℕ (succℕ k +ℕ 1ℕ)} x (≡-to-≤ℕ {succℕ n ·ℕ (succℕ k +ℕ 1ℕ)} {n ·ℕ (succℕ k +ℕ 1ℕ) +ℕ (succℕ k +ℕ 1ℕ)} (succ-mulℕ n (succℕ k +ℕ 1ℕ))))))

le-minℕ : (m n k : ℕ) → (m ≤ℕ minℕ n k) → (m ≤ℕ n) × (m ≤ℕ k)
le-minℕ 0ℕ 0ℕ 0ℕ * = (* , *)
le-minℕ 0ℕ (succℕ n) 0ℕ * = (* , *)
le-minℕ 0ℕ 0ℕ (succℕ k) * = (* , *)
le-minℕ 0ℕ (succℕ n) (succℕ k) p = (* , *)
le-minℕ (succℕ m) (succℕ n) (succℕ k) p = le-minℕ m n k p

max-leℕ : (m n k : ℕ) → (maxℕ m n ≤ℕ k) → (m ≤ℕ k) × (n ≤ℕ k)
max-leℕ 0ℕ 0ℕ 0ℕ * = (* , *)
max-leℕ 0ℕ 0ℕ (succℕ k) * = (* , *)
max-leℕ 0ℕ (succℕ n) (succℕ k) p = (* , p)
max-leℕ (succℕ m) 0ℕ (succℕ k) p = (p , *)
max-leℕ (succℕ m) (succℕ n) (succℕ k) p = max-leℕ m n k p

-- Ex 6.4
infix 4 _<ℕ_
_<ℕ_ : ℕ → ℕ → Set
0ℕ <ℕ 0ℕ = 𝟘
0ℕ <ℕ succℕ y = 𝟙
succℕ x <ℕ 0ℕ = 𝟘
succℕ x <ℕ succℕ y = x <ℕ y

<-antirflℕ : (m : ℕ) → ¬ (m <ℕ m)
<-antirflℕ 0ℕ ()
<-antirflℕ (succℕ m) x = <-antirflℕ m x

<-antisymℕ : (m n : ℕ) → m <ℕ n → ¬ (n <ℕ m)
<-antisymℕ 0ℕ (succℕ n) * ()
<-antisymℕ (succℕ m) (succℕ n) p = <-antisymℕ m n p

<-transℕ : (m n k : ℕ) → m <ℕ n → n <ℕ k → m <ℕ k
<-transℕ 0ℕ 0ℕ 0ℕ () nk
<-transℕ 0ℕ (succℕ n) 0ℕ * ()
<-transℕ (succℕ m) 0ℕ 0ℕ () nk
<-transℕ (succℕ m) (succℕ n) 0ℕ mn ()
<-transℕ 0ℕ 0ℕ (succℕ k) () *
<-transℕ (succℕ m) 0ℕ (succℕ k) () *
<-transℕ 0ℕ (succℕ n) (succℕ k) * nk = *
<-transℕ (succℕ m) (succℕ n) (succℕ k) mn nk = <-transℕ m n k mn nk

<-succℕ : (m : ℕ) → m <ℕ succℕ m
<-succℕ 0ℕ = *
<-succℕ (succℕ m) = <-succℕ m

<-to-succ-≤ℕ : (m n : ℕ) → m <ℕ n → succℕ m ≤ℕ n
<-to-succ-≤ℕ 0ℕ (succℕ 0ℕ) * = *
<-to-succ-≤ℕ 0ℕ (succℕ (succℕ n)) * = *
<-to-succ-≤ℕ (succℕ m) (succℕ n) p = <-to-succ-≤ℕ m n p

succ-≤-to-<ℕ : (m n : ℕ) → succℕ m ≤ℕ n → m <ℕ n
succ-≤-to-<ℕ 0ℕ (succℕ n) p = *
succ-≤-to-<ℕ (succℕ m) (succℕ n) p = succ-≤-to-<ℕ m n p

<-to-≱ : (m n : ℕ) → m <ℕ n → ¬ (n ≤ℕ m)
<-to-≱ 0ℕ (succℕ n) * ()
<-to-≱ (succℕ m) (succℕ n) p q = <-to-≱ m n p q

<-zeroℕ : (m : ℕ) → ¬ (m <ℕ 0ℕ)
<-zeroℕ 0ℕ ()
<-zeroℕ (succℕ m) ()

<-succ-to-<-or-≡ℕ : (m k : ℕ) → m <ℕ succℕ k → (m <ℕ k) ⊎ (m ≡ k)
<-succ-to-<-or-≡ℕ 0ℕ 0ℕ * = inr refl
<-succ-to-<-or-≡ℕ 0ℕ (succℕ k) * = inl *
<-succ-to-<-or-≡ℕ (succℕ m) 0ℕ p = ex-falso (<-zeroℕ m p)
<-succ-to-<-or-≡ℕ (succℕ m) (succℕ k) p with <-succ-to-<-or-≡ℕ m k p
... | inl q = inl q
... | inr q = inr (ap succℕ q)

-- Ex 6.5
distℕ : ℕ → ℕ → ℕ
distℕ m 0ℕ = m
distℕ 0ℕ (succℕ n) = succℕ n
distℕ (succℕ m) (succℕ n) = distℕ m n

≡-to-dist0ℕ : (m n : ℕ) → m ≡ n → distℕ m n ≡ 0ℕ
≡-to-dist0ℕ 0ℕ 0ℕ refl = refl
≡-to-dist0ℕ 0ℕ (succℕ n) ()
≡-to-dist0ℕ (succℕ m) 0ℕ ()
≡-to-dist0ℕ (succℕ m) (succℕ n) refl = ≡-to-dist0ℕ m n refl

dist0-to-≡ℕ : (m n : ℕ) → distℕ m n ≡ 0ℕ → m ≡ n
dist0-to-≡ℕ 0ℕ 0ℕ refl = refl
dist0-to-≡ℕ (succℕ m) (succℕ n) d = ap succℕ (dist0-to-≡ℕ m n d)

dist-symmℕ : (m n : ℕ) → distℕ m n ≡ distℕ n m
dist-symmℕ 0ℕ 0ℕ = refl
dist-symmℕ 0ℕ (succℕ n) = refl
dist-symmℕ (succℕ m) 0ℕ = refl
dist-symmℕ (succℕ m) (succℕ n) = dist-symmℕ m n

≤-add-distℕ : (m n : ℕ) → m ≤ℕ n +ℕ distℕ m n
≤-add-distℕ 0ℕ 0ℕ = *
≤-add-distℕ 0ℕ (succℕ n) = *
≤-add-distℕ (succℕ m) 0ℕ = ≡-to-≤ℕ {succℕ m} {0ℕ +ℕ succℕ m} (inv (zero-addℕ (succℕ m)))
≤-add-distℕ (succℕ m) (succℕ n) = ≤-transℕ {succℕ m} {distℕ (succℕ m) (succℕ n) +ℕ succℕ n} {succℕ n +ℕ distℕ (succℕ m) (succℕ n)} (≤-transℕ {m} {n +ℕ distℕ (m) (n)} {distℕ (m) (n) +ℕ n} (≤-add-distℕ m n) (≡-to-≤ℕ {n +ℕ distℕ m n} {distℕ m n +ℕ n} (add-commℕ n (distℕ m n)))) (≡-to-≤ℕ {distℕ (succℕ m) (succℕ n) +ℕ succℕ n} {succℕ n +ℕ distℕ (succℕ m) (succℕ n)} (add-commℕ (distℕ (succℕ m) (succℕ n)) (succℕ n)))

dist-zero-rightℕ : (m : ℕ) → distℕ m 0ℕ ≡ m
dist-zero-rightℕ 0ℕ = refl
dist-zero-rightℕ (succℕ m) = refl

add-distℕ : (x y : ℕ) → (x ≤ℕ y) → x +ℕ distℕ x y ≡ y
add-distℕ 0ℕ 0ℕ * = refl
add-distℕ 0ℕ (succℕ y) * = zero-addℕ (succℕ y)
add-distℕ (succℕ x) (succℕ y) p = concat (succ-addℕ x (distℕ x y)) (ap succℕ (add-distℕ x y p))

dist-triangleℕ : (m n k : ℕ) → distℕ m n ≤ℕ distℕ m k +ℕ distℕ n k
dist-triangleℕ 0ℕ 0ℕ 0ℕ = *
dist-triangleℕ 0ℕ 0ℕ (succℕ k) = *
dist-triangleℕ 0ℕ (succℕ n) 0ℕ = ≡-to-≤ℕ {succℕ n} {0ℕ +ℕ succℕ n} (inv (zero-addℕ (succℕ n)))
dist-triangleℕ 0ℕ (succℕ n) (succℕ k) = ≤-add-distℕ (succℕ n) (succℕ k)
dist-triangleℕ (succℕ m) 0ℕ 0ℕ = ≤-rflℕ (succℕ m)
dist-triangleℕ (succℕ m) 0ℕ (succℕ k) = ≤-transℕ {distℕ (succℕ m) 0ℕ} {distℕ 0ℕ (succℕ k) +ℕ distℕ (succℕ m) (succℕ k)} {distℕ (succℕ m) (succℕ k) +ℕ distℕ 0ℕ (succℕ k)} (≤-add-distℕ (succℕ m) (succℕ k)) (≡-to-≤ℕ {distℕ 0ℕ (succℕ k) +ℕ distℕ (succℕ m) (succℕ k)} {distℕ (succℕ m) (succℕ k) +ℕ distℕ 0ℕ (succℕ k)} (add-commℕ (distℕ 0ℕ (succℕ k)) (distℕ (succℕ m) (succℕ k))))
dist-triangleℕ (succℕ m) (succℕ n) 0ℕ = ≤-transℕ {distℕ m n} {distℕ m 0ℕ +ℕ distℕ n 0ℕ} {distℕ (succℕ m) 0ℕ +ℕ distℕ (succℕ n) 0ℕ} (dist-triangleℕ m n 0ℕ) (≤-transℕ {distℕ m 0ℕ +ℕ distℕ n 0ℕ} {m +ℕ n} {succℕ m +ℕ succℕ n} (≡-to-≤ℕ (concat (ap (λ x → x +ℕ distℕ n 0ℕ) (dist-zero-rightℕ m)) (ap (λ x → m +ℕ x) (dist-zero-rightℕ n)))) (≤-transℕ {m +ℕ n} {m +ℕ succℕ n} {succℕ m +ℕ succℕ n} (≤-succℕ (m +ℕ n)) (proj₁ (≤-addℕ m (succℕ m) (succℕ n)) (≤-succℕ m))))
dist-triangleℕ (succℕ m) (succℕ n) (succℕ k) = dist-triangleℕ m n k

≡-add-to-≤ℕ : (m n k : ℕ) → m ≡ n +ℕ k → n ≤ℕ m
≡-add-to-≤ℕ 0ℕ 0ℕ 0ℕ refl = *
≡-add-to-≤ℕ (succℕ m) 0ℕ (succℕ k) p = *
≡-add-to-≤ℕ (succℕ m) (succℕ n) 0ℕ refl = ≤-rflℕ m
≡-add-to-≤ℕ (succℕ m) (succℕ n) (succℕ k) refl = ≤-transℕ {n} {succℕ n} {succℕ n +ℕ k} (≤-succℕ n) (≤-transℕ {succℕ n} {succℕ n +ℕ 0ℕ} {succℕ n +ℕ k} (≡-to-≤ℕ {succℕ n} {succℕ n +ℕ 0ℕ} refl) (add-≤ℕ (succℕ n) 0ℕ k (0ℕ-leℕ k)))

double-succ-not-leℕ : (m : ℕ) → ¬ (succℕ (succℕ m) ≤ℕ m)
double-succ-not-leℕ 0ℕ ()
double-succ-not-leℕ (succℕ m) p = double-succ-not-leℕ m p

dist-tri-eqℕ : (m n k : ℕ) → (distℕ m n ≡ distℕ m k +ℕ distℕ n k) ↔ (((m ≤ℕ k) × (k ≤ℕ n)) ⊎ ((n ≤ℕ k) × (k ≤ℕ m)))
dist-tri-eqℕ m n k = (to m n k , from m n k)
  where
  to : (m n k : ℕ) → (distℕ m n ≡ distℕ m k +ℕ distℕ n k) → ((m ≤ℕ k) × (k ≤ℕ n)) ⊎ ((n ≤ℕ k) × (k ≤ℕ m))
  to 0ℕ 0ℕ 0ℕ refl = inl (* , *)
  to 0ℕ (succℕ n) 0ℕ p = inl (* , *)
  to 0ℕ (succℕ n) (succℕ k) p = inl (* , ≡-add-to-≤ℕ (succℕ n) (succℕ k) (distℕ n k) p)
  to (succℕ m) 0ℕ 0ℕ p = inr (* , *)
  to (succℕ m) 0ℕ (succℕ k) p = inr (* , ≡-add-to-≤ℕ (succℕ m) (succℕ k) (distℕ m k) (concat p (add-commℕ (distℕ m k) (succℕ k))))
  to (succℕ m) (succℕ n) 0ℕ p = ex-falso (double-succ-not-leℕ (m +ℕ n)
    (tr (λ x → x ≤ℕ m +ℕ n) (ap succℕ (succ-addℕ m n))
    (tr (λ x → x ≤ℕ m +ℕ n) p
    (tr (λ x → distℕ m n ≤ℕ x)
      (concat (ap (λ y → y +ℕ distℕ n 0ℕ) (dist-zero-rightℕ m))
              (ap (λ y → m +ℕ y) (dist-zero-rightℕ n)))
      (dist-triangleℕ m n 0ℕ)))))
  to (succℕ m) (succℕ n) (succℕ k) p = to m n k p

  from : (m n k : ℕ) → ((m ≤ℕ k) × (k ≤ℕ n)) ⊎ ((n ≤ℕ k) × (k ≤ℕ m)) → (distℕ m n ≡ distℕ m k +ℕ distℕ n k)
  from 0ℕ 0ℕ 0ℕ (inl (* , *)) = refl
  from 0ℕ 0ℕ 0ℕ (inr (* , *)) = refl
  from 0ℕ 0ℕ (succℕ k) (inl (* , ()))
  from 0ℕ 0ℕ (succℕ k) (inr (* , ()))
  from 0ℕ (succℕ n) 0ℕ (inl (* , *)) = inv (zero-addℕ (succℕ n))
  from 0ℕ (succℕ n) 0ℕ (inr (() , y))
  from 0ℕ (succℕ n) (succℕ k) (inl (* , y)) = concat (inv (add-distℕ (succℕ k) (succℕ n) y)) (ap (λ x → succℕ k +ℕ x) (dist-symmℕ k n))
  from 0ℕ (succℕ n) (succℕ k) (inr (x , ()))
  from (succℕ m) 0ℕ 0ℕ (inl (() , y))
  from (succℕ m) 0ℕ 0ℕ (inr (* , *)) = refl
  from (succℕ m) 0ℕ (succℕ k) (inl (x , ()))
  from (succℕ m) 0ℕ (succℕ k) (inr (* , y)) = concat (inv (add-distℕ (succℕ k) (succℕ m) y)) (concat (ap (λ x → succℕ k +ℕ x) (dist-symmℕ k m)) (add-commℕ (succℕ k) (distℕ m k)))
  from (succℕ m) (succℕ n) 0ℕ (inl (() , y))
  from (succℕ m) (succℕ n) 0ℕ (inr (() , y))
  from (succℕ m) (succℕ n) (succℕ k) (inl (x , y)) = from m n k (inl (x , y))
  from (succℕ m) (succℕ n) (succℕ k) (inr (x , y)) = from m n k (inr (x , y))

dist-trans-invarℕ : (m n a : ℕ) → distℕ (m +ℕ a) (n +ℕ a) ≡ distℕ m n
dist-trans-invarℕ m n 0ℕ = refl
dist-trans-invarℕ m n (succℕ a) = dist-trans-invarℕ m n a

≤-mul-leftℕ : (m n k : ℕ) → m ≤ℕ n → k ·ℕ m ≤ℕ k ·ℕ n
≤-mul-leftℕ m n 0ℕ _ = ≡-to-≤ℕ (concat (zero-mulℕ m) (inv (zero-mulℕ n)))
≤-mul-leftℕ m n (succℕ k) m≤n =
  tr (λ x → x ≤ℕ succℕ k ·ℕ n) (mul-commℕ m (succℕ k))
  (tr (λ x → m ·ℕ succℕ k ≤ℕ x) (mul-commℕ n (succℕ k))
  (proj₁ (≤-mulℕ m n k) m≤n))

dist-linearℕ : (m n k : ℕ) → distℕ (k ·ℕ m) (k ·ℕ n) ≡ k ·ℕ distℕ m n
dist-linearℕ m n 0ℕ = concat (ap (λ x → distℕ x (0ℕ ·ℕ n)) (zero-mulℕ m)) (concat (ap (λ x → distℕ 0ℕ x) (zero-mulℕ n)) (inv (zero-mulℕ (distℕ m n))))
dist-linearℕ m n (succℕ k) with ≤-dichotomyℕ m n
... | inl m≤n = proj₂ (add-injℕ (distℕ (succℕ k ·ℕ m) (succℕ k ·ℕ n)) (succℕ k ·ℕ distℕ m n) (succℕ k ·ℕ m))
  (concat (add-commℕ (distℕ (succℕ k ·ℕ m) (succℕ k ·ℕ n)) (succℕ k ·ℕ m))
  (concat (add-distℕ (succℕ k ·ℕ m) (succℕ k ·ℕ n) (≤-mul-leftℕ m n (succℕ k) m≤n))
  (concat (ap (succℕ k ·ℕ_) (inv (add-distℕ m n m≤n)))
  (concat (left-distribℕ (succℕ k) m (distℕ m n))
  (add-commℕ (succℕ k ·ℕ m) (succℕ k ·ℕ distℕ m n))))))
... | inr n≤m = concat (dist-symmℕ (succℕ k ·ℕ m) (succℕ k ·ℕ n))
  (concat (proj₂ (add-injℕ (distℕ (succℕ k ·ℕ n) (succℕ k ·ℕ m)) (succℕ k ·ℕ distℕ n m) (succℕ k ·ℕ n))
    (concat (add-commℕ (distℕ (succℕ k ·ℕ n) (succℕ k ·ℕ m)) (succℕ k ·ℕ n))
    (concat (add-distℕ (succℕ k ·ℕ n) (succℕ k ·ℕ m) (≤-mul-leftℕ n m (succℕ k) n≤m))
    (concat (ap (succℕ k ·ℕ_) (inv (add-distℕ n m n≤m)))
    (concat (left-distribℕ (succℕ k) n (distℕ n m))
    (add-commℕ (succℕ k ·ℕ n) (succℕ k ·ℕ distℕ n m)))))))
  (ap (succℕ k ·ℕ_) (dist-symmℕ n m)))

absℤ : ℤ → ℕ
absℤ 0ℤ = 0ℕ
absℤ (in-neg x) = succℕ x
absℤ (in-pos x) = succℕ x


abs-zeroℤ : absℤ 0ℤ ≡ 0ℕ
abs-zeroℤ = refl

abs-eq-zeroℤ : (x : ℤ) → absℤ x ≡ 0ℕ → x ≡ 0ℤ
abs-eq-zeroℤ 0ℤ refl = refl
abs-eq-zeroℤ (in-neg x) ()
abs-eq-zeroℤ (in-pos x) ()

abs-predℤ : (x : ℤ) → absℤ (predℤ x) ≤ℕ succℕ (absℤ x)
abs-predℤ 0ℤ = *
abs-predℤ (in-neg x) = ≤-rflℕ x
abs-predℤ (in-pos 0ℕ) = *
abs-predℤ (in-pos (succℕ x)) = ≤-transℕ {x} {succℕ x} {succℕ (succℕ x)} (≤-succℕ x) (≤-succℕ (succℕ x))

abs-succℤ : (x : ℤ) → absℤ (succℤ x) ≤ℕ succℕ (absℤ x)
abs-succℤ 0ℤ = *
abs-succℤ (in-neg 0ℕ) = *
abs-succℤ (in-neg (succℕ x)) = ≤-transℕ {x} {succℕ x} {succℕ (succℕ x)} (≤-succℕ x) (≤-succℕ (succℕ x))
abs-succℤ (in-pos x) = ≤-rflℕ x

abs-tri-ineqℤ : (x y : ℤ) → absℤ (x +ℤ y) ≤ℕ absℤ x +ℕ absℤ y
abs-tri-ineqℤ x 0ℤ = ≡-to-≤ℕ {absℤ (x +ℤ 0ℤ)} {absℤ x +ℕ absℤ 0ℤ} refl
abs-tri-ineqℤ x (in-neg 0ℕ) = abs-predℤ x
abs-tri-ineqℤ x (in-neg (succℕ y)) = ≤-transℕ {absℤ (predℤ (x +ℤ in-neg y))} {succℕ (absℤ (x +ℤ in-neg y))} {absℤ x +ℕ succℕ (succℕ y)} (abs-predℤ (x +ℤ in-neg y)) (abs-tri-ineqℤ x (in-neg y))
abs-tri-ineqℤ x (in-pos 0ℕ) = abs-succℤ x
abs-tri-ineqℤ x (in-pos (succℕ y)) = ≤-transℕ {absℤ (succℤ (x +ℤ in-pos y))} {succℕ (absℤ (x +ℤ in-pos y))} {absℤ x +ℕ succℕ (succℕ y)} (abs-succℤ (x +ℤ in-pos y)) (abs-tri-ineqℤ x (in-pos y))
