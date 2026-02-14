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

zero-ne-succℕ = 0-ne-succℕ

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
  from 0ℕ 0ℕ k refl = refl
  from 0ℕ (succℕ n) k p = ex-falso (0-ne-succℕ (n +ℕ succℕ n ·ℕ k) (concat (inv (zero-mulℕ k)) (concat (inv (zero-addℕ (0ℕ ·ℕ k))) (concat p (succ-addℕ n (succℕ n ·ℕ k))))))
  from (succℕ m) 0ℕ k p = ex-falso (0-ne-succℕ (m +ℕ succℕ m ·ℕ k) (concat (inv (zero-mulℕ k)) (concat (inv (zero-addℕ (0ℕ ·ℕ k))) (concat (inv p) (succ-addℕ m (succℕ m ·ℕ k))))))
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
mul-ne-selfℕ (succℕ m) 0ℕ p = ex-falso (0-ne-succℕ (succℕ m) (proj₂ (add-injℕ 0ℕ (succℕ (succℕ m)) m) (concat (zero-addℕ m) (proj₂ (succ-injℕ m (succℕ (succℕ m) +ℕ m)) (proj₂ (succ-injℕ (succℕ m) (succℕ (succℕ (succℕ m) +ℕ m))) (concat p (concat (ap (λ x → (succℕ m +ℕ 1ℕ) ·ℕ x) (zero-addℕ 2ℕ)) (inv (concat (inv (ap succℕ (add-succℕ (succℕ (succℕ m)) m))) (add-succℕ (succℕ (succℕ m)) (succℕ m))))))) ))))
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

infix 4 _≤ℕ_
_≤ℕ_ : ℕ → ℕ → Set
0ℕ ≤ℕ 0ℕ = 𝟙
0ℕ ≤ℕ succℕ y = 𝟙
succℕ x ≤ℕ 0ℕ = 𝟘
succℕ x ≤ℕ succℕ y = x ≤ℕ y

≤-rflℕ : (x : ℕ) → (x ≤ℕ x)
≤-rflℕ 0ℕ = *
≤-rflℕ (succℕ x) = ≤-rflℕ x

≤-antisymmℕ : (x y : ℕ) → (x ≤ℕ y) → (y ≤ℕ x) → (x ≡ y)
≤-antisymmℕ 0ℕ 0ℕ * * = refl
≤-antisymmℕ (succℕ x) (succℕ y) x≤y y≤x = ap succℕ (≤-antisymmℕ x y x≤y y≤x)

≤-transℕ : (x y z : ℕ) → (x ≤ℕ y) → (y ≤ℕ z) → (x ≤ℕ z)
≤-transℕ 0ℕ 0ℕ 0ℕ * * = *
≤-transℕ 0ℕ 0ℕ (succℕ z) * * = *
≤-transℕ 0ℕ (succℕ y) (succℕ z) * yz = *
≤-transℕ (succℕ x) (succℕ y) (succℕ z) xy yz = ≤-transℕ x y z xy yz

≤-dichotomyℕ : (x y : ℕ) → (x ≤ℕ y) ⊎ (y ≤ℕ x)
≤-dichotomyℕ 0ℕ 0ℕ = inl *
≤-dichotomyℕ 0ℕ (succℕ y) = inl *
≤-dichotomyℕ (succℕ x) 0ℕ = inr *
≤-dichotomyℕ (succℕ x) (succℕ y) = ≤-dichotomyℕ x y

succ-nle-zeroℕ : (x : ℕ) → ¬ (succℕ x ≤ℕ 0ℕ)
succ-nle-zeroℕ 0ℕ ()
succ-nle-zeroℕ (succℕ x) ()

succ-≰-zeroℕ = succ-nle-zeroℕ 

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

≤-mulℕ : (m n k : ℕ) → (m ≤ℕ n) ↔ ((m ·ℕ (k +ℕ 1ℕ)) ≤ℕ (n ·ℕ (k +ℕ 1ℕ)))
≤-mulℕ m n k = (to m n k , from m n k)
  where
  to : (m n k : ℕ) → (m ≤ℕ n) → ((m ·ℕ (k +ℕ 1ℕ)) ≤ℕ (n ·ℕ (k +ℕ 1ℕ)))
  to 0ℕ 0ℕ 0ℕ * = *
  to 0ℕ (succℕ n) 0ℕ * = *
  to (succℕ m) (succℕ n) 0ℕ p = p
  to 0ℕ 0ℕ (succℕ k) * = ≤-rflℕ (0ℕ ·ℕ (succℕ k +ℕ 1ℕ))
  to 0ℕ (succℕ n) (succℕ k) * = {!!}
  to (succℕ m) (succℕ n) (succℕ k) p = {!!}

  from : (m n k : ℕ) → ((m ·ℕ (k +ℕ 1ℕ)) ≤ℕ (n ·ℕ (k +ℕ 1ℕ))) →  (m ≤ℕ n)
  from 0ℕ 0ℕ 0ℕ * = *
  from 0ℕ 0ℕ (succℕ k) x = *
  from 0ℕ (succℕ n) 0ℕ * = *
  from 0ℕ (succℕ n) (succℕ k) x = *
  from (succℕ m) 0ℕ (succℕ k) x = ex-falso (succ-nle-zeroℕ (m +ℕ (succℕ m +ℕ succℕ m ·ℕ k)) (from (succℕ m) 0ℕ k {!!}))
  from (succℕ m) (succℕ n) 0ℕ x = x
  from (succℕ m) (succℕ n) (succℕ k) x = from m n (succℕ k) {!!}
