module ch7 where

open import ch6 public

infix 4 _∣_
_∣_ : (n : ℕ) → (m : ℕ) → Set lzero
n ∣ m = Σ ℕ (λ k → (k ·ℕ n ≡ m))

one-divℕ : (x : ℕ) → 1ℕ ∣ x
one-divℕ x = (x , refl)

div-zeroℕ : (x : ℕ) → x ∣ 0ℕ
div-zeroℕ x = (0ℕ , zero-mulℕ x)

div-sumℕ : (x y d : ℕ) → (d ∣ x) → (d ∣ y) → (d ∣ (x +ℕ y))
div-sumℕ x y d (kx , refl) (ky , refl) = ((kx +ℕ ky) , right-distribℕ kx ky d)

is-reflexive : {A : Set} → (A → A → Set) → Set
is-reflexive {A} R = (x : A) → R x x

is-symmetric : {A : Set} → (A → A → Set) → Set
is-symmetric {A} R = (x y : A) → R x y → R y x

is-transitive : {A : Set} → (A → A → Set) → Set
is-transitive {A} R = (x y z : A) → R x y → R y z → R x z

infix 4 _≡ℕ_mod_
_≡ℕ_mod_ : ℕ → ℕ → ℕ → Set lzero
x ≡ℕ y mod k = k ∣ distℕ x y

k-is-zero-mod-kℕ : (k : ℕ) → k ≡ℕ 0ℕ mod k
k-is-zero-mod-kℕ k = (1ℕ , one-mulℕ k)

mod-is-rflℕ : (k : ℕ) → is-reflexive (λ x y → x ≡ℕ y mod k)
mod-is-rflℕ k 0ℕ = (0ℕ , zero-mulℕ k)
mod-is-rflℕ k (succℕ x) =
  (0ℕ , concat (zero-mulℕ k) (inv (≡-to-dist0ℕ (succℕ x) (succℕ x) refl)))

mod-is-symmℕ : (k : ℕ) → is-symmetric (λ x y → x ≡ℕ y mod k)
mod-is-symmℕ k 0ℕ 0ℕ p = (0ℕ , zero-mulℕ k)
mod-is-symmℕ k 0ℕ (succℕ y) (n , p) = (n , concat p (dist-symmℕ 0ℕ (succℕ y)))
mod-is-symmℕ k (succℕ x) 0ℕ (n , p) = (n , concat p (dist-symmℕ 0ℕ (succℕ x)))
mod-is-symmℕ k (succℕ x) (succℕ y) (n , p) = (n , concat p (dist-symmℕ x y))

mod-is-transℕ : (k : ℕ) → is-transitive (λ x y → x ≡ℕ y mod k)
mod-is-transℕ k x y z (kxy , pxy) (kyz , pyz) =
  ((kxy +ℕ kyz) ,
   concat (right-distribℕ kxy kyz k)
          (concat (ap (λ n → n +ℕ kyz ·ℕ k) pxy)
                  (concat (ap (λ n → distℕ x y +ℕ n) pyz)
                          (by-cases-on-xy-yz x y z))))
  where
    by-cases-on-xy-yz : (x y z : ℕ) →
                        distℕ x y +ℕ distℕ y z ≡ distℕ x z
    by-cases-on-xy-yz x y z with ≤-dichotomyℕ x y | ≤-dichotomyℕ y z

    ... | inl x≤y | inl y≤z =
      inv (concat (dist-symmℕ x z)
                  (inv (concat (concat (add-commℕ (distℕ x y) (distℕ y z))
                                       (ap (λ n → n +ℕ distℕ x y)
                                           (dist-symmℕ y z)))
                               (inv (proj₂ (dist-tri-eqℕ z x y)
                                           (inr ((x≤y , y≤z))))))))

    ... | inl x≤y | inr z≤y = {!!}

    ... | inr y≤x | inl y≤z = {!!}

    ... | inr y≤x | inr z≤y = {!!}
