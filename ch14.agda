{-# OPTIONS --without-K #-}

open import ch13 public

is-prop-trunc : {A P : Set} → is-prop P → (f : A → P) → Set₁
is-prop-trunc {A} {P} Pprop f = (Q : Set) → is-prop Q → is-equiv (precomp f Q)

prop-truncs-to-equiv : {A P P' : Set} → (Pprop : is-prop P) → (Pprop' : is-prop P') → (f : A → P) → (f' : A → P') → is-prop-trunc Pprop f → is-prop-trunc Pprop' f' → P ≃ P' 
prop-truncs-to-equiv {A} {P} {P'} Pprop Pprop' f f' fproptrunc f'proptrunc = iff-to-≃ Pprop Pprop' ((g f') , g' f)
    where
        g = proj₁ (proj₁ (fproptrunc P' Pprop'))
        g' = proj₁ (proj₁ (f'proptrunc P Pprop))

precomp-equiv-to-equiv : {P P' : Set} → (e : P ≃ P') → (X : Set) → is-equiv (precomp (proj₁ e) X)
precomp-equiv-to-equiv (e , eq) X = precomp-Π-is-equiv-to-precomp-is-equiv e (is-equiv-to-precomp-Π-is-equiv e eq) X

equiv-to-prop-trunc-to-prop-trunc : {A P P' : Set} → (Pprop : is-prop P) → (Pprop' : is-prop P') → (f : A → P) → (f' : A → P') → P ≃ P' → is-prop-trunc Pprop f → is-prop-trunc Pprop' f'
equiv-to-prop-trunc-to-prop-trunc Pprop Pprop' f f' (e , eq) fproptrunc Q Qprop = 
    htpy-of-equiv-is-equiv 
        (λ z z₁ → z (e (f z₁))) 
        (λ z z₁ → z (f' z₁)) 
        (λ h → eq-htpy _ _ λ a → ap h (proj₁ (Pprop' (e (f a)) (f' a)))) 
        (equiv-comp (precomp e Q) (precomp f Q) (precomp-equiv-to-equiv ((e , eq)) Q) (fproptrunc Q Qprop))

postulate
    ∥_∥ : Set → Set
    η : {A : Set} → A → ∥ A ∥
    α : {A : Set} → (x y : ∥ A ∥) → x ≡ y

    ind-prop-trunc : {A : Set} → {Q : ∥ A ∥ → Set} →
      (f : (a : A) → Q (η a)) →
      (coh : (x y : ∥ A ∥) → (u : Q x) → (v : Q y) → tr Q (α x y) u ≡ v) →
      (t : ∥ A ∥) → Q t

    comp-prop-trunc : {A : Set} → {Q : ∥ A ∥ → Set} →
      (f : (a : A) → Q (η a)) →
      (coh : (x y : ∥ A ∥) → (u : Q x) → (v : Q y) → tr Q (α x y) u ≡ v) →
      (a : A) → ind-prop-trunc f coh (η a) ≡ f a

is-prop'-to-is-prop : {A : Set} → is-prop' A → is-prop A
is-prop'-to-is-prop {A} propA' = emb-𝟙-to-is-prop (inhab-contr-to-emb-𝟙 (is-prop'-to-inhab-contr propA'))

prop-trunc-is-prop : {A : Set} → is-prop ∥ A ∥
prop-trunc-is-prop = is-prop'-to-is-prop α