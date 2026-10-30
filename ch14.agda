{-# OPTIONS --without-K #-}

open import ch13 public

-- 14.1 The universal property of propositional truncations

-- Definition 14.1.1
is-prop-trunc : {A P : Set} → is-prop P → (f : A → P) → Set₁
is-prop-trunc {A} {P} Pprop f = (Q : Set) → (Qprop : is-prop Q) → is-equiv (precomp f Q)

-- Remark 14.1.2: every map into a proposition extends uniquely along a propositional truncation
is-prop-trunc-to-unique-ext : {A P : Set} → (Pprop : is-prop P) → (f : A → P) → is-prop-trunc Pprop f
  → (Q : Set) → is-prop Q → (g : A → Q) → is-contr (fib (precomp f Q) g)
is-prop-trunc-to-unique-ext {A} {P} Pprop f fproptrunc Q Qprop g = equiv-to-contr-map (precomp f Q) (fproptrunc Q Qprop) g

-- the extension itself, forgetting uniqueness
is-prop-trunc-to-ext : {A P : Set} → (Pprop : is-prop P) → (f : A → P) → is-prop-trunc Pprop f
  → (Q : Set) → is-prop Q → (A → Q) → (P → Q)
is-prop-trunc-to-ext Pprop f fproptrunc Q Qprop = proj₁ (proj₁ (fproptrunc Q Qprop))

-- Remark 14.1.3
→-prop : (X Q : Set) → is-prop Q → is-prop (X → Q)
→-prop X Q Qprop = fam-trunc-to-Π-trunc λ x → Qprop

-- for a single proposition Q, extending maps into Q along f makes precomposition with f an equivalence
ext-to-precomp-is-equiv : {A P : Set} → (f : A → P) → (Q : Set) → is-prop Q
  → ((A → Q) → (P → Q)) → is-equiv (precomp f Q)
ext-to-precomp-is-equiv {A} {P} f Q Qprop ext = proj₂ (iff-to-≃ (→-prop P Q Qprop) (→-prop A Q Qprop) (precomp f Q , ext))

-- to show f is a propositional truncation it suffices to extend maps into propositions along f
ext-to-is-prop-trunc : {A P : Set} → (Pprop : is-prop P) → (f : A → P)
  → ((Q : Set) → is-prop Q → (A → Q) → (P → Q)) → is-prop-trunc Pprop f
ext-to-is-prop-trunc Pprop f ext Q Qprop = ext-to-precomp-is-equiv f Q Qprop (ext Q Qprop)

-- Proposition 14.1.4
-- (i) and (ii) imply (iii)
prop-truncs-to-equiv : {A P P' : Set} → (Pprop : is-prop P) → (Pprop' : is-prop P') → (f : A → P) → (f' : A → P') → is-prop-trunc Pprop f → is-prop-trunc Pprop' f' → P ≃ P'
prop-truncs-to-equiv {A} {P} {P'} Pprop Pprop' f f' fproptrunc f'proptrunc =
  iff-to-≃ Pprop Pprop' (is-prop-trunc-to-ext Pprop f fproptrunc P' Pprop' f' , is-prop-trunc-to-ext Pprop' f' f'proptrunc P Pprop f)

-- the equivalence in (iii) is unique
≃-prop : {P P' : Set} → is-prop P → is-prop P' → is-prop (P ≃ P')
≃-prop {P} {P'} Pprop Pprop' = fam-trunc-to-Σ-trunc (→-prop P P' Pprop') λ g → equiv-is-prop g

precomp-equiv-to-equiv : {P P' : Set} → (e : P ≃ P') → (X : Set) → is-equiv (precomp (proj₁ e) X)
precomp-equiv-to-equiv (e , eq) X = precomp-Π-is-equiv-to-precomp-is-equiv e (is-equiv-to-precomp-Π-is-equiv e eq) X

-- (iii) and (i) imply (ii); (iii) and (ii) imply (i) by swapping roles and using inv-≃
equiv-to-prop-trunc-to-prop-trunc : {A P P' : Set} → (Pprop : is-prop P) → (Pprop' : is-prop P') → (f : A → P) → (f' : A → P') → P ≃ P' → is-prop-trunc Pprop f → is-prop-trunc Pprop' f'
equiv-to-prop-trunc-to-prop-trunc Pprop Pprop' f f' (e , eq) fproptrunc Q Qprop =
    htpy-of-equiv-is-equiv
        (λ z z₁ → z (e (f z₁)))
        (λ z z₁ → z (f' z₁))
        (λ h → eq-htpy _ _ λ a → ap h (proj₁ (Pprop' (e (f a)) (f' a))))
        (equiv-comp (precomp e Q) (precomp f Q) (precomp-equiv-to-equiv ((e , eq)) Q) (fproptrunc Q Qprop))

-- Remark 14.1.5: A → ¬¬A has the universal property, but only against doubly negated propositions
precomp-dni-¬¬-is-equiv : (A Q : Set) → is-equiv (precomp (dni {A}) (¬¬ Q))
precomp-dni-¬¬-is-equiv A Q = ext-to-precomp-is-equiv (λ a na → na a) (¬¬ Q) (¬-prop (¬ Q)) λ z z₁ z₂ → z₁ (λ z₃ → z z₃ z₂)

-- 14.2 Propositional truncations as higher inductive types

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

-- Lemma 14.2.1
prop-trunc-is-prop : (A : Set) → is-prop ∥ A ∥
prop-trunc-is-prop A = is-prop'-to-is-prop α

-- Remark 14.2.3: the coherence hypothesis of ind-prop-trunc holds exactly for families of propositions
prop-trunc-coh-to-prop-fam : {A : Set} → (Q : ∥ A ∥ → Set)
  → ((x y : ∥ A ∥) → (u : Q x) → (v : Q y) → tr Q (α x y) u ≡ v) → ((t : ∥ A ∥) → is-prop (Q t))
prop-trunc-coh-to-prop-fam {A} Q coh t = is-prop'-to-is-prop λ qt₁ qt₂ → concat (inv (coh t t qt₁ qt₁)) (coh t t qt₁ qt₂)

prop-fam-to-prop-trunc-coh : {A : Set} → (Q : ∥ A ∥ → Set)
  → ((t : ∥ A ∥) → is-prop (Q t)) → ((x y : ∥ A ∥) → (u : Q x) → (v : Q y) → tr Q (α x y) u ≡ v)
prop-fam-to-prop-trunc-coh {A} Q Qprop x y u v = proj₁ (Qprop y (tr Q (α x y) u) v)

prop-trunc-coh-iff-prop-fam : {A : Set} → (Q : ∥ A ∥ → Set)
  → ((x y : ∥ A ∥) → (u : Q x) → (v : Q y) → tr Q (α x y) u ≡ v) ↔ ((t : ∥ A ∥) → is-prop (Q t))
prop-trunc-coh-iff-prop-fam Q = prop-trunc-coh-to-prop-fam Q , prop-fam-to-prop-trunc-coh Q

-- the induction principle in the form it is used in practice
ind-prop-trunc-prop : {A : Set} → (Q : ∥ A ∥ → Set) → ((t : ∥ A ∥) → is-prop (Q t))
  → ((a : A) → Q (η a)) → (t : ∥ A ∥) → Q t
ind-prop-trunc-prop Q Qprop f = ind-prop-trunc {Q = Q} f (prop-fam-to-prop-trunc-coh Q Qprop)

-- recursion: induction into a constant family of propositions
rec-prop-trunc : {A : Set} → (Q : Set) → is-prop Q → (A → Q) → ∥ A ∥ → Q
rec-prop-trunc Q Qprop = ind-prop-trunc-prop (λ _ → Q) λ _ → Qprop 

-- Theorem 14.2.4
η-is-prop-trunc : {A : Set} → is-prop-trunc (prop-trunc-is-prop A) η
η-is-prop-trunc Q Qprop = ext-to-precomp-is-equiv η Q Qprop (ind-prop-trunc-prop (λ _ → Q) λ t → Qprop)

-- Proposition 14.2.5
map-prop-trunc : {A B : Set} → (A → B) → ∥ A ∥ → ∥ B ∥
map-prop-trunc {A} {B} f = rec-prop-trunc ∥ B ∥ (prop-trunc-is-prop B) (η ∘ f)

-- ∥  ∥ extends η ∘ f along η
map-prop-trunc-η : {A B : Set} → (f : A → B) → (map-prop-trunc f ∘ η) ∼ (η ∘ f)
map-prop-trunc-η f a = α _ _

map-prop-trunc-id : {A : Set} → map-prop-trunc (id {A}) ∼ id
map-prop-trunc-id x = α _ _

map-prop-trunc-comp : {A B C : Set} → (f : A → B) → (g : B → C)
  → map-prop-trunc (g ∘ f) ∼ (map-prop-trunc g ∘ map-prop-trunc f)
map-prop-trunc-comp f g x = α _ _

infixr 1 _∨_
_∨_ : (P Q : Set) → Set
P ∨ Q = ∥ P ⊎ Q ∥

inl∨ : {P Q : Set} → P → P ∨ Q
inl∨ = η ∘ inl

inr∨ : {P Q : Set} → Q → P ∨ Q
inr∨ = η ∘ inr

∨-prop : (P Q : Set) → is-prop (P ∨ Q)
∨-prop P Q = prop-trunc-is-prop (P ⊎ Q)

-- case split on a disjunction, when the goal is a proposition
elim∨ : {P Q R : Set} → is-prop R → (P → R) → (Q → R) → P ∨ Q → R
elim∨ {P} {Q} {R} Rprop pr qr = rec-prop-trunc R Rprop (λ { (inl x) → pr x ; (inr x) → qr x })

∨-up : {P Q R : Set} → is-prop R → (P ∨ Q → R) ↔ ((P → R) × (Q → R))
∨-up {P} {Q} {R} Rprop = (λ pvq→r → (λ p → pvq→r (inl∨ p)) , λ q → pvq→r (inr∨ q)) , λ { (pr , qr) → elim∨ Rprop pr qr }

∃ : (A : Set) → (P : A → Set) → Set
∃ A P = ∥ Σ A P ∥

-- Proposition 14.3.4
∃-intro : {A : Set} → (P : A → Set) → (a : A) → P a → ∃ A P
∃-intro P a p = η (a , p)

∃-prop : {A : Set} → (P : A → Set) → is-prop (∃ A P)
∃-prop {A} P = prop-trunc-is-prop (Σ A P)

-- take a witness out of an existential, when the goal is a proposition
elim∃ : {A Q : Set} → (P : A → Set) → is-prop Q → ((x : A) → P x → Q) → ∃ A P → Q
elim∃ {A} {Q} P Qprop xPxQ = rec-prop-trunc Q Qprop (λ { (x , x₁) → xPxQ x x₁ })

∃-up : {A Q : Set} → (P : A → Set) → is-prop Q → (∃ A P → Q) ↔ ((x : A) → P x → Q)
∃-up {A} {Q} P Qprop = (λ exQ x Px → exQ (η (x , Px))) , elim∃ P Qprop

-- Table on p. 181: propositions are closed under every logical connective
--
--   connective       interpretation      closure lemma
--   ⊤                𝟙                   unit-prop   (ch12)
--   ⊥                𝟘                   empty-prop  (ch12)
--   P ⇒ Q            P → Q               →-prop
--   P ∧ Q            P × Q               prop-×      (ch12)
--   P ∨ Q            ∥ P ⊎ Q ∥           ∨-prop
--   P ⇔ Q            P ↔ Q               ↔-prop
--   ∃ (x : A) P x    ∥ Σ A P ∥           ∃-prop
--   ∀ (x : A) P x    (x : A) → P x       Π-prop

↔-prop : {P Q : Set} → is-prop P → is-prop Q → is-prop (P ↔ Q)
↔-prop {P} {Q} Pprop Qprop = prop-× (→-prop P Q Qprop) (→-prop Q P Pprop)

Π-prop : {A : Set} → (B : A → Set) → ((x : A) → is-prop (B x)) → is-prop ((x : A) → B x)
Π-prop {A} B Bprop = fam-trunc-to-Π-trunc Bprop
