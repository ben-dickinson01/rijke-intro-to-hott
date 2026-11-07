{-# OPTIONS --without-K #-}

open import ch13 public

-- 14.1 The universal property of propositional truncations

-- Definition 14.1.1
is-prop-trunc : {A P : Set ℓ} → is-prop P → (f : A → P) → Set (lsuc ℓ)
is-prop-trunc {ℓ} Pprop f = (Q : Set ℓ) → (Qprop : is-prop Q) → is-equiv (precomp f Q)

-- Remark 14.1.2: every map into a proposition extends uniquely along a propositional truncation
is-prop-trunc-to-unique-ext : {A P : Set ℓ} → (Pprop : is-prop P) → (f : A → P) → is-prop-trunc Pprop f
  → (Q : Set ℓ) → is-prop Q → (g : A → Q) → is-contr (fib (precomp f Q) g)
is-prop-trunc-to-unique-ext {A = A} {P = P} Pprop f fproptrunc Q Qprop g = equiv-to-contr-map (precomp f Q) (fproptrunc Q Qprop) g

-- the extension itself, forgetting uniqueness
is-prop-trunc-to-ext : {A P : Set ℓ} → (Pprop : is-prop P) → (f : A → P) → is-prop-trunc Pprop f
  → (Q : Set ℓ) → is-prop Q → (A → Q) → (P → Q)
is-prop-trunc-to-ext Pprop f fproptrunc Q Qprop = proj₁ (proj₁ (fproptrunc Q Qprop))

-- Remark 14.1.3
→-prop : (X : Set ℓ) (Q : Set ℓ₁) → is-prop Q → is-prop (X → Q)
→-prop X Q Qprop = fam-trunc-to-Π-trunc λ x → Qprop

-- for a single proposition Q, extending maps into Q along f makes precomposition with f an equivalence
ext-to-precomp-is-equiv : {A : Set ℓ} {P : Set ℓ₁} → (f : A → P) → (Q : Set ℓ₂) → is-prop Q
  → ((A → Q) → (P → Q)) → is-equiv (precomp f Q)
ext-to-precomp-is-equiv {A = A} {P = P} f Q Qprop ext = proj₂ (iff-to-≃ (→-prop P Q Qprop) (→-prop A Q Qprop) (precomp f Q , ext))

-- to show f is a propositional truncation it suffices to extend maps into propositions along f
ext-to-is-prop-trunc : {A P : Set ℓ} → (Pprop : is-prop P) → (f : A → P)
  → ((Q : Set ℓ) → is-prop Q → (A → Q) → (P → Q)) → is-prop-trunc Pprop f
ext-to-is-prop-trunc Pprop f ext Q Qprop = ext-to-precomp-is-equiv f Q Qprop (ext Q Qprop)

-- Proposition 14.1.4
-- (i) and (ii) imply (iii)
prop-truncs-to-equiv : {A P P' : Set ℓ} → (Pprop : is-prop P) → (Pprop' : is-prop P') → (f : A → P) → (f' : A → P')
  → is-prop-trunc Pprop f → is-prop-trunc Pprop' f' → P ≃ P'
prop-truncs-to-equiv {A = A} {P = P} {P' = P'} Pprop Pprop' f f' fproptrunc f'proptrunc =
  iff-to-≃ Pprop Pprop' (is-prop-trunc-to-ext Pprop f fproptrunc P' Pprop' f' , is-prop-trunc-to-ext Pprop' f' f'proptrunc P Pprop f)

-- the equivalence in (iii) is unique
≃-prop : {P : Set ℓ} {P' : Set ℓ₁} → is-prop P → is-prop P' → is-prop (P ≃ P')
≃-prop {P = P} {P' = P'} Pprop Pprop' = fam-trunc-to-Σ-trunc (→-prop P P' Pprop') λ g → equiv-is-prop g

precomp-equiv-to-equiv : {P : Set ℓ} {P' : Set ℓ₁} → (e : P ≃ P') → (X : Set ℓ₂) → is-equiv (precomp (proj₁ e) X)
precomp-equiv-to-equiv (e , eq) X = precomp-Π-is-equiv-to-precomp-is-equiv e (is-equiv-to-precomp-Π-is-equiv e eq) X

-- (iii) and (i) imply (ii); (iii) and (ii) imply (i) by swapping roles and using inv-≃
equiv-to-prop-trunc-to-prop-trunc : {A P P' : Set ℓ} → (Pprop : is-prop P) → (Pprop' : is-prop P') → (f : A → P) → (f' : A → P')
  → P ≃ P' → is-prop-trunc Pprop f → is-prop-trunc Pprop' f'
equiv-to-prop-trunc-to-prop-trunc Pprop Pprop' f f' (e , eq) fproptrunc Q Qprop =
    htpy-of-equiv-is-equiv
        (λ z z₁ → z (e (f z₁)))
        (λ z z₁ → z (f' z₁))
        (λ h → eq-htpy _ _ λ a → ap h (proj₁ (Pprop' (e (f a)) (f' a))))
        (equiv-comp (precomp e Q) (precomp f Q) (precomp-equiv-to-equiv ((e , eq)) Q) (fproptrunc Q Qprop))

-- Remark 14.1.5: A → ¬¬A has the universal property, but only against doubly negated propositions
precomp-dni-¬¬-is-equiv : (A : Set ℓ) (Q : Set ℓ₁) → is-equiv (precomp (dni {P = A}) (¬¬ Q))
precomp-dni-¬¬-is-equiv A Q = ext-to-precomp-is-equiv dni (¬¬ Q) (¬-prop (¬ Q)) dn-bind

-- 14.2 Propositional truncations as higher inductive types

-- Definition 14.2.2, with the formation rule and constructors
postulate
    ∥_∥ : Set ℓ → Set ℓ
    η : {A : Set ℓ} → A → ∥ A ∥
    α : {A : Set ℓ} → (x y : ∥ A ∥) → x ≡ y

    ind-prop-trunc : {A : Set ℓ} → {Q : ∥ A ∥ → Set ℓ₁} →
      (f : (a : A) → Q (η a)) →
      (coh : (x y : ∥ A ∥) → (u : Q x) → (v : Q y) → tr Q (α x y) u ≡ v) →
      (t : ∥ A ∥) → Q t

    comp-prop-trunc : {A : Set ℓ} → {Q : ∥ A ∥ → Set ℓ₁} →
      (f : (a : A) → Q (η a)) →
      (coh : (x y : ∥ A ∥) → (u : Q x) → (v : Q y) → tr Q (α x y) u ≡ v) →
      (a : A) → ind-prop-trunc f coh (η a) ≡ f a

is-prop'-to-is-prop : {A : Set ℓ} → is-prop' A → is-prop A
is-prop'-to-is-prop {A = A} propA' = emb-𝟙-to-is-prop (inhab-contr-to-emb-𝟙 (is-prop'-to-inhab-contr propA'))

-- Lemma 14.2.1
prop-trunc-is-prop : (A : Set ℓ) → is-prop ∥ A ∥
prop-trunc-is-prop A = is-prop'-to-is-prop α

-- Remark 14.2.3: the coherence hypothesis of ind-prop-trunc holds exactly for families of propositions
prop-trunc-coh-to-prop-fam : {A : Set ℓ} → (Q : ∥ A ∥ → Set ℓ₁)
  → ((x y : ∥ A ∥) → (u : Q x) → (v : Q y) → tr Q (α x y) u ≡ v) → ((t : ∥ A ∥) → is-prop (Q t))
prop-trunc-coh-to-prop-fam {A = A} Q coh t = is-prop'-to-is-prop λ qt₁ qt₂ → concat (inv (coh t t qt₁ qt₁)) (coh t t qt₁ qt₂)

prop-fam-to-prop-trunc-coh : {A : Set ℓ} → (Q : ∥ A ∥ → Set ℓ₁)
  → ((t : ∥ A ∥) → is-prop (Q t)) → ((x y : ∥ A ∥) → (u : Q x) → (v : Q y) → tr Q (α x y) u ≡ v)
prop-fam-to-prop-trunc-coh {A = A} Q Qprop x y u v = proj₁ (Qprop y (tr Q (α x y) u) v)

prop-trunc-coh-iff-prop-fam : {A : Set ℓ} → (Q : ∥ A ∥ → Set ℓ₁)
  → ((x y : ∥ A ∥) → (u : Q x) → (v : Q y) → tr Q (α x y) u ≡ v) ↔ ((t : ∥ A ∥) → is-prop (Q t))
prop-trunc-coh-iff-prop-fam Q = prop-trunc-coh-to-prop-fam Q , prop-fam-to-prop-trunc-coh Q

-- the induction principle in the form it is used in practice
ind-prop-trunc-prop : {A : Set ℓ} → (Q : ∥ A ∥ → Set ℓ₁) → ((t : ∥ A ∥) → is-prop (Q t))
  → ((a : A) → Q (η a)) → (t : ∥ A ∥) → Q t
ind-prop-trunc-prop Q Qprop f = ind-prop-trunc {Q = Q} f (prop-fam-to-prop-trunc-coh Q Qprop)

-- recursion: induction into a constant family of propositions
rec-prop-trunc : {A : Set ℓ} → (Q : Set ℓ₁) → is-prop Q → (A → Q) → ∥ A ∥ → Q
rec-prop-trunc Q Qprop = ind-prop-trunc-prop (λ _ → Q) λ _ → Qprop

-- Theorem 14.2.4
η-is-prop-trunc : {A : Set ℓ} → is-prop-trunc (prop-trunc-is-prop A) η
η-is-prop-trunc Q Qprop = ext-to-precomp-is-equiv η Q Qprop (ind-prop-trunc-prop (λ _ → Q) λ t → Qprop)

-- Proposition 14.2.5
map-prop-trunc : {A : Set ℓ} {B : Set ℓ₁} → (A → B) → ∥ A ∥ → ∥ B ∥
map-prop-trunc {A = A} {B = B} f = rec-prop-trunc ∥ B ∥ (prop-trunc-is-prop B) (η ∘ f)

-- ∥ f ∥ extends η ∘ f along η
map-prop-trunc-η : {A : Set ℓ} {B : Set ℓ₁} → (f : A → B) → (map-prop-trunc f ∘ η) ∼ (η ∘ f)
map-prop-trunc-η f a = α _ _

map-prop-trunc-id : {A : Set ℓ} → map-prop-trunc (id {A = A}) ∼ id
map-prop-trunc-id x = α _ _

map-prop-trunc-comp : {A : Set ℓ} {B : Set ℓ₁} {C : Set ℓ₂} → (f : A → B) → (g : B → C)
  → map-prop-trunc (g ∘ f) ∼ (map-prop-trunc g ∘ map-prop-trunc f)
map-prop-trunc-comp f g x = α _ _

-- 14.3 Logic in type theory

-- Definition 14.3.1
infixr 1 _∨_
_∨_ : (P : Set ℓ) (Q : Set ℓ₁) → Set (ℓ ⊔ ℓ₁)
P ∨ Q = ∥ P ⊎ Q ∥

-- Proposition 14.3.2
inl∨ : {P : Set ℓ} {Q : Set ℓ₁} → P → P ∨ Q
inl∨ = η ∘ inl

inr∨ : {P : Set ℓ} {Q : Set ℓ₁} → Q → P ∨ Q
inr∨ = η ∘ inr

∨-prop : (P : Set ℓ) (Q : Set ℓ₁) → is-prop (P ∨ Q)
∨-prop P Q = prop-trunc-is-prop (P ⊎ Q)

-- case split on a disjunction, when the goal is a proposition
elim∨ : {P : Set ℓ} {Q : Set ℓ₁} {R : Set ℓ₂} → is-prop R → (P → R) → (Q → R) → P ∨ Q → R
elim∨ {P = P} {Q = Q} {R = R} Rprop pr qr = rec-prop-trunc R Rprop (λ { (inl x) → pr x ; (inr x) → qr x })

∨-up : {P : Set ℓ} {Q : Set ℓ₁} {R : Set ℓ₂} → is-prop R → (P ∨ Q → R) ↔ ((P → R) × (Q → R))
∨-up {P = P} {Q = Q} {R = R} Rprop = (λ pvq→r → (λ p → pvq→r (inl∨ p)) , λ q → pvq→r (inr∨ q)) , λ { (pr , qr) → elim∨ Rprop pr qr }

-- Definition 14.3.3
∃ : (A : Set ℓ) → (P : A → Set ℓ₁) → Set (ℓ ⊔ ℓ₁)
∃ A P = ∥ Σ A P ∥

-- Proposition 14.3.4
∃-intro : {A : Set ℓ} → (P : A → Set ℓ₁) → (a : A) → P a → ∃ A P
∃-intro P a p = η (a , p)

∃-prop : {A : Set ℓ} → (P : A → Set ℓ₁) → is-prop (∃ A P)
∃-prop {A = A} P = prop-trunc-is-prop (Σ A P)

-- take a witness out of an existential, when the goal is a proposition
elim∃ : {A : Set ℓ} {Q : Set ℓ₁} → (P : A → Set ℓ₂) → is-prop Q → ((x : A) → P x → Q) → ∃ A P → Q
elim∃ {A = A} {Q = Q} P Qprop xPxQ = rec-prop-trunc Q Qprop (λ { (x , x₁) → xPxQ x x₁ })

∃-up : {A : Set ℓ} {Q : Set ℓ₁} → (P : A → Set ℓ₂) → is-prop Q → (∃ A P → Q) ↔ ((x : A) → P x → Q)
∃-up {A = A} {Q = Q} P Qprop = (λ exQ x Px → exQ (η (x , Px))) , elim∃ P Qprop

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

↔-prop : {P : Set ℓ} {Q : Set ℓ₁} → is-prop P → is-prop Q → is-prop (P ↔ Q)
↔-prop {P = P} {Q = Q} Pprop Qprop = prop-× (→-prop P Q Qprop) (→-prop Q P Pprop)

Π-prop : {A : Set ℓ} → (B : A → Set ℓ₁) → ((x : A) → is-prop (B x)) → is-prop ((x : A) → B x)
Π-prop {A = A} B Bprop = fam-trunc-to-Π-trunc Bprop

-- 14.4 Mapping propositional truncations into sets

-- Example 14.4.1
is-lower-bound-propℕ : (P : ℕ → Set ℓ) → (n : ℕ) → is-prop (is-lower-bound P n)
is-lower-bound-propℕ P n = Π-prop _ λ x → →-prop (P x) (n ≤ℕ x) (≤-propℕ n x)

least-element-propℕ : (P : ℕ → Set ℓ) → is-subtype ℕ P → is-prop (Σ ℕ (λ m → P m × is-lower-bound P m))
least-element-propℕ P Psubtype = is-prop'-to-is-prop λ {(n , (pn , ln)) (m , (pm , lm)) →
  eq-pair _ _ (≤-antisymℕ n m (ln m pm) (lm n pn) , proj₁ (prop-× (Psubtype m) (is-lower-bound-propℕ P m) _ _))}

∃-to-Σ-decidableℕ : (P : ℕ → Set ℓ) → is-subtype ℕ P → ((n : ℕ) → is-decidable (P n)) → ∃ ℕ P → Σ ℕ P
∃-to-Σ-decidableℕ P Psubtype Pdec t = proj₁ lbP , proj₁ (proj₂ (lbP))
    where
    lbP : Σ ℕ (λ m → P m × is-lower-bound P m)
    lbP = rec-prop-trunc (Σ ℕ (λ m → P m × is-lower-bound P m)) (least-element-propℕ P Psubtype) (ℕ-well-ordered P Pdec) t

-- corollary of Example 14.4.1 for Fin k
Fin-decidable-Σ : (k : ℕ) → (P : Fin k → Set ℓ) → ((x : Fin k) → is-decidable (P x)) → is-decidable (Σ (Fin k) P)
Fin-decidable-Σ 0ℕ P Pdec = inr λ { (() , _) }
Fin-decidable-Σ (succℕ k) P Pdec with Fin-decidable-Σ k (λ x → P (inl x)) (λ x → Pdec (inl x))
... | inl (x , px) = inl (inl x , px)
... | inr nΣ with Pdec (inr *)
...   | inl p = inl (inr * , p)
...   | inr np = inr λ { (inl x , px) → nΣ (x , px) ; (inr * , px) → np px }

∃-to-Σ-decidableFin : (k : ℕ) → (P : Fin k → Set ℓ) → ((x : Fin k) → is-decidable (P x)) → ∃ (Fin k) P → Σ (Fin k) P
∃-to-Σ-decidableFin k P Pdec t with Fin-decidable-Σ k P Pdec
... | inl w = w
... | inr nw = ex-falso (elim∃ P empty-prop (λ x p → nw (x , p)) t)

-- Remark 14.4.2
has-global-choice : (A : Set ℓ) → Set ℓ
has-global-choice A = ∥ A ∥ → A

-- Definition 14.4.3
is-weakly-constant : {A : Set ℓ} {B : Set ℓ₁} → (f : A → B) → Set (ℓ ⊔ ℓ₁)
is-weakly-constant {A = A} f = (x y : A) → f x ≡ f y

-- Remark 14.4.4
is-constant : {A : Set ℓ} {B : Set ℓ₁} → (f : A → B) → Set (ℓ ⊔ ℓ₁)
is-constant {A = A} {B = B} f = Σ B (λ b → f ∼ const {A = A} {B = B} {b = b})

constant-to-weakly-constant : {A : Set ℓ} {B : Set ℓ₁} → (f : A → B) → is-constant f → is-weakly-constant f
constant-to-weakly-constant f fconst x y = concat (proj₂ (fconst) x) (inv (proj₂ (fconst) y))

contr-iff-id-constant : (A : Set ℓ) → is-contr A ↔ is-constant (id {A = A})
contr-iff-id-constant A = (λ {(a , eqa) → a , λ x → eqa x}) , λ {(a , idhc) → a , idhc}

prop-iff-id-weakly-constant : (A : Set ℓ) → is-prop A ↔ is-weakly-constant (id {A = A})
prop-iff-id-weakly-constant A = (λ {Aprop x y → proj₁ (Aprop x y) }) , λ Awc → is-prop'-to-is-prop Awc

-- Lemma 14.4.5
comm-tri-η-to-weakly-constant-f : {A : Set ℓ} {B : Set ℓ₁} → (f : A → B) → (g : ∥ A ∥ → B) → triangle-commutes f η g → is-weakly-constant f
comm-tri-η-to-weakly-constant-f {A = A} {B = B} f g H x y = concat (H x) (concat (ap g (α _ _)) (inv (H y)))

-- Theorem 14.4.6 (Kraus)
-- the map g ↦ (g ∘ η , λ x y → ap g (α (η x) (η y)))
prop-trunc-to-weakly-constant : {A : Set ℓ} {B : Set ℓ₁} → (∥ A ∥ → B) → Σ (A → B) is-weakly-constant
prop-trunc-to-weakly-constant g = (g ∘ η) , λ x y → ap g (α (η x) (η y))

-- proof, step 1: f extends in at most one way
set-ext-along-η-unique : {A : Set ℓ} {B : Set ℓ₁} → is-set B → (f : A → B) → (g h : ∥ A ∥ → B)
  → triangle-commutes f η g → triangle-commutes f η h → g ∼ h
set-ext-along-η-unique {A = A} {B = B} Bset f g h G H = ind-prop-trunc-prop (λ t → g t ≡ h t) (λ t → Bset (g t) (h t)) (λ a → concat (inv (G a)) (H a))

-- proof, step 2: Σ (b : B) ∥ fib f b ∥ is a proposition
weakly-constant-image-prop : {A : Set ℓ} {B : Set ℓ₁} → is-set B → (f : A → B) → is-weakly-constant f
  → is-prop (Σ B (λ b → ∥ fib f b ∥))
weakly-constant-image-prop Bset f H = is-prop'-to-is-prop λ {(b , s) (b' , s') →
  eq-pair _ _ (elim∃ (λ x → f x ≡ b) (Bset b b')
    (λ x p → elim∃ (λ x → f x ≡ b') (Bset b b') (λ x' p' → concat (inv p) (concat (H x x') p')) s') s , α _ _)}

-- is-weakly-constant f is a proposition when the codomain is a set
weakly-constant-prop : {A : Set ℓ} {B : Set ℓ₁} → is-set B → (f : A → B) → is-prop (is-weakly-constant f)
weakly-constant-prop Bset f = Π-prop _ λ x → Π-prop _ λ y → Bset (f x) (f y)

-- proof, step 3: a weakly constant map into a set extends along η
weakly-constant-ext : {A : Set ℓ} {B : Set ℓ₁} → is-set B → (f : A → B) → is-weakly-constant f → ∥ A ∥ → B
weakly-constant-ext {A = A} {B = B} Bset f H = proj₁ ∘ rec-prop-trunc (Σ B (λ b → ∥ fib f b ∥)) (weakly-constant-image-prop Bset f H) (λ x → f x , η (x , refl))

weakly-constant-ext-η : {A : Set ℓ} {B : Set ℓ₁} → (Bset : is-set B) → (f : A → B) → (H : is-weakly-constant f)
  → (a : A) → weakly-constant-ext Bset f H (η a) ≡ f a
weakly-constant-ext-η Bset f H a =
  ap proj₁ (proj₁ (weakly-constant-image-prop Bset f H
    (rec-prop-trunc _ (weakly-constant-image-prop Bset f H) (λ x → f x , η (x , refl)) (η a)) (f a , η (a , refl))))

prop-trunc-set-up : (A : Set ℓ) → {B : Set ℓ₁} → is-set B → is-equiv (prop-trunc-to-weakly-constant {A = A} {B = B})
prop-trunc-set-up A {B} Bset = (ψ , φψ) , (ψ , ψφ)
    where
        ψ : Σ (A → B) is-weakly-constant → ∥ A ∥ → B
        ψ (f , H) = weakly-constant-ext Bset f H
        φψ : prop-trunc-to-weakly-constant ∘ ψ ∼ id
        φψ (f , H) = eq-pair _ _ (eq-htpy _ _ (weakly-constant-ext-η Bset f H) , proj₁ (weakly-constant-prop Bset f _ _))
        ψφ : ψ ∘ prop-trunc-to-weakly-constant ∼ id
        ψφ g = eq-htpy _ _ (set-ext-along-η-unique Bset (g ∘ η) (ψ (prop-trunc-to-weakly-constant g)) g
          (λ a → inv (weakly-constant-ext-η Bset (g ∘ η) _ a)) (λ a → refl))

-- Exercises
-- 14.1
-- a
double-prop-trunc-to-prop-trunc : {A : Set ℓ} → ∥ ∥ A ∥ ∥ → ∥ A ∥
double-prop-trunc-to-prop-trunc {A = A} = rec-prop-trunc ∥ A ∥ (prop-trunc-is-prop A) id

prop-trunc-to-double-prop-trunc : {A : Set ℓ} → ∥ A ∥ → ∥ ∥ A ∥ ∥
prop-trunc-to-double-prop-trunc ta = η ta

-- b
prop-trunc-dec-to-dec-prop-trunc : {A : Set ℓ} → ∥ is-decidable A ∥ → is-decidable ∥ A ∥
prop-trunc-dec-to-dec-prop-trunc {A = A} = rec-prop-trunc (is-decidable ∥ A ∥) (to-neg-to-prop-⊎ (prop-trunc-is-prop A) (¬-prop ∥ A ∥) dni) λ {(inl a) → inl (η a)
                                                                                    ; (inr na) → inr (rec-prop-trunc 𝟘 empty-prop na)}

dec-prop-trunc-to-prop-trunc-dec : {A : Set ℓ} → is-decidable ∥ A ∥ → ∥ is-decidable A ∥
dec-prop-trunc-to-prop-trunc-dec {A = A} (inl t) = map-prop-trunc inl t
dec-prop-trunc-to-prop-trunc-dec {A = A} (inr nt) = η (inr λ a → nt (η a))

-- c
prop-has-global-choice : {P : Set ℓ} → is-prop P → ∥ P ∥ → P
prop-has-global-choice {P = P} Pprop = rec-prop-trunc P Pprop id

is-dec-to-global-choice : {A : Set ℓ} → is-decidable A → has-global-choice A
is-dec-to-global-choice (inl a) t = a
is-dec-to-global-choice (inr na) t = ex-falso (prop-has-global-choice empty-prop (map-prop-trunc na t))

-- d
¬¬-prop-trunc-to-¬¬ : {A : Set ℓ} → ¬¬ ∥ A ∥ → ¬¬ A
¬¬-prop-trunc-to-¬¬ {A = A} = dn-bind (rec-prop-trunc (¬¬ A) (¬-prop (¬ A)) dni)

¬¬-to-¬¬-prop-trunc : {A : Set ℓ} → ¬¬ A → ¬¬ ∥ A ∥
¬¬-to-¬¬-prop-trunc = dn-functor η

-- e
∨-prop-trunc-to-∨ : {A : Set ℓ} {B : Set ℓ₁} → ∥ A ∥ ∨ ∥ B ∥ → A ∨ B
∨-prop-trunc-to-∨ {A = A} {B = B} = rec-prop-trunc (A ∨ B) (prop-trunc-is-prop _) λ {(inl ta) → map-prop-trunc inl ta
                                                                           ; (inr tb) → map-prop-trunc inr tb}

∨-to-∨-prop-trunc : {A : Set ℓ} {B : Set ℓ₁} → ∥ A ⊎ B ∥ → ∥ A ∥ ∨ ∥ B ∥
∨-to-∨-prop-trunc {A = A} {B = B} t = rec-prop-trunc (∥ A ∥ ∨ ∥ B ∥) (prop-trunc-is-prop _) (λ {(inl a) → η (inl (η a))
                                                                                      ; (inr b) → η (inr (η b))}) t

-- f
∃-prop-trunc-to-∃ : {A : Set ℓ} → (B : A → Set ℓ₁) → ∃ A (λ x → ∥ B x ∥) → ∥ Σ A B ∥
∃-prop-trunc-to-∃ {A = A} B = rec-prop-trunc ∥ Σ A B ∥ (prop-trunc-is-prop _) λ {(a , tb) → map-prop-trunc ((_,_ a)) tb}

∃-to-∃-prop-trunc : {A : Set ℓ} → (B : A → Set ℓ₁) → ∥ Σ A B ∥ → ∃ A (λ x → ∥ B x ∥)
∃-to-∃-prop-trunc {A = A} B = rec-prop-trunc (∃ A (λ x → ∥ B x ∥)) (prop-trunc-is-prop _) λ {(a , b) → η (a , η b)}

-- g
¬¬-global-choice : {A : Set ℓ} → ¬¬ (has-global-choice A)
¬¬-global-choice {A = A} = dn-functor is-dec-to-global-choice dn-lem

-- 14.2
mere-eq : {A : Set ℓ} → A → A → Set ℓ
mere-eq x y = ∥ x ≡ y ∥

mere-eq-is-rfl : (A : Set ℓ) → is-reflexive (mere-eq {A = A})
mere-eq-is-rfl A x = η refl

mere-eq-is-symm : (A : Set ℓ) → is-symmetric (mere-eq {A = A})
mere-eq-is-symm A x y tp = map-prop-trunc inv tp

mere-eq-is-trans : (A : Set ℓ) → is-transitive (mere-eq {A = A})
mere-eq-is-trans A x y z tp tq = rec-prop-trunc ∥ x ≡ z ∥ (prop-trunc-is-prop _) (λ p → map-prop-trunc (concat p) tq) tp

-- 14.3
prop-truncs-to-×'-is-prop-trunc : {A B P Q : Set ℓ} → (Pprop : is-prop P) → (Qprop : is-prop Q) → (f : A → P) → (g : B → Q)
  → is-prop-trunc Pprop f → is-prop-trunc Qprop g → is-prop-trunc (prop-× Pprop Qprop) (f ×' g)
prop-truncs-to-×'-is-prop-trunc {A = A} {B = B} {P = P} {Q = Q} Pprop Qprop f g fproptrunc gproptrunc =
  ext-to-is-prop-trunc (prop-× Pprop Qprop) (f ×' g) λ { R Rprop h (p , q) →
    is-prop-trunc-to-ext Pprop f fproptrunc (Q → R) (→-prop Q R Rprop)
      (λ a → is-prop-trunc-to-ext Qprop g gproptrunc R Rprop (λ b → h (a , b))) p q }

-- the conclusion of 14.3: ∥ A × B ∥ ≃ ∥ A ∥ × ∥ B ∥
prop-trunc-×-≃-×-prop-trunc : {A B : Set ℓ} → ∥ A × B ∥ ≃ ∥ A ∥ × ∥ B ∥
prop-trunc-×-≃-×-prop-trunc {A = A} {B = B} =
  prop-truncs-to-equiv (prop-trunc-is-prop (A × B)) (prop-× (prop-trunc-is-prop A) (prop-trunc-is-prop B))
    η (η ×' η) η-is-prop-trunc
    (prop-truncs-to-×'-is-prop-trunc (prop-trunc-is-prop A) (prop-trunc-is-prop B) η η η-is-prop-trunc η-is-prop-trunc)

-- 14.4
is-dep-prop-trunc : {A P : Set ℓ} → is-prop P → (f : A → P) → Set (lsuc ℓ)
is-dep-prop-trunc {ℓ} {P = P} Pprop f = (Q : P → Set ℓ) → ((p : P) → is-prop (Q p)) → is-equiv (precomp-Π f Q)

-- (i) implies (ii)
prop-trunc-to-dep-prop-trunc : {A P : Set ℓ} → (Pprop : is-prop P) → (f : A → P)
  → is-prop-trunc Pprop f → is-dep-prop-trunc Pprop f
prop-trunc-to-dep-prop-trunc {A = A} {P = P} Pprop f fproptrunc Q Qprop =
  proj₂ (iff-to-≃ (Π-prop Q Qprop) (Π-prop (λ x → Q (f x)) (λ x → Qprop (f x)))
    (precomp-Π f Q ,
     λ h p → is-prop-trunc-to-ext Pprop f fproptrunc (Q p) (Qprop p) (λ a → tr Q (proj₁ (Pprop (f a) p)) (h a)) p))

-- (ii) implies (i)
dep-prop-trunc-to-prop-trunc : {A P : Set ℓ} → (Pprop : is-prop P) → (f : A → P) → is-dep-prop-trunc Pprop f → is-prop-trunc Pprop f
dep-prop-trunc-to-prop-trunc {A = A} {P = P} Pprop f fdepproptrunc Q Qprop = fdepproptrunc (λ _ → Q) λ _ → Qprop

-- 14.5
-- (a)
iff-prop-to-prop-trunc : {A P : Set ℓ} → (Pprop : is-prop P) → (f : A → P) → (P → A) → is-prop-trunc Pprop f
iff-prop-to-prop-trunc Pprop f g = ext-to-is-prop-trunc Pprop f (λ Q Qprop h → h ∘ g)

const𝟙-is-prop-trunc : {A : Set} → (a : A) → is-prop-trunc unit-prop (const {A = A} {B = 𝟙} {b = *})
const𝟙-is-prop-trunc a = iff-prop-to-prop-trunc unit-prop const (λ _ → a)

-- (b)
equiv-to-prop-trunc : {A P : Set ℓ} → (Pprop : is-prop P) → (f : A → P) → is-equiv f → is-prop-trunc Pprop f
equiv-to-prop-trunc {A = A} {P = P} Pprop f fequiv = iff-prop-to-prop-trunc Pprop f (proj₁ (proj₁ fequiv))

prop-to-prop-trunc-to-equiv : {A P : Set ℓ} → (Pprop : is-prop P) → (f : A → P) → (Aprop : is-prop A) → is-prop-trunc Pprop f → is-equiv f
prop-to-prop-trunc-to-equiv {A = A} Pprop f Aprop fproptrunc = proj₂ (iff-to-≃ Aprop Pprop (f , is-prop-trunc-to-ext Pprop f fproptrunc A Aprop id))

prop-id-is-prop-trunc : {A : Set ℓ} → (Aprop : is-prop A) → is-prop-trunc Aprop id
prop-id-is-prop-trunc {A = A} Aprop = equiv-to-prop-trunc Aprop id (is-equiv-id A)
-- 14.6
-- (a)
dec-to-inl-fib : {A : Set ℓ} → (d : is-decidable A) → A → Σ A (λ x → inl x ≡ d)
dec-to-inl-fib (inl x) a = x , refl
dec-to-inl-fib (inr x) a = ex-falso (x a)

inl-fib-prop : {A : Set ℓ} → (d : is-decidable A) → is-prop (Σ A (λ x → inl x ≡ d))
inl-fib-prop {A = A} d = emb-to-fib-prop inl (inl-emb A (¬ A)) d

dec-to-inl-fib-is-prop-trunc : {A : Set ℓ} → (d : is-decidable A) → is-prop-trunc (inl-fib-prop d) (dec-to-inl-fib d)
dec-to-inl-fib-is-prop-trunc d = iff-prop-to-prop-trunc (inl-fib-prop d) (dec-to-inl-fib d) proj₁

-- (b)
π-dec : {A : Set ℓ} → is-decidable A → 𝟚
π-dec (inl x) = true
π-dec (inr x) = false

dec-to-π-true : {A : Set ℓ} → (d : is-decidable A) → A → π-dec d ≡ true
dec-to-π-true (inl x) a = refl
dec-to-π-true (inr x) a = ex-falso (x a)

π-true-prop : {A : Set ℓ} → (d : is-decidable A) → is-prop (π-dec d ≡ true)
π-true-prop d = 𝟚-set (π-dec d) true

π-true-to-A : {A : Set ℓ} → (d : is-decidable A) → π-dec d ≡ true → A
π-true-to-A (inl x) p = x
π-true-to-A (inr x) ()

dec-to-π-true-is-prop-trunc : {A : Set} → (d : is-decidable A) → is-prop-trunc (π-true-prop d) (dec-to-π-true d)
dec-to-π-true-is-prop-trunc d = iff-prop-to-prop-trunc (π-true-prop d) (dec-to-π-true d) (π-true-to-A d)

-- 14.7
-- helpers: contractible types are k-truncated for every k, so equivalences are k-truncated maps
contr-to-k-trunc : {A : Set ℓ} → (k : 𝕋) → is-contr A → is-trunc k A
contr-to-k-trunc -2𝕋 Acontr = Acontr
contr-to-k-trunc (succ𝕋 k) Acontr = type-is-succ-type (contr-to-k-trunc k Acontr)

equiv-to-k-trunc-map : {A : Set ℓ} {B : Set ℓ₁} → (k : 𝕋) → (f : A → B) → is-equiv f → is-trunc-map k f
equiv-to-k-trunc-map k f fequiv b = contr-to-k-trunc k (equiv-to-contr-map f fequiv b)

succ-trunc-fam-to-precomp-η-is-trunc-map : {A : Set ℓ} → (k : 𝕋) → (B : ∥ A ∥ → Set ℓ)
  → ((t : ∥ A ∥) → is-trunc (succ𝕋 k) (B t)) → is-trunc-map k (precomp-Π η B)
succ-trunc-fam-to-precomp-η-is-trunc-map {A = A} -2𝕋 B Btrunc =
  equiv-to-contr-map (precomp-Π η B) (prop-trunc-to-dep-prop-trunc (prop-trunc-is-prop A) η η-is-prop-trunc B Btrunc)
succ-trunc-fam-to-precomp-η-is-trunc-map (succ𝕋 k) B Btrunc = ap-k-trunc-to-k+1-trunc-map (precomp-Π η B) λ s t →
  -- top: ap (precomp-Π η B), right: htpy-eq over A, diagonal: right ∘ top
  comm-tri-k-trunc-g-to-k-trunc-f-to-k-trunc-h
    (htpy-eq (precomp-Π η B s) (precomp-Π η B t) ∘ ap (precomp-Π η B))
    (htpy-eq (precomp-Π η B s) (precomp-Π η B t))
    (ap (precomp-Π η B))
    (λ p → refl)
    (equiv-to-k-trunc-map k (htpy-eq (precomp-Π η B s) (precomp-Π η B t)) (fun-ext (precomp-Π η B s) (precomp-Π η B t)))
    -- left: htpy-eq over ∥ A ∥, bottom: precomp-Π η on the family of identity types
    (comm-tri-k-trunc-g-to-k-trunc-h-to-k-trunc-f
      (htpy-eq (precomp-Π η B s) (precomp-Π η B t) ∘ ap (precomp-Π η B))
      (precomp-Π η (λ x → s x ≡ t x))
      (htpy-eq s t)
      (λ { refl → refl })
      (succ-trunc-fam-to-precomp-η-is-trunc-map k (λ x → s x ≡ t x) (λ x → Btrunc x (s x) (t x)))
      (equiv-to-k-trunc-map k (htpy-eq s t) (fun-ext s t)))

-- 14.8
-- impredicative encodings: each connective is equivalent to quantifying over all propositions Q
-- the encodings quantify over Set ℓ, so they live one universe up, in Set (lsuc ℓ)
imp-𝟙 : (ℓ : Level) → Set (lsuc ℓ)
imp-𝟙 ℓ = (Q : Set ℓ) → (Qprop : is-prop Q) → (q : Q) → Q

𝟙-≃-imp-𝟙 : (ℓ : Level) → 𝟙 ≃ imp-𝟙 ℓ
𝟙-≃-imp-𝟙 ℓ =
  iff-to-≃ unit-prop
    (Π-prop _ λ Q → Π-prop _ λ Qprop → Π-prop _ λ _ → Qprop)
    ((λ _ Q Qprop q → q) , λ _ → *)

imp-𝟘 : (ℓ : Level) → Set (lsuc ℓ)
imp-𝟘 ℓ = (Q : Set ℓ) → (Qprop : is-prop Q) → Q

𝟘-≃-imp-𝟘 : (ℓ : Level) → 𝟘 ≃ imp-𝟘 ℓ
𝟘-≃-imp-𝟘 ℓ =
  iff-to-≃ empty-prop
    (Π-prop _ λ Q → Π-prop _ λ Qprop → Qprop)
    ((λ ()) , λ x → map-inv-raise (x (raise ℓ 𝟘) λ { (map-raise ()) }))

imp-prop-trunc : (A : Set ℓ) → Set (lsuc ℓ)
imp-prop-trunc {ℓ} A = (Q : Set ℓ) → (Qprop : is-prop Q) → (f : A → Q) → Q

prop-trunc-≃-imp-prop-trunc : (A : Set ℓ) → ∥ A ∥ ≃ imp-prop-trunc A
prop-trunc-≃-imp-prop-trunc A =
  iff-to-≃ (prop-trunc-is-prop A)
    (Π-prop _ λ Q → Π-prop _ λ Qprop → Π-prop _ λ f → Qprop)
    ((λ t Q Qprop f → rec-prop-trunc Q Qprop f t) , λ h → h ∥ A ∥ (prop-trunc-is-prop A) η)

imp-∨ : (P₁ : Set ℓ) → (P₂ : Set ℓ₁) → Set (lsuc (ℓ ⊔ ℓ₁))
imp-∨ {ℓ} {ℓ₁} P₁ P₂ = (Q : Set (ℓ ⊔ ℓ₁)) → (Qprop : is-prop Q) → (f : P₁ → Q) → (g : P₂ → Q) → Q

∨-≃-imp-∨ : (P₁ : Set ℓ) → (P₂ : Set ℓ₁) → P₁ ∨ P₂ ≃ imp-∨ P₁ P₂
∨-≃-imp-∨ P₁ P₂ =
  iff-to-≃ (∨-prop P₁ P₂)
    (Π-prop _ λ Q → Π-prop _ λ Qprop → Π-prop _ λ f → Π-prop _ λ g → Qprop)
    ((λ t Q Qprop f g → elim∨ Qprop f g t) , λ h → h (P₁ ∨ P₂) (∨-prop P₁ P₂) inl∨ inr∨)

imp-× : (P₁ : Set ℓ) → (P₂ : Set ℓ₁) → (P₁prop : is-prop P₁) → (P₂prop : is-prop P₂) → Set (lsuc (ℓ ⊔ ℓ₁))
imp-× {ℓ} {ℓ₁} P₁ P₂ P₁prop P₂prop = (Q : Set (ℓ ⊔ ℓ₁)) → (Qprop : is-prop Q) → (f : P₁ → P₂ → Q) → Q

×-≃-imp-× : (P₁ : Set ℓ) → (P₂ : Set ℓ₁) → (P₁prop : is-prop P₁) → (P₂prop : is-prop P₂) → P₁ × P₂ ≃ imp-× P₁ P₂ P₁prop P₂prop
×-≃-imp-× P₁ P₂ P₁prop P₂prop =
  iff-to-≃ (prop-× P₁prop P₂prop)
    (Π-prop _ λ Q → Π-prop _ λ Qprop → Π-prop _ λ f → Qprop)
    ((λ { (p₁ , p₂) Q Qprop f → f p₁ p₂ }) , λ h → h (P₁ × P₂) (prop-× P₁prop P₂prop) _,_)

-- Q only needs to reach P₂'s level: the backward map instantiates Q := P₂
imp-→ : (P₁ : Set ℓ) → (P₂ : Set ℓ₁) → Set (ℓ ⊔ lsuc ℓ₁)
imp-→ {ℓ₁ = ℓ₁} P₁ P₂ = (Q : Set ℓ₁) → (Qprop : is-prop Q) → (p : P₁) → (k : P₂ → Q) → Q

→-≃-imp-→ : (P₁ : Set ℓ) → (P₂ : Set ℓ₁) → (P₂prop : is-prop P₂) → (P₁ → P₂) ≃ imp-→ P₁ P₂
→-≃-imp-→ P₁ P₂ P₂prop =
  iff-to-≃ (→-prop P₁ P₂ P₂prop)
    (Π-prop _ λ Q → Π-prop _ λ Qprop → Π-prop _ λ p → Π-prop _ λ k → Qprop)
    ((λ f Q Qprop p k → k (f p)) , λ h p → h P₂ P₂prop p id)

-- the backward map instantiates Q at the empty type, raised to A's level
imp-¬ : (A : Set ℓ) → Set (lsuc ℓ)
imp-¬ {ℓ} A = (Q : Set ℓ) → (Qprop : is-prop Q) → (a : A) → Q

¬-≃-imp-¬ : (A : Set ℓ) → ¬ A ≃ imp-¬ A
¬-≃-imp-¬ {ℓ} A =
  iff-to-≃ (¬-prop A)
    (Π-prop _ λ Q → Π-prop _ λ Qprop → Π-prop _ λ a → Qprop)
    ((λ na Q Qprop a → ex-falso (na a)) , λ h a → map-inv-raise (h (raise ℓ 𝟘) (λ { (map-raise ()) }) a))

imp-∃ : (A : Set ℓ) → (P : A → Set ℓ₁) → Set (lsuc (ℓ ⊔ ℓ₁))
imp-∃ {ℓ} {ℓ₁} A P = (Q : Set (ℓ ⊔ ℓ₁)) → (Qprop : is-prop Q) → (f : (x : A) → P x → Q) → Q

∃-≃-imp-∃ : (A : Set ℓ) → (P : A → Set ℓ₁) → ∃ A P ≃ imp-∃ A P
∃-≃-imp-∃ A P =
  iff-to-≃ (∃-prop P)
    (Π-prop _ λ Q → Π-prop _ λ Qprop → Π-prop _ λ f → Qprop)
    ((λ t Q Qprop f → elim∃ P Qprop f t) , λ h → h (∃ A P) (∃-prop P) (∃-intro P))

-- Q only needs to reach the level of the fibres: the backward map instantiates Q := P x
imp-∀ : (A : Set ℓ) → (P : A → Set ℓ₁) → Set (ℓ ⊔ lsuc ℓ₁)
imp-∀ {ℓ₁ = ℓ₁} A P = (Q : Set ℓ₁) → (Qprop : is-prop Q) → (x : A) → (k : P x → Q) → Q

∀-≃-imp-∀ : (A : Set ℓ) → (P : A → Set ℓ₁) → (Pprop : (x : A) → is-prop (P x)) → ((x : A) → P x) ≃ imp-∀ A P
∀-≃-imp-∀ A P Pprop =
  iff-to-≃ (Π-prop _ Pprop)
    (Π-prop _ λ Q → Π-prop _ λ Qprop → Π-prop _ λ x → Π-prop _ λ k → Qprop)
    ((λ g Q Qprop x k → k (g x)) , λ h x → h (P x) (Pprop x) x id)
-- Q is a family over A at A's level: the backward map instantiates Q := λ y → mere-eq a y
imp-mere-eq : {A : Set ℓ} → (a x : A) → Set (lsuc ℓ)
imp-mere-eq {ℓ} {A} a x = (Q : A → Set ℓ) → (Qprop : (y : A) → is-prop (Q y)) → (qa : Q a) → Q x

mere-eq-≃-imp-mere-eq : {A : Set ℓ} → (a x : A) → mere-eq a x ≃ imp-mere-eq a x
mere-eq-≃-imp-mere-eq {A = A} a x =
  iff-to-≃ (prop-trunc-is-prop _)
    (Π-prop _ λ Q → Π-prop _ λ Qprop → Π-prop _ λ qa → Qprop x)
    ((λ t Q Qprop qa → rec-prop-trunc (Q x) (Qprop x) (λ p → tr Q p qa) t) ,
     λ h → h (mere-eq a) (λ y → prop-trunc-is-prop _) (mere-eq-is-rfl A a))

-- 14.9
postulate
  𝕀 : Set
  source target : 𝕀
  path : source ≡ target

  -- induction gives a section f with α, β, and a coherence γ filling the square
  --   tr P path (f source) ──ap (tr P path) α──▶ tr P path u
  --          │ apd f path                             │ p
  --          ▼                                        ▼
  --      f target ──────────────── β ─────────────▶   v
  ind-𝕀 : (P : 𝕀 → Set ℓ) → (u : P source) → (v : P target) → (p : tr P path u ≡ v)
    → Σ ((x : 𝕀) → P x) (λ f →
      Σ (f source ≡ u) (λ α →
      Σ (f target ≡ v) (λ β →
        concat (ap (tr P path) α) p ≡ concat (apd f path) β)))

ε : (P : 𝕀 → Set ℓ) → ((x : 𝕀) → P x) → Σ (P source) (λ u → Σ (P target) (λ v → tr P path u ≡ v))
ε P f = f source , (f target , apd f path)

-- the codomain of ε: values at the two endpoints, related over path
𝕀-data : (P : 𝕀 → Set ℓ) → Set ℓ
𝕀-data P = Σ (P source) (λ u → Σ (P target) (λ v → tr P path u ≡ v))

-- (a) identity types of 𝕀-data
Eq-𝕀-data : (P : 𝕀 → Set ℓ) → 𝕀-data P → 𝕀-data P → Set ℓ
Eq-𝕀-data P (u , (v , q)) (u' , (v' , q')) =
  Σ (u ≡ u') (λ α → Σ (v ≡ v') (λ β → concat q β ≡ concat (ap (tr P path) α) q'))

𝕀-data-eq : (P : 𝕀 → Set ℓ) → (s t : 𝕀-data P) → s ≡ t → Eq-𝕀-data P s t
𝕀-data-eq P (u , (v , q)) t refl = refl , (refl , concat (right-unit _) (inv (left-unit q)))

𝕀-data-eq-is-equiv : (P : 𝕀 → Set ℓ) → (s t : 𝕀-data P) → is-equiv (𝕀-data-eq P s t)
𝕀-data-eq-is-equiv P (u , (v , q)) t =
  total-contr-to-fam-equiv (refl , (refl , concat (right-unit _) (inv (left-unit q))))
    (𝕀-data-eq P (u , (v , q))) refl total-contr t
  where
    -- the fibre once the endpoints are paired with their paths
    D : Σ (P source) (λ u' → u ≡ u') → Σ (P target) (λ v' → v ≡ v') → Set _
    D (u' , α) (v' , β) = Σ (tr P path u' ≡ v') (λ q' → concat q β ≡ concat (ap (tr P path) α) q')

    -- regroup each endpoint next to its path
    e1 : Σ (𝕀-data P) (Eq-𝕀-data P (u , (v , q)))
       ≃ Σ (Σ (P source) (λ u' → u ≡ u')) (λ ua → Σ (Σ (P target) (λ v' → v ≡ v')) (λ vb → D ua vb))
    e1 = (λ { ((u' , (v' , q')) , (α , (β , γ))) → (u' , α) , ((v' , β) , (q' , γ)) }) ,
         (((λ { ((u' , α) , ((v' , β) , (q' , γ))) → (u' , (v' , q')) , (α , (β , γ)) }) ,
            λ { ((u' , α) , ((v' , β) , (q' , γ))) → refl }) ,
          ((λ { ((u' , α) , ((v' , β) , (q' , γ))) → (u' , (v' , q')) , (α , (β , γ)) }) ,
            λ { ((u' , (v' , q')) , (α , (β , γ))) → refl }))

    -- contract (u' , α) to (u , refl)
    e2 : Σ (Σ (P source) (λ u' → u ≡ u')) (λ ua → Σ (Σ (P target) (λ v' → v ≡ v')) (λ vb → D ua vb))
       ≃ Σ (Σ (P target) (λ v' → v ≡ v')) (λ vb → D (u , refl) vb)
    e2 = inv-≃ (_ , (is-equiv-pair-contr-base (Σ-≡-contractible u) _))

    -- contract (v' , β) to (v , refl)
    e3 : Σ (Σ (P target) (λ v' → v ≡ v')) (λ vb → D (u , refl) vb) ≃ D (u , refl) (v , refl)
    e3 = inv-≃ (_ , (is-equiv-pair-contr-base (Σ-≡-contractible v) _))

    -- remove the unit laws from the coherence
    e4 : D (u , refl) (v , refl) ≃ Σ (tr P path u ≡ v) (λ q' → q ≡ q')
    e4 = tot-≃ λ q' → _ ,
      equiv-comp (concat (inv (right-unit q))) (λ δ → concat δ (left-unit q'))
        (is-equiv-concat (inv (right-unit q))) (is-equiv-concat' (left-unit q'))

    total-contr : is-contr (Σ (𝕀-data P) (Eq-𝕀-data P (u , (v , q))))
    total-contr = is-contr-domain-equiv (proj₁ e) (Σ-≡-contractible q) (proj₂ e)
      where
        e = concat-≃ e1 (concat-≃ e2 (concat-≃ e3 e4))

𝕀-data-≡-equiv : (P : 𝕀 → Set ℓ) → (u u' : P source) → (v v' : P target)
  → (q : tr P path u ≡ v) → (q' : tr P path u' ≡ v')
  → ((u , (v , q)) ≡ (u' , (v' , q')))
  ≃ Σ (u ≡ u') (λ α → Σ (v ≡ v') (λ β → concat q β ≡ concat (ap (tr P path) α) q'))
𝕀-data-≡-equiv P u u' v v' q q' = 𝕀-data-eq P _ _ , 𝕀-data-eq-is-equiv P _ _

-- (c)
𝕀-contractible : is-contr 𝕀
𝕀-contractible =
  source , proj₁ (ind-𝕀 (λ z → z ≡ source) refl (inv path)
    (concat (tr-fib id path refl) (concat (right-unit _) (ap inv (ap-id path)))))

-- (b) the dependent universal property of 𝕀
𝕀-dep-up : (P : 𝕀 → Set ℓ) → is-equiv (ε P)
𝕀-dep-up P =
  3-for-2-f-g-to-h (λ f → f source) proj₁ (ε P) (λ f → refl)
    (proj₂ (contr-to-dep-up 𝕀-contractible) P)
    (fib-contr-to-proj₁-equiv λ u → Σ-≡-contractible (tr P path u))
