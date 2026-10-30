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

-- Definition 14.2.2, with the formation rule and constructors
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

-- ∥ f ∥ extends η ∘ f along η
map-prop-trunc-η : {A B : Set} → (f : A → B) → (map-prop-trunc f ∘ η) ∼ (η ∘ f)
map-prop-trunc-η f a = α _ _

map-prop-trunc-id : {A : Set} → map-prop-trunc (id {A}) ∼ id
map-prop-trunc-id x = α _ _

map-prop-trunc-comp : {A B C : Set} → (f : A → B) → (g : B → C)
  → map-prop-trunc (g ∘ f) ∼ (map-prop-trunc g ∘ map-prop-trunc f)
map-prop-trunc-comp f g x = α _ _

-- 14.3 Logic in type theory

-- Definition 14.3.1
infixr 1 _∨_
_∨_ : (P Q : Set) → Set
P ∨ Q = ∥ P ⊎ Q ∥

-- Proposition 14.3.2
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

-- Definition 14.3.3
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

-- 14.4 Mapping propositional truncations into sets

-- Example 14.4.1
is-lower-bound-propℕ : (P : ℕ → Set) → (n : ℕ) → is-prop (is-lower-bound P n)
is-lower-bound-propℕ P n = Π-prop _ λ x → →-prop (P x) (n ≤ℕ x) (≤-propℕ n x)

least-element-propℕ : (P : ℕ → Set) → is-subtype ℕ P → is-prop (Σ ℕ (λ m → P m × is-lower-bound P m))
least-element-propℕ P Psubtype = is-prop'-to-is-prop λ {(n , (pn , ln)) (m , (pm , lm)) → eq-pair _ _ (≤-antisymℕ n m (ln m pm) (lm n pn) , proj₁ (prop-× (Psubtype m) (is-lower-bound-propℕ P m) _ _))}

∃-to-Σ-decidableℕ : (P : ℕ → Set) → is-subtype ℕ P → ((n : ℕ) → is-decidable (P n)) → ∃ ℕ P → Σ ℕ P
∃-to-Σ-decidableℕ P Psubtype Pdec t = proj₁ lbP , proj₁ (proj₂ (lbP))
    where
    lbP : Σ ℕ (λ m → P m × is-lower-bound P m)
    lbP = rec-prop-trunc (Σ ℕ (λ m → P m × is-lower-bound P m)) (least-element-propℕ P Psubtype) (ℕ-well-ordered P Pdec) t

-- corollary of Example 14.4.1 for Fin k
Fin-decidable-Σ : (k : ℕ) → (P : Fin k → Set) → ((x : Fin k) → is-decidable (P x)) → is-decidable (Σ (Fin k) P)
Fin-decidable-Σ 0ℕ P Pdec = inr λ { (() , _) }
Fin-decidable-Σ (succℕ k) P Pdec with Fin-decidable-Σ k (λ x → P (inl x)) (λ x → Pdec (inl x))
... | inl (x , px) = inl (inl x , px)
... | inr nΣ with Pdec (inr *)
...   | inl p = inl (inr * , p)
...   | inr np = inr λ { (inl x , px) → nΣ (x , px) ; (inr * , px) → np px }

∃-to-Σ-decidableFin : (k : ℕ) → (P : Fin k → Set) → ((x : Fin k) → is-decidable (P x)) → ∃ (Fin k) P → Σ (Fin k) P
∃-to-Σ-decidableFin k P Pdec t with Fin-decidable-Σ k P Pdec
... | inl w = w
... | inr nw = ex-falso (elim∃ P empty-prop (λ x p → nw (x , p)) t)

-- Remark 14.4.2
has-global-choice : (A : Set) → Set
has-global-choice A = ∥ A ∥ → A

-- Definition 14.4.3
is-weakly-constant : {A B : Set} → (f : A → B) → Set
is-weakly-constant {A} f = (x y : A) → f x ≡ f y

-- Remark 14.4.4
is-constant : {A B : Set} → (f : A → B) → Set
is-constant {A} {B} f = Σ B (λ b → f ∼ const {A} {B} {b})

constant-to-weakly-constant : {A B : Set} → (f : A → B) → is-constant f → is-weakly-constant f
constant-to-weakly-constant f fconst x y = concat (proj₂ (fconst) x) (inv (proj₂ (fconst) y))

contr-iff-id-constant : (A : Set) → is-contr A ↔ is-constant (id {A})
contr-iff-id-constant A = (λ {(a , eqa) → a , λ x → eqa x}) , λ {(a , idhc) → a , idhc}

prop-iff-id-weakly-constant : (A : Set) → is-prop A ↔ is-weakly-constant (id {A})
prop-iff-id-weakly-constant A = (λ {Aprop x y → proj₁ (Aprop x y) }) , λ Awc → is-prop'-to-is-prop Awc

-- Lemma 14.4.5
comm-tri-η-to-weakly-constant-f : {A B : Set} → (f : A → B) → (g : ∥ A ∥ → B) → triangle-commutes f η g → is-weakly-constant f
comm-tri-η-to-weakly-constant-f {A} {B} f g H x y = concat (H x) (concat (ap g (α _ _)) (inv (H y)))

-- Theorem 14.4.6 (Kraus)
-- the map g ↦ (g ∘ η , λ x y → ap g (α (η x) (η y)))
prop-trunc-to-weakly-constant : {A B : Set} → (∥ A ∥ → B) → Σ (A → B) is-weakly-constant
prop-trunc-to-weakly-constant g = (g ∘ η) , λ x y → ap g (α (η x) (η y))

-- proof, step 1: f extends in at most one way
set-ext-along-η-unique : {A B : Set} → is-set B → (f : A → B) → (g h : ∥ A ∥ → B)
  → triangle-commutes f η g → triangle-commutes f η h → g ∼ h
set-ext-along-η-unique {A} {B} Bset f g h G H = ind-prop-trunc-prop (λ t → g t ≡ h t) (λ t → Bset (g t) (h t)) (λ a → concat (inv (G a)) (H a)) 

-- proof, step 2: Σ (b : B) ∥ fib f b ∥ is a proposition
weakly-constant-image-prop : {A B : Set} → is-set B → (f : A → B) → is-weakly-constant f
  → is-prop (Σ B (λ b → ∥ fib f b ∥))
weakly-constant-image-prop Bset f H = is-prop'-to-is-prop λ {(b , s) (b' , s') → eq-pair _ _ (elim∃ (λ x → f x ≡ b) (Bset b b') (λ x p → elim∃ (λ x → f x ≡ b') (Bset b b') (λ x' p' → concat (inv p) (concat (H x x') p')) s') s , α _ _)}

-- is-weakly-constant f is a proposition when the codomain is a set
weakly-constant-prop : {A B : Set} → is-set B → (f : A → B) → is-prop (is-weakly-constant f)
weakly-constant-prop Bset f = Π-prop _ λ x → Π-prop _ λ y → Bset (f x) (f y)

-- proof, step 3: a weakly constant map into a set extends along η
weakly-constant-ext : {A B : Set} → is-set B → (f : A → B) → is-weakly-constant f → ∥ A ∥ → B
weakly-constant-ext {A} {B} Bset f H = proj₁ ∘ rec-prop-trunc (Σ B (λ b → ∥ fib f b ∥)) (weakly-constant-image-prop Bset f H) (λ x → f x , η (x , refl))

weakly-constant-ext-η : {A B : Set} → (Bset : is-set B) → (f : A → B) → (H : is-weakly-constant f)
  → (a : A) → weakly-constant-ext Bset f H (η a) ≡ f a
weakly-constant-ext-η Bset f H a = ap proj₁ (proj₁ (weakly-constant-image-prop Bset f H (rec-prop-trunc _ (weakly-constant-image-prop Bset f H) (λ x → f x , η (x , refl)) (η a)) (f a , η (a , refl))))

prop-trunc-set-up : (A : Set) → {B : Set} → is-set B → is-equiv (prop-trunc-to-weakly-constant {A} {B})
prop-trunc-set-up A {B} Bset = (ψ , φψ) , (ψ , ψφ)
    where
        ψ : Σ (A → B) is-weakly-constant → ∥ A ∥ → B
        ψ (f , H) = weakly-constant-ext Bset f H
        φψ : prop-trunc-to-weakly-constant ∘ ψ ∼ id
        φψ (f , H) = eq-pair _ _ (eq-htpy _ _ (weakly-constant-ext-η Bset f H) , proj₁ (weakly-constant-prop Bset f _ _))
        ψφ : ψ ∘ prop-trunc-to-weakly-constant ∼ id
        ψφ g = eq-htpy _ _ (set-ext-along-η-unique Bset (g ∘ η) (ψ (prop-trunc-to-weakly-constant g)) g (λ a → inv (weakly-constant-ext-η Bset (g ∘ η) _ a)) (λ a → refl))

