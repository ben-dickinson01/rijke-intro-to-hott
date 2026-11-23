{-# OPTIONS --without-K #-}
module ch16 where

open import ch15 public

-- 16.1 Counting in type theory

-- Definition 16.1.1
count : (A : Set ℓ) → Set _
count A = Σ ℕ (λ k → Fin k ≃ A)

-- Example 16.1.2
count-Fin : (k : ℕ) → count (Fin k)
count-Fin k = k , (id , is-equiv-id (Fin k))

count-equiv : {A : Set ℓ} {B : Set ℓ₁} → A ≃ B → count A → count B
count-equiv e (k , f) = k , concat-≃ f e

-- Example 16.1.3
count-zero-iff-empty : {A : Set ℓ} → (c : count A) → (proj₁ c ≡ 0ℕ) ↔ ¬ A
count-zero-iff-empty (k , (f , (_ , (r , _)))) =
  (λ { refl a → r a }) , λ na → empty-Fin-zero k (λ x → na (f x))
  where
    empty-Fin-zero : (n : ℕ) → ¬ (Fin n) → n ≡ 0ℕ
    empty-Fin-zero 0ℕ _ = refl
    empty-Fin-zero (succℕ n) ne = ex-falso (ne (inr *))

-- Example 16.1.4
count-1-to-contr : (A : Set ℓ) → (c : count A) → proj₁ c ≡ 1ℕ → is-contr A
count-1-to-contr A (.1ℕ , f) refl =
  is-contr-codomain-equiv (proj₁ f)
    (inr * , λ { (inl ()) ; (inr *) → refl }) (proj₂ f)

contr-to-count-1 : (A : Set ℓ) → (c : count A) → is-contr A → proj₁ c ≡ 1ℕ
contr-to-count-1 A (0ℕ , f) (a , xeqa) = ex-falso (proj₁ (proj₁ (proj₂ f)) a)
contr-to-count-1 A (succℕ 0ℕ , f) (a , xeqa) = refl
contr-to-count-1 A (succℕ (succℕ n) , e) (a , xeqa) =
  ex-falso (Fin-2+-not-contr n
    (is-contr-domain-equiv (proj₁ e) (a , xeqa) (proj₂ e)))

is-contr-to-count : {A : Set ℓ} → is-contr A → count A
is-contr-to-count (a , xeqa) =
  1ℕ , concat-≃ (𝟘-⊎ 𝟙)
    (inv-≃ ((λ x → *) ,
            (((λ u → a) , λ {* → refl}) ,
             ((λ z → a) , λ y → inv (xeqa y)))))

-- Example 16.1.5
empty-to-𝟘-equiv : {A : Set ℓ} → is-empty A → A ≃ 𝟘
empty-to-𝟘-equiv na = na , ((ex-falso , λ ()) , ((λ ()) , λ x → ex-falso (na x)))

prop-dec-to-count : (A : Set ℓ) → is-prop A → is-decidable A → count A
prop-dec-to-count A Aprop (inl a) = is-contr-to-count (a , λ x → proj₁ (Aprop x a))
prop-dec-to-count A Aprop (inr na) = 0ℕ , inv-≃ (empty-to-𝟘-equiv na)

prop-count-to-dec : (A : Set ℓ) → is-prop A → count A → is-decidable A
prop-count-to-dec A Aprop (0ℕ , e) =
  inr (proj₁ (count-zero-iff-empty (0ℕ , e)) refl)
prop-count-to-dec A Aprop (succℕ k , e) = inl ((proj₁ e) (inr *))

-- Remark 16.1.6
count-to-dec-eq : {A : Set ℓ} → count A → has-decidable-eq A
count-to-dec-eq (0ℕ , e) x y =
  inr λ p → (proj₁ (count-zero-iff-empty (0ℕ , e)) refl) x
count-to-dec-eq (succℕ k , (f , ((g , fg) , (h , hf)))) x y
  with Fin-decidable-eq (succℕ k) (g x) (g y)
... | inl p = inl (concat (inv (fg x)) (concat (ap f p) (fg y)))
... | inr np = inr λ q → np (ap g q)

-- Theorem 16.1.7 (i), forward direction
count-to-⊎-count : {A : Set ℓ₁} → {B : Set ℓ₂} → count A → count B → count (A ⊎ B)
count-to-⊎-count (k , e) (l , e') =
  (k +ℕ l) ,
  concat-≃ (Fin-add-equiv-⊎ k l)
    (concat-≃ (⊎-equiv-left e) (⊎-equiv-right e'))

-- Theorem 16.1.7 (ii), forward direction
-- (helper: reindexing a Σ-type along an equivalence of the base)
Σ-equiv-base : {A : Set ℓ} {A' : Set ℓ₁} → (B : A' → Set ℓ₂) → (e : A ≃ A')
  → Σ A (λ x → B (proj₁ e x)) ≃ Σ A' B
Σ-equiv-base B e =
  base-change (proj₁ e) B , f-equiv-to-base-change-equiv (proj₁ e) B (proj₂ e)

Σ-Fin-count : (k : ℕ) → (C : Fin k → Set ℓ) → ((i : Fin k) → count (C i))
  → count (Σ (Fin k) C)
Σ-Fin-count 0ℕ C cC = 0ℕ , inv-≃ (empty-to-𝟘-equiv λ x → proj₁ x)
Σ-Fin-count (succℕ k) C cC =
  count-equiv (inv-≃ (Σ-⊎-distrib C))
    (count-to-⊎-count
      (Σ-Fin-count k (λ a → C (inl a)) (λ i → cC (inl i)))
      (count-equiv (inv-≃ (Σ-𝟙 (λ b → C (inr b)))) (cC (inr *))))

count-to-Σ-count : {A : Set ℓ} → (B : A → Set ℓ₁) → count A
  → ((x : A) → count (B x)) → count (Σ A B)
count-to-Σ-count B (0ℕ , e) cB =
  0ℕ , inv-≃ (empty-to-𝟘-equiv λ {(a , b) → proj₁ (proj₁ (proj₂ e)) a})
count-to-Σ-count B (succℕ k , e) cB =
  count-equiv (Σ-equiv-base B e)
    (Σ-Fin-count (succℕ k) (λ x → B (proj₁ e x)) λ i → cB (proj₁ e i))

-- Theorem 16.1.7 (i), reverse direction
⊎-count-to-count : {A : Set ℓ₁} → {B : Set ℓ₂} → count (A ⊎ B)
  → count A × count B
⊎-count-to-count {A = A} {B = B} (k , e) =
  count-equiv P-equiv-A (count-to-Σ-count P (k , e) count-P) ,
  count-equiv Q-equiv-B (count-to-Σ-count Q (k , e) count-Q)
  where
    P : A ⊎ B → Set _
    P (inl _) = 𝟙
    P (inr _) = 𝟘

    count-P : (z : A ⊎ B) → count (P z)
    count-P (inl a) = is-contr-to-count (* , λ {* → refl})
    count-P (inr b) = 0ℕ , inv-≃ (empty-to-𝟘-equiv λ ())

    P-equiv-A : Σ (A ⊎ B) P ≃ A
    P-equiv-A =
      concat-≃ (Σ-⊎-distrib P)
        (concat-≃ (⊎-equiv-left (Σ-A-𝟙 A))
          (concat-≃ (⊎-equiv-right (Σ-A-𝟘 B)) (⊎-𝟘 A)))

    Q : A ⊎ B → Set _
    Q (inl _) = 𝟘
    Q (inr _) = 𝟙

    count-Q : (z : A ⊎ B) → count (Q z)
    count-Q (inl a) = 0ℕ , inv-≃ (empty-to-𝟘-equiv λ ())
    count-Q (inr b) = is-contr-to-count (* , λ {* → refl})

    Q-equiv-B : Σ (A ⊎ B) Q ≃ B
    Q-equiv-B =
      concat-≃ (Σ-⊎-distrib Q)
        (concat-≃ (⊎-equiv-right (Σ-A-𝟙 B))
          (concat-≃ (⊎-equiv-left (Σ-A-𝟘 A)) (𝟘-⊎ B)))

-- Theorem 16.1.7 (ii), converse direction
Σ-count-to-fib-count : {A : Set ℓ} → (B : A → Set ℓ₁) → count A
  → count (Σ A B) → (x : A) → count (B x)
Σ-count-to-fib-count {A = A} B (k , eA) (l , eAB) a =
  count-equiv (inv-≃ (proj₁ (fib-repl i)))
    (count-to-Σ-count (fib i) (l , eAB) count-fib)
  where
    i : B a → Σ A B
    i b = a , b

    fib-i-equiv : (w : Σ A B) → fib i w ≃ (a ≡ proj₁ w)
    fib-i-equiv (x , b) =
      concat-≃
        (tot-≃ λ b' → (pair-eq (i b') (x , b)) , pair-eq-is-equiv (i b') (x , b))
        (Σ-swap-drop-contr (λ z α₁ → tr B α₁ (proj₂ (i z)) ≡ b)
          λ q → equiv-to-contr-map (λ z → tr B q (proj₂ (i z))) (is-equiv-tr q) b)

    count-a≡ : (x : A) → count (a ≡ x)
    count-a≡ x =
      prop-dec-to-count (a ≡ x)
        (Hedberg (count-to-dec-eq (k , eA)) a x)
        (count-to-dec-eq (k , eA) a x)

    count-fib : (w : Σ A B) → count (fib i w)
    count-fib w = count-equiv (inv-≃ (fib-i-equiv w)) (count-a≡ (proj₁ w))

-- Theorem 16.1.7 (ii), section claim
Σ-section-count-to-count : {A : Set ℓ} → (B : A → Set ℓ₁) → ((x : A) → B x)
  → ((x : A) → count (B x)) → count (Σ A B) → count A
Σ-section-count-to-count {A = A} B b cB cΣ =
  count-equiv (inv-≃ (proj₁ (fib-repl g)))
    (count-to-Σ-count (fib g) cΣ count-fib)
  where
    g : A → Σ A B
    g a = a , b a

    fib-g-equiv : (w : Σ A B) → fib g w ≃ (b (proj₁ w) ≡ proj₂ w)
    fib-g-equiv (x , y) =
      concat-≃
        (tot-≃ λ a → (pair-eq (g a) (x , y)) , pair-eq-is-equiv (g a) (x , y))
        (concat-≃
          (inv-≃ (Σ-assoc (λ z → z ≡ x)
                          λ w → tr B (proj₂ w) (b (proj₁ w)) ≡ y))
          (inv-≃ (_ , is-equiv-pair-contr-base (identity-contr x)
                        (λ w → tr B (proj₂ w) (b (proj₁ w)) ≡ y))))

    count-b≡ : (w : Σ A B) → count (b (proj₁ w) ≡ proj₂ w)
    count-b≡ w =
      prop-dec-to-count (b (proj₁ w) ≡ proj₂ w)
        (Hedberg (count-to-dec-eq (cB (proj₁ w))) (b (proj₁ w)) (proj₂ w))
        (count-to-dec-eq (cB (proj₁ w)) (b (proj₁ w)) (proj₂ w))

    count-fib : (w : Σ A B) → count (fib g w)
    count-fib w = count-equiv (inv-≃ (fib-g-equiv w)) (count-b≡ w)

-- Theorem 16.1.7, counting subtypes
subtype-count-to-decidable : {A : Set ℓ} → (P : A → Set ℓ₁)
  → ((x : A) → is-prop (P x)) → count A → count (Σ A P)
  → (x : A) → is-decidable (P x)
subtype-count-to-decidable P Pprop (k , eA) (l , eAP) a =
  prop-count-to-dec (P a) (Pprop a)
    (Σ-count-to-fib-count P (k , eA) (l , eAP) a)

subtype-decidable-to-count : {A : Set ℓ} → (P : A → Set ℓ₁)
  → ((x : A) → is-prop (P x)) → count A → ((x : A) → is-decidable (P x))
  → count (Σ A P)
subtype-decidable-to-count P Pprop cA d =
  count-to-Σ-count P cA λ a → prop-dec-to-count (P a) (Pprop a) (d a)

subtype-count-iff-decidable : {A : Set ℓ} → (P : A → Set ℓ₁)
  → ((x : A) → is-prop (P x)) → count A
  → count (Σ A P) ↔ ((x : A) → is-decidable (P x))
subtype-count-iff-decidable P Pprop cA =
  subtype-count-to-decidable P Pprop cA , subtype-decidable-to-count P Pprop cA

-- Corollary 16.1.8
count-to-×-count : {A : Set ℓ} {B : Set ℓ₁} → count A → count B → count (A × B)
count-to-×-count {B = B} cA cB = count-to-Σ-count (λ _ → B) cA (λ _ → cB)

-- The book's proof of (ii) does not supply the decidability and propositionality
-- of the subtype below; both are obtained from the counting of A × B at the
-- point (x , y) in hand.
×-count-to-count-left : {A : Set ℓ} {B : Set ℓ₁} → count (A × B) → B → count A
×-count-to-count-left {A = A} {B = B} c b =
  count-equiv P-equiv-A (subtype-decidable-to-count P P-prop c P-dec)
  where
    P : A × B → Set _
    P w = proj₂ w ≡ b

    dec-eq-B : A → has-decidable-eq B
    dec-eq-B x y y' =
      proj₁ (iff-to-iff-decidable
              ((λ p → ap proj₂ p) , (λ p → ap (λ z → x , z) p)))
            (count-to-dec-eq c (x , y) (x , y'))

    P-dec : (w : A × B) → is-decidable (P w)
    P-dec (x , y) = dec-eq-B x y b

    P-prop : (w : A × B) → is-prop (P w)
    P-prop (x , y) = Hedberg (dec-eq-B x) y b

    P-equiv-A : Σ (A × B) P ≃ A
    P-equiv-A =
      concat-≃ (Σ-assoc (λ _ → B) (λ w → proj₂ w ≡ b))
        (proj₁ , fib-contr-to-proj₁-equiv (λ x → identity-contr b))

×-count-to-count-right : {A : Set ℓ} {B : Set ℓ₁} → count (A × B) → A → count B
×-count-to-count-right {A = A} {B = B} c a =
  count-equiv Q-equiv-B (subtype-decidable-to-count Q Q-prop c Q-dec)
  where
    Q : A × B → Set _
    Q w = proj₁ w ≡ a

    dec-eq-A : B → has-decidable-eq A
    dec-eq-A y x x' =
      proj₁ (iff-to-iff-decidable
              ((λ p → ap proj₁ p) , (λ p → ap (λ z → z , y) p)))
            (count-to-dec-eq c (x , y) (x' , y))

    Q-dec : (w : A × B) → is-decidable (Q w)
    Q-dec (x , y) = dec-eq-A y x a

    Q-prop : (w : A × B) → is-prop (Q w)
    Q-prop (x , y) = Hedberg (dec-eq-A y) x a

    Q-equiv-B : Σ (A × B) Q ≃ B
    Q-equiv-B =
      concat-≃ (Σ-assoc (λ _ → B) (λ w → proj₁ w ≡ a))
        (concat-≃ (Σ-swap (λ x y → x ≡ a))
          (proj₁ , fib-contr-to-proj₁-equiv (λ y → identity-contr a)))


-- 16.2 Double counting in type theory
-- Proposition 16.2.1
-- (i)
star-value : {X : Set ℓ} {Y : Set ℓ₁} → (e : (X ⊎ 𝟙) → (Y ⊎ 𝟙)) → is-equiv e
  → (x : X) → e (inl x) ≡ inr * → Σ Y (λ y → inl y ≡ e (inr *))
star-value {X = X} {Y = Y} e eequiv x p = go (e (inr *)) refl
  where
    go : (z : Y ⊎ 𝟙) → e (inr *) ≡ z → Σ Y (λ y → inl y ≡ e (inr *))
    go (inl y) q = y , inv q
    go (inr *) q =
      ex-falso (inl-ne-inr x *
        (is-equiv-to-injective e eequiv (concat p (inv q))))

-- (ii)
map-⊎-𝟙-aux : {X : Set ℓ} {Y : Set ℓ₁} → (e : (X ⊎ 𝟙) → (Y ⊎ 𝟙)) → is-equiv e
  → (x : X) → (u : Y ⊎ 𝟙) → e (inl x) ≡ u → Y
map-⊎-𝟙-aux e eequiv x (inl y) p = y
map-⊎-𝟙-aux e eequiv x (inr *) p = proj₁ (star-value e eequiv x p)

map-⊎-𝟙 : {X : Set ℓ} {Y : Set ℓ₁} → (e : (X ⊎ 𝟙) → (Y ⊎ 𝟙)) → is-equiv e → X → Y
map-⊎-𝟙 e eequiv x = map-⊎-𝟙-aux e eequiv x (e (inl x)) refl

map-⊎-𝟙-aux-inl : {X : Set ℓ} {Y : Set ℓ₁} → (e : (X ⊎ 𝟙) → (Y ⊎ 𝟙))
  → (eequiv : is-equiv e) → (x : X) → (u : Y ⊎ 𝟙) → (q : e (inl x) ≡ u) → (y : Y)
  → u ≡ inl y
  → map-⊎-𝟙-aux e eequiv x u q ≡ y
map-⊎-𝟙-aux-inl e eequiv x (inl y) q .y refl = refl

map-⊎-𝟙-aux-inr : {X : Set ℓ} {Y : Set ℓ₁} → (e : (X ⊎ 𝟙) → (Y ⊎ 𝟙))
  → (eequiv : is-equiv e) → (x : X) → (u : Y ⊎ 𝟙) → (q : e (inl x) ≡ u) → (r : u ≡ inr *)
  → map-⊎-𝟙-aux e eequiv x u q ≡ proj₁ (star-value e eequiv x (concat q r))
map-⊎-𝟙-aux-inr e eequiv x (inr *) q refl =
  ap (λ s → proj₁ (star-value e eequiv x s)) (inv (right-unit _))

map-⊎-𝟙-inl : {X : Set ℓ} {Y : Set ℓ₁} → (e : (X ⊎ 𝟙) → (Y ⊎ 𝟙))
  → (eequiv : is-equiv e) → (x : X) → (y : Y) → e (inl x) ≡ inl y → map-⊎-𝟙 e eequiv x ≡ y
map-⊎-𝟙-inl e eequiv x y p = map-⊎-𝟙-aux-inl e eequiv x (e (inl x)) refl y p

map-⊎-𝟙-inr : {X : Set ℓ} {Y : Set ℓ₁} → (e : (X ⊎ 𝟙) → (Y ⊎ 𝟙))
  → (eequiv : is-equiv e) → (x : X) → (p : e (inl x) ≡ inr *)
  → map-⊎-𝟙 e eequiv x ≡ proj₁ (star-value e eequiv x p)
map-⊎-𝟙-inr e eequiv x p =
  concat (map-⊎-𝟙-aux-inr e eequiv x (e (inl x)) refl p)
    (ap (λ s → proj₁ (star-value e eequiv x s)) (left-unit _))

-- (iii) g := map-⊎-𝟙 applied to the inverse equivalence; δ and ε are the instances
-- map-⊎-𝟙-inl and map-⊎-𝟙-inr at inv-≃ e.

-- (iv)
section-⊎-𝟙 : {X : Set ℓ} {Y : Set ℓ₁} → (e : (X ⊎ 𝟙) ≃ (Y ⊎ 𝟙)) → (y : Y)
  → map-⊎-𝟙 (proj₁ e) (proj₂ e) (map-⊎-𝟙 (proj₁ (inv-≃ e)) (proj₂ (inv-≃ e)) y) ≡ y
section-⊎-𝟙 {X = X} {Y = Y} e@(f , ((g , fg) , (h , hf))) y = go (g (inl y)) refl
  where
    ef = proj₂ e
    eg = proj₂ (inv-≃ e)

    go : (z : X ⊎ 𝟙) → g (inl y) ≡ z
      → map-⊎-𝟙 f ef (map-⊎-𝟙 g eg y) ≡ y
    go (inl x) p =
      map-⊎-𝟙-inl f ef (map-⊎-𝟙 g eg y) y
        (concat (ap (λ t → f (inl t)) (map-⊎-𝟙-inl g eg y x p))
                (concat (ap f (inv p)) (fg (inl y))))
    go (inr *) p =
      ap (λ { (inl a) → a ; (inr _) → y })
         (concat (ap inl (map-⊎-𝟙-inr f ef (map-⊎-𝟙 g eg y) q))
                 (concat (proj₂ (star-value f ef (map-⊎-𝟙 g eg y) q))
                         (concat (ap f (inv p)) (fg (inl y)))))
      where
        q : f (inl (map-⊎-𝟙 g eg y)) ≡ inr *
        q = concat (ap (λ t → f (inl t)) (map-⊎-𝟙-inr g eg y p))
              (concat (ap f (proj₂ (star-value g eg y p))) (fg (inr *)))

retraction-⊎-𝟙 : {X : Set ℓ} {Y : Set ℓ₁} → (e : (X ⊎ 𝟙) ≃ (Y ⊎ 𝟙)) → (x : X)
  → map-⊎-𝟙 (proj₁ (inv-≃ e)) (proj₂ (inv-≃ e)) (map-⊎-𝟙 (proj₁ e) (proj₂ e) x) ≡ x
retraction-⊎-𝟙 {X = X} {Y = Y} e@(f , ((g , fg) , (h , hf))) x = go (f (inl x)) refl
  where
    ef = proj₂ e
    eg = proj₂ (inv-≃ e)

    -- g (f u) ≡ u
    gf : (u : X ⊎ 𝟙) → g (f u) ≡ u
    gf = proj₂ (proj₂ (equiv-to-inverse f ef))

    go : (z : Y ⊎ 𝟙) → f (inl x) ≡ z
      → map-⊎-𝟙 g eg (map-⊎-𝟙 f ef x) ≡ x
    go (inl y) p =
      concat (ap (map-⊎-𝟙 g eg) (map-⊎-𝟙-inl f ef x y p))
        (map-⊎-𝟙-inl g eg y x (concat (ap g (inv p)) (gf (inl x))))
    go (inr *) p =
      ap (λ { (inl a) → a ; (inr _) → x })
         (concat (ap inl (map-⊎-𝟙-inr g eg (map-⊎-𝟙 f ef x) q))
                 (concat (proj₂ (star-value g eg (map-⊎-𝟙 f ef x) q))
                         (concat (ap g (inv p)) (gf (inl x)))))
      where
        q : g (inl (map-⊎-𝟙 f ef x)) ≡ inr *
        q = concat (ap (λ t → g (inl t)) (map-⊎-𝟙-inr f ef x p))
              (concat (ap g (proj₂ (star-value f ef x p))) (gf (inr *)))

⊎-𝟙-equiv-to-equiv : {X : Set ℓ} {Y : Set ℓ₁} → (X ⊎ 𝟙) ≃ (Y ⊎ 𝟙) → X ≃ Y
⊎-𝟙-equiv-to-equiv {X = X} {Y = Y} e =
  map-⊎-𝟙 (proj₁ e) (proj₂ e) ,
  ((map-⊎-𝟙 (proj₁ (inv-≃ e)) (proj₂ (inv-≃ e)) , section-⊎-𝟙 e) ,
   (map-⊎-𝟙 (proj₁ (inv-≃ e)) (proj₂ (inv-≃ e)) , retraction-⊎-𝟙 e))

Fin-equiv-to-same-ℕ : (k l : ℕ) → Fin k ≃ Fin l → k ≡ l
Fin-equiv-to-same-ℕ 0ℕ 0ℕ (e , eequiv) = refl
Fin-equiv-to-same-ℕ 0ℕ (succℕ l) (e , eequiv) = ex-falso ((proj₁ (proj₂ eequiv)) (inr *))
Fin-equiv-to-same-ℕ (succℕ k) 0ℕ (e , eequiv) = ex-falso (e (inr *))
Fin-equiv-to-same-ℕ (succℕ k) (succℕ l) (e , eequiv) = ap succℕ (Fin-equiv-to-same-ℕ k l (⊎-𝟙-equiv-to-equiv (e , eequiv)))

