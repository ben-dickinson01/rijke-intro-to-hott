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
star-value {X = X} {Y = Y} e eequiv x p = star-cases (e (inr *)) refl
  where
    star-cases : (z : Y ⊎ 𝟙) → e (inr *) ≡ z → Σ Y (λ y → inl y ≡ e (inr *))
    star-cases (inl y) q = y , inv q
    star-cases (inr *) q =
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
section-⊎-𝟙 {X = X} {Y = Y} e@(f , ((g , fg) , (h , hf))) y = section-cases (g (inl y)) refl
  where
    ef = proj₂ e
    eg = proj₂ (inv-≃ e)

    section-cases : (z : X ⊎ 𝟙) → g (inl y) ≡ z
      → map-⊎-𝟙 f ef (map-⊎-𝟙 g eg y) ≡ y
    section-cases (inl x) p =
      map-⊎-𝟙-inl f ef (map-⊎-𝟙 g eg y) y
        (concat (ap (λ t → f (inl t)) (map-⊎-𝟙-inl g eg y x p))
                (concat (ap f (inv p)) (fg (inl y))))
    section-cases (inr *) p =
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
retraction-⊎-𝟙 {X = X} {Y = Y} e@(f , ((g , fg) , (h , hf))) x = retraction-cases (f (inl x)) refl
  where
    ef = proj₂ e
    eg = proj₂ (inv-≃ e)

    -- g (f u) ≡ u
    gf : (u : X ⊎ 𝟙) → g (f u) ≡ u
    gf = proj₂ (proj₂ (equiv-to-inverse f ef))

    retraction-cases : (z : Y ⊎ 𝟙) → f (inl x) ≡ z
      → map-⊎-𝟙 g eg (map-⊎-𝟙 f ef x) ≡ x
    retraction-cases (inl y) p =
      concat (ap (map-⊎-𝟙 g eg) (map-⊎-𝟙-inl f ef x y p))
        (map-⊎-𝟙-inl g eg y x (concat (ap g (inv p)) (gf (inl x))))
    retraction-cases (inr *) p =
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

-- Theorem 16.2.2
Fin-equiv-to-same-ℕ : (k l : ℕ) → Fin k ≃ Fin l → k ≡ l
Fin-equiv-to-same-ℕ 0ℕ 0ℕ (e , eequiv) = refl
Fin-equiv-to-same-ℕ 0ℕ (succℕ l) (e , eequiv) =
  ex-falso ((proj₁ (proj₂ eequiv)) (inr *))
Fin-equiv-to-same-ℕ (succℕ k) 0ℕ (e , eequiv) = ex-falso (e (inr *))
Fin-equiv-to-same-ℕ (succℕ k) (succℕ l) (e , eequiv) =
  ap succℕ (Fin-equiv-to-same-ℕ k l (⊎-𝟙-equiv-to-equiv (e , eequiv)))

-- 16.3 Finite types

-- Definition 16.3.1
is-finite : (X : Set ℓ) → Set _
is-finite X = ∥ count X ∥

𝔽 : Set _
𝔽 = Σ Set is-finite

BS : (k : ℕ) → Set _
BS k = Σ Set (λ X → ∥ Fin k ≃ X ∥)

-- Remark 16.3.2
count-to-finite : (X : Set ℓ) → count X → is-finite X
count-to-finite X cX = η cX

equiv-finite-to-finite : {X : Set ℓ} {Y : Set ℓ₁} → X ≃ Y → is-finite Y → is-finite X
equiv-finite-to-finite e Yfin = map-prop-trunc (count-equiv (inv-≃ e)) Yfin

is-decidable-is-prop : {A : Set ℓ} → is-prop A → is-prop (is-decidable A)
is-decidable-is-prop {A = A} Aprop = to-neg-to-prop-⊎ Aprop (¬-prop A) λ z z₁ → z₁ z

finite-to-set : {X : Set ℓ} → is-finite X → is-set X
finite-to-set {X = X} Xfin =
  rec-prop-trunc (is-set X)
    (Π-prop _ (λ x → Π-prop _ λ y → trunc-is-prop (x ≡ y)))
    (λ c → Hedberg (count-to-dec-eq c)) Xfin

finite-to-dec-eq : {X : Set ℓ} → is-finite X → has-decidable-eq X
finite-to-dec-eq {X = X} Xfin =
  rec-prop-trunc (has-decidable-eq X)
    (Π-prop _ (λ x → Π-prop _ λ y →
      is-decidable-is-prop (finite-to-set Xfin x y)))
    count-to-dec-eq Xfin

-- Theorem 16.3.3
-- (helper: the number k is determined by a merely-existing equivalence)
trunc-Fin-equiv-to-same-ℕ : {X : Set ℓ} → (k l : ℕ)
  → ∥ Fin k ≃ X ∥ → ∥ Fin l ≃ X ∥ → k ≡ l
trunc-Fin-equiv-to-same-ℕ k l u v =
  rec-prop-trunc (k ≡ l) (ℕ-set k l)
    (λ e → rec-prop-trunc (k ≡ l) (ℕ-set k l)
      (λ e' → Fin-equiv-to-same-ℕ k l (concat-≃ e (inv-≃ e'))) v) u

is-finite' : (X : Set ℓ) → Set _
is-finite' X = Σ ℕ (λ k → ∥ Fin k ≃ X ∥)

is-finite'-is-prop : (X : Set ℓ) → is-prop (is-finite' X)
is-finite'-is-prop X = is-prop'-to-is-prop λ { (k , u) (l , v) →
  let p = trunc-Fin-equiv-to-same-ℕ k l u v
  in eq-pair _ _ (p , is-prop-to-is-prop' (prop-trunc-is-prop _)
       (tr (λ k₁ → ∥ Fin k₁ ≃ X ∥) p u) v) }

is-finite-to-is-finite' : (X : Set ℓ) → is-finite X → is-finite' X
is-finite-to-is-finite' X Xfin =
  rec-prop-trunc (is-finite' X) (is-finite'-is-prop X)
    (λ { (k , e) → k , η e }) Xfin

is-finite'-to-is-finite : (X : Set ℓ) → is-finite' X → is-finite X
is-finite'-to-is-finite X (k , u) =
  rec-prop-trunc (is-finite X) (prop-trunc-is-prop _) (λ e → η (k , e)) u

card : (X : Set ℓ) → is-finite' X → ℕ
card X Xfin' = proj₁ Xfin'

𝔽-equiv-Σ-BS : 𝔽 ≃ Σ ℕ BS
𝔽-equiv-Σ-BS =
  concat-≃
    (tot (is-finite-to-is-finite') ,
      fam-equiv-to-tot-equiv is-finite-to-is-finite' λ X →
        proj₂ (iff-to-≃ (prop-trunc-is-prop _) (is-finite'-is-prop X)
          (is-finite-to-is-finite' X , is-finite'-to-is-finite X)))
    (Σ-swap λ X k → ∥ Fin k ≃ X ∥)

-- Proposition 16.3.5
-- (helper: finite choice for Fin k, by induction on k)
finite-choice-Fin : (k : ℕ) → (B : Fin k → Set ℓ)
  → ((i : Fin k) → ∥ B i ∥) → ∥ ((i : Fin k) → B i) ∥
finite-choice-Fin 0ℕ B h =
  rec-prop-trunc ∥ ((i : Fin 0ℕ) → B i) ∥ (prop-trunc-is-prop _)
    (λ z → z) (η (η λ ()))
finite-choice-Fin (succℕ k) B h = map-prop-trunc (λ {x (inl n) → proj₁ x n
                                                   ; x (inr *) → proj₂ x}) both
  where
    IH : ∥ ((i : Fin k) → B (inl i)) ∥
    IH = finite-choice-Fin k (λ i → B (inl i)) (λ i → h (inl i))

    both : ∥ ((i : Fin k) → B (inl i)) × B (inr *) ∥
    both = proj₁ (inv-≃ prop-trunc-×-≃-×-prop-trunc) (IH , h (inr *))

finite-choice : {A : Set ℓ} {B : A → Set ℓ₁} → is-finite A
  → ((x : A) → ∥ B x ∥) → ∥ ((x : A) → B x) ∥
finite-choice {A = A} {B = B} Afin h =
  rec-prop-trunc ∥ ((x : A) → B x) ∥ (prop-trunc-is-prop _) from-counting Afin
  where
    from-counting : count A → ∥ ((x : A) → B x) ∥
    from-counting (k , e) =
      map-prop-trunc (map-Π-≃ e (B ∘ proj₁ e) B λ i z → z)
        (finite-choice-Fin k (B ∘ proj₁ e) λ i → h (proj₁ e i))

-- Theorem 16.3.6 (i)
finite-to-⊎-finite : {X : Set ℓ} {Y : Set ℓ₁} → is-finite X → is-finite Y
  → is-finite (X ⊎ Y)
finite-to-⊎-finite {X = X} {Y = Y} Xfin Yfin =
  rec-prop-trunc (is-finite (X ⊎ Y)) (prop-trunc-is-prop _)
    (λ cX → rec-prop-trunc (is-finite (X ⊎ Y)) (prop-trunc-is-prop _)
      (λ cY → η (count-to-⊎-count cX cY)) Yfin) Xfin

⊎-finite-to-finite : {X : Set ℓ} {Y : Set ℓ₁} → is-finite (X ⊎ Y)
  → is-finite X × is-finite Y
⊎-finite-to-finite {X = X} {Y = Y} XYfin =
  rec-prop-trunc (is-finite X) (prop-trunc-is-prop _)
    (λ cXY → η (proj₁ (⊎-count-to-count cXY))) XYfin ,
  rec-prop-trunc (is-finite Y) (prop-trunc-is-prop _)
    (λ cXY → η (proj₂ (⊎-count-to-count cXY))) XYfin

-- Theorem 16.3.6 (ii)
finite-to-×-finite : {X : Set ℓ} {Y : Set ℓ₁} → is-finite X → is-finite Y
  → is-finite (X × Y)
finite-to-×-finite {X = X} {Y = Y} Xfin Yfin =
  rec-prop-trunc (is-finite (X × Y)) (prop-trunc-is-prop _)
    (λ cX → rec-prop-trunc (is-finite (X × Y)) (prop-trunc-is-prop _)
      (λ cY → η (count-to-Σ-count (λ _ → Y) cX λ _ → cY)) Yfin) Xfin

×-finite-to-finite-left : {X : Set ℓ} {Y : Set ℓ₁} → is-finite (X × Y) → Y
  → is-finite X
×-finite-to-finite-left {X = X} {Y = Y} XYfin y =
  rec-prop-trunc (is-finite X) (prop-trunc-is-prop _)
    (λ cXY → η (×-count-to-count-left cXY y)) XYfin

×-finite-to-finite-right : {X : Set ℓ} {Y : Set ℓ₁} → is-finite (X × Y) → X
  → is-finite Y
×-finite-to-finite-right {X = X} {Y = Y} XYfin x =
  rec-prop-trunc (is-finite Y) (prop-trunc-is-prop _)
    (λ cXY → η (×-count-to-count-right cXY x)) XYfin

-- Theorem 16.3.6 (iii)
-- (helpers: a counted type is decidable, hence finite types are
-- merely-inhabited-or-empty and their negations are finite)
count-to-dec : {X : Set ℓ} → count X → is-decidable X
count-to-dec {ℓ} {X} (0ℕ , e) = inr (proj₁ (inv-≃ e))
count-to-dec {ℓ} {X} (succℕ k , e) = inl (proj₁ e (inr *))

finite-to-dec-trunc : {X : Set ℓ} → is-finite X → is-decidable ∥ X ∥
finite-to-dec-trunc {X = X} Xfin =
  rec-prop-trunc (is-decidable ∥ X ∥)
    (is-decidable-is-prop (prop-trunc-is-prop _))
    (λ cX → dec-trunc (count-to-dec cX)) Xfin
  where
    dec-trunc : is-decidable X → is-decidable ∥ X ∥
    dec-trunc (inl x) = inl (η x)
    dec-trunc (inr n) = inr λ tx → (rec-prop-trunc Empty (λ ()) n tx)

finite-to-¬-finite : {X : Set ℓ} → is-finite X → is-finite (¬ X)
finite-to-¬-finite {X = X} Xfin =
  rec-prop-trunc (is-finite (¬ X)) (prop-trunc-is-prop _)
    (λ cX → η (prop-dec-to-count (¬ X) (¬-prop X) (¬-is-decidable (count-to-dec cX)))) Xfin

-- (helper: the fibre of the section map x ↦ (x , f x) at (x , y) is f x ≡ y)
fib-section-≃-≡ : {A : Set ℓ} → (B : A → Set ℓ₁) → (f : (x : A) → B x)
  → (z : Σ A B) → fib (λ x → x , f x) z ≃ (f (proj₁ z) ≡ proj₂ z)
fib-section-≃-≡ {A = A} B f (a , y) =
  concat-≃
    (tot (λ x → pair-eq (x , f x) (a , y)) ,
     fam-equiv-to-tot-equiv (λ x → pair-eq (x , f x) (a , y)) λ x → pair-eq-is-equiv (x , f x) (a , y))
    (concat-≃
      (inv-≃ (Σ-assoc (λ z → z ≡ a) λ x → tr B (proj₂ x) (f (proj₁ x)) ≡ y))
      (inv-≃ (_,_ (proj₁ (identity-contr a)) ,
              is-equiv-pair-contr-base (identity-contr a) λ x → tr B (proj₂ x) (f (proj₁ x)) ≡ y)))

finite-fam-to-Σ-finite : {A : Set ℓ} → (B : A → Set ℓ₁) → is-finite A
  → ((x : A) → is-finite (B x)) → is-finite (Σ A B)
finite-fam-to-Σ-finite {A = A} B Afin Bfin =
  rec-prop-trunc (is-finite (Σ A B)) (prop-trunc-is-prop _)
    (λ cA → rec-prop-trunc (is-finite (Σ A B)) (prop-trunc-is-prop _)
      (λ cB → η (count-to-Σ-count B cA cB)) (finite-choice Afin λ x → Bfin x)) Afin

Σ-finite-to-finite-fam : {A : Set ℓ} → (B : A → Set ℓ₁) → is-finite A
  → is-finite (Σ A B) → (x : A) → is-finite (B x)
Σ-finite-to-finite-fam {A = A} B Afin ΣABfin x =
  rec-prop-trunc (is-finite (B x)) (prop-trunc-is-prop _)
    (λ cA → rec-prop-trunc (is-finite (B x)) (prop-trunc-is-prop _)
      (λ cAB → η (Σ-count-to-fib-count B cA cAB x)) ΣABfin) Afin

finite-to-set-Σ-¬-finite : {A : Set ℓ} → (B : A → Set ℓ₁)
  → ((x : A) → is-finite (B x)) → is-finite (Σ A B) → is-finite A
  → is-set A × is-finite (Σ A (λ x → ¬ (B x)))
finite-to-set-Σ-¬-finite {A = A} B Bfin ΣABfin Afin = Aset , ¬B-fin
  where
    Aset : is-set A
    Aset = finite-to-set Afin

    ¬B-fin : is-finite (Σ A (λ x → ¬ (B x)))
    ¬B-fin = finite-fam-to-Σ-finite (λ x → ¬ (B x)) Afin λ x → finite-to-¬-finite (Bfin x)

sec-finite-to-finite : {A : Set ℓ} → (B : A → Set ℓ₁)
  → ((x : A) → is-finite (B x)) → is-finite (Σ A B) → ((x : A) → B x)
  → is-finite A
sec-finite-to-finite {A = A} B Bfin ΣABfin f =
  rec-prop-trunc (is-finite A) (prop-trunc-is-prop _) from-counting ΣABfin
  where
    s : A → Σ A B
    s x = x , f x

    P : Σ A B → Set _
    P z = fib s z

    B-set : (z : Σ A B) → is-set (B (proj₁ z))
    B-set z = finite-to-set (Bfin (proj₁ z))

    ≡-prop : (z : Σ A B) → is-prop (f (proj₁ z) ≡ proj₂ z)
    ≡-prop z = B-set z (f (proj₁ z)) (proj₂ z)

    P-prop : (z : Σ A B) → is-prop (P z)
    P-prop z = (proj₂ (≃-to-iff-prop (fib-section-≃-≡ B f z))) (≡-prop z)

    P-dec : (z : Σ A B) → is-decidable (P z)
    P-dec z =
      proj₁ (iff-to-iff-decidable (≃-to-iff (≡-prop z) (P-prop z) (inv-≃ (fib-section-≃-≡ B f z)))) ≡-dec
      where
        ≡-dec : is-decidable (f (proj₁ z) ≡ proj₂ z)
        ≡-dec = rec-prop-trunc (is-decidable (f (proj₁ z) ≡ proj₂ z)) (is-decidable-is-prop (≡-prop z))
          (λ cBz → count-to-dec-eq cBz (f (proj₁ z)) (proj₂ z)) (Bfin (proj₁ z))

    A-equiv : A ≃ Σ (Σ A B) P
    A-equiv = proj₁ (fib-repl s)

    from-counting : count (Σ A B) → is-finite A
    from-counting c =
      η (count-equiv (inv-≃ A-equiv)
          (count-to-Σ-count P c λ z → prop-dec-to-count (P z) (P-prop z) (P-dec z)))

-- (helper: restricting B to the base points where it is merely inhabited
--  does not change the total space)
Σ-Σ-trunc-≃ : {A : Set ℓ} → (B : A → Set ℓ₁)
  → Σ (Σ A (λ x → ∥ B x ∥)) (λ t → B (proj₁ t)) ≃ Σ A B
Σ-Σ-trunc-≃ B =
  concat-≃ (Σ-assoc (λ x → ∥ B x ∥) λ t → B (proj₁ t))
    (tot (λ x → proj₂) ,
     fam-equiv-to-tot-equiv (λ x → proj₂) λ x →
       ((λ b → η b , b) , λ b → refl) ,
       ((λ b → η b , b) , λ { (t , b) → eq-pair× (proj₁ (prop-trunc-is-prop (B x) (η b) t)) refl }))

set-Σ-¬-finite-to-finite : {A : Set ℓ} → (B : A → Set ℓ₁)
  → ((x : A) → is-finite (B x)) → is-finite (Σ A B)
  → is-set A × is-finite (Σ A (λ x → ¬ (B x))) → is-finite A
set-Σ-¬-finite-to-finite {A = A} B Bfin ΣABfin (Aset , ΣA¬Bfin) =
  equiv-finite-to-finite A-equiv (finite-to-⊎-finite ∥B∥-fin ΣA¬Bfin)
  where
    A-equiv : A ≃ (Σ A (λ x → ∥ B x ∥) ⊎ Σ A (λ x → ¬ (B x)))
    A-equiv =
      concat-≃ (inv-≃ (Σ-A-𝟙 A))
        (concat-≃
          ((tot λ x _ → dec-B x) ,
           fam-equiv-to-tot-equiv (λ x _ → dec-B x) λ x →
             contr-contr-to-equiv (λ _ → dec-B x) (* , λ {* → refl})
               (⊕-to-contr-⊎ (⊕-B x (dec-B x)) (prop-trunc-is-prop _) (¬-prop _)))
          (Σ-distrib-⊎ (λ x → ∥ B x ∥) λ x → ¬ (B x)))
      where
        dec-B : (x : A) → ∥ B x ∥ ⊎ ¬ (B x)
        dec-B x = aux (finite-to-dec-trunc (Bfin x))
          where
            aux : is-decidable ∥ B x ∥ → ∥ B x ∥ ⊎ ¬ (B x)
            aux (inl tbx) = inl tbx
            aux (inr ntbx) = inr λ bx → ntbx (η bx)

        ⊕-B : (x : A) → ∥ B x ∥ ⊎ ¬ (B x) → ∥ B x ∥ ⊕ ¬ (B x)
        ⊕-B x (inl tbx) = inl (tbx , λ nbx → rec-prop-trunc Empty (λ ()) nbx tbx)
        ⊕-B x (inr nbx) = inr (nbx , λ tbx → rec-prop-trunc Empty (λ ()) nbx tbx)

    ∥B∥-fin : is-finite (Σ A (λ x → ∥ B x ∥))
    ∥B∥-fin =
      rec-prop-trunc (is-finite (Σ A (λ x → ∥ B x ∥))) (prop-trunc-is-prop _) from-counting ΣABfin
      where
        dec-eq : (a x : A) → ∥ B x ∥ → is-decidable (a ≡ x)
        dec-eq a x tx = rec-prop-trunc (is-decidable (a ≡ x)) (is-decidable-is-prop (Aset a x))
          (λ bx → to-dec (finite-to-dec-trunc (equiv-finite-to-finite (inv-≃ (fib-fib-incl-≃-≡ B a x bx))
            (finite-fam-to-Σ-finite (λ b → (a , b) ≡ (x , bx)) (Bfin a)
              (λ b → η (prop-dec-to-count _ (finite-to-set ΣABfin _ _) (finite-to-dec-eq ΣABfin _ _)))))))
          tx
          where
            to-dec : {a x : A} → is-decidable ∥ a ≡ x ∥ → is-decidable (a ≡ x)
            to-dec (inl t) = inl (rec-prop-trunc _ (Aset _ _) (λ p → p) t)
            to-dec (inr n) = inr (λ p → n (η p))

        section : count (Σ A B) → (t : Σ A (λ x → ∥ B x ∥)) → B (proj₁ t)
        section (k , (f , ((g , fg) , _))) (a , ta) =
          tr B (proj₂ (pick a ta)) (proj₂ (f (proj₁ (pick a ta))))
          where
            pick : (a : A) → ∥ B a ∥ → Σ (Fin k) (λ i → proj₁ (f i) ≡ a)
            pick a ta = ∃-to-Σ-decidableFin k (λ i → proj₁ (f i) ≡ a)
              (λ i → dec-eq (proj₁ (f i)) a ta)
              (rec-prop-trunc _ (prop-trunc-is-prop _) (λ b → η (g (a , b) , ap proj₁ (fg (a , b)))) ta)

        from-counting : count (Σ A B) → is-finite (Σ A (λ x → ∥ B x ∥))
        from-counting e =
          sec-finite-to-finite (λ t → B (proj₁ t)) (λ t → Bfin (proj₁ t))
            (equiv-finite-to-finite (Σ-Σ-trunc-≃ B) ΣABfin) (section e)


-- Exercises
-- 16.1
-- (a)
Fin-pow-equiv-→ : (n m : ℕ) → Fin (n ^ℕ m) ≃ (Fin m → Fin n)
Fin-pow-equiv-→ n 0ℕ = (λ z ()) , contr-contr-to-equiv (λ z ()) ((inr *) , λ {(inl ()) ; (inr *) → refl}) ((λ ()) , λ {x → eq-htpy _ _ λ ()})
Fin-pow-equiv-→ n (succℕ m) = concat-≃ (Fin-mul-equiv-× n (n ^ℕ m)) (concat-≃ (×-equiv-right (Fin-pow-equiv-→ n m)) (concat-≃ (×-symm (Fin n) (Fin m → Fin n)) (concat-≃ (×-equiv-right (inv-≃ (Π-𝟙 λ * →  Fin n))) (inv-≃ (ev-⊎ (Fin m) 𝟙 (Fin n) , ⊎-up (Fin m) 𝟙 (Fin n))))))

finite-to-→-finite : {A : Set ℓ} {B : Set ℓ₁} → is-finite A → is-finite B → is-finite (A → B)
finite-to-→-finite {A = A} {B = B} Afin Bfin =
  rec-prop-trunc (is-finite (A → B)) (prop-trunc-is-prop _)
    (λ {(n , e) → rec-prop-trunc (is-finite (A → B)) (prop-trunc-is-prop _)
      (λ {(m , e') → η ((m ^ℕ n) ,
        concat-≃ (Fin-pow-equiv-→ m n)
          (concat-≃ (precomp (proj₁ (inv-≃ e)) (Fin m) , precomp-equiv-to-equiv (inv-≃ e) (Fin m))
            (map-Π (λ _ → Fin m) (λ _ → B) (λ _ → proj₁ e') ,
             fam-equiv-to-Π-equiv (λ _ → Fin m) (λ _ → B) (λ _ → proj₁ e') (λ _ → proj₂ e'))))})
      Bfin})
    Afin

-- (b)
Fin-fact-equiv-Fin-equiv : (n : ℕ) → Fin (factorialℕ n) ≃ (Fin n ≃ Fin n)
Fin-fact-equiv-Fin-equiv 0ℕ = (λ x → empty-to-𝟘-equiv λ ()) , contr-contr-to-equiv (λ x → empty-to-𝟘-equiv λ ()) ((inr *) , λ {(inl ()); (inr *) → refl}) (is-prop'-to-inhab-contr (is-prop-to-is-prop' (≃-prop (λ ()) (λ ()))) (empty-to-𝟘-equiv λ ()))
Fin-fact-equiv-Fin-equiv (succℕ n) = concat-≃ (Fin-mul-equiv-× (succℕ n) (factorialℕ n)) (concat-≃ (×-equiv-right (Fin-fact-equiv-Fin-equiv n)) perm-equiv)
  where
    -- a permutation of n+1 points is a choice of image for the last point plus a permutation of the rest
    perm-equiv : (Fin (succℕ n) × (Fin n ≃ Fin n)) ≃ (Fin (succℕ n) ≃ Fin (succℕ n))
    perm-equiv = fwd , ((bwd , fwd-bwd) , (bwd , bwd-fwd))
      where
        -- the transposition swapping z and the last point
        swap : Fin (succℕ n) → Fin (succℕ n) → Fin (succℕ n)
        swap z x with Fin-decidable-eq (succℕ n) z x
        ... | inl p = inr *
        ... | inr np with Fin-decidable-eq (succℕ n) x (inr *)
        ... | inl q = z
        ... | inr nq = x

        -- computation facts for swap, matching its own case split
        swap-eq : (z x : Fin (succℕ n)) → z ≡ x → swap z x ≡ inr *
        swap-eq z x p with Fin-decidable-eq (succℕ n) z x
        ... | inl _ = refl
        ... | inr np = ex-falso (np p)

        swap-pt : (z x : Fin (succℕ n)) → ¬ (z ≡ x) → x ≡ inr * → swap z x ≡ z
        swap-pt z x np q with Fin-decidable-eq (succℕ n) z x
        ... | inl p = ex-falso (np p)
        ... | inr _ with Fin-decidable-eq (succℕ n) x (inr *)
        ...   | inl _ = refl
        ...   | inr nq = ex-falso (nq q)

        swap-fix : (z x : Fin (succℕ n)) → ¬ (z ≡ x) → ¬ (x ≡ inr *) → swap z x ≡ x
        swap-fix z x np nq with Fin-decidable-eq (succℕ n) z x
        ... | inl p = ex-falso (np p)
        ... | inr _ with Fin-decidable-eq (succℕ n) x (inr *)
        ...   | inl q = ex-falso (nq q)
        ...   | inr _ = refl

        -- swap-swap mirrors swap's own case split with nested `with`s,
        -- so each reduction fires the same way it does inside swap itself.
        swap-swap : (x : Fin (succℕ n)) → (swap x) ∘ (swap x) ∼ id
        swap-swap x z with Fin-decidable-eq (succℕ n) x z
        swap-swap x z | inl refl with Fin-decidable-eq (succℕ n) x x
        swap-swap x z | inl refl | inl _ with Fin-decidable-eq (succℕ n) x (inr *)
        swap-swap x z | inl refl | inl _ | inl q = inv q
        swap-swap x z | inl refl | inl _ | inr _ = refl
        swap-swap x z | inl refl | inr absurd = ex-falso (absurd refl)
        swap-swap x z | inr np with Fin-decidable-eq (succℕ n) z (inr *)
        swap-swap x z | inr np | inl q with Fin-decidable-eq (succℕ n) x x
        swap-swap x z | inr np | inl q | inl _ = inv q
        swap-swap x z | inr np | inl q | inr absurd = ex-falso (absurd refl)
        swap-swap x z | inr np | inr nq with Fin-decidable-eq (succℕ n) x z
        swap-swap x z | inr np | inr nq | inl p = ex-falso (np p)
        swap-swap x z | inr np | inr nq | inr _ with Fin-decidable-eq (succℕ n) z (inr *)
        swap-swap x z | inr np | inr nq | inr _ | inl q' = ex-falso (nq q')
        swap-swap x z | inr np | inr nq | inr _ | inr _ = refl

        transp : Fin (succℕ n) → Fin (succℕ n) ≃ Fin (succℕ n)
        transp z = swap z , ((swap z , swap-swap z) , (swap z , swap-swap z))

        fwd : (Fin (succℕ n) × (Fin n ≃ Fin n)) → (Fin (succℕ n) ≃ Fin (succℕ n))
        fwd (z , g) = concat-≃ (⊎-equiv-left g) (transp z)

        bwd : (Fin (succℕ n) ≃ Fin (succℕ n)) → (Fin (succℕ n) × (Fin n ≃ Fin n))
        bwd e = proj₁ e (inr *) , ⊎-𝟙-equiv-to-equiv e

        -- transport in a constant family is trivial
        tr-triv : {A : Set ℓ} {C : Set ℓ₁} {u v : A} (q : u ≡ v) {c c' : C}
          → c ≡ c' → tr (λ _ → C) q c ≡ c'
        tr-triv refl eq = eq

        -- two equivalences with equal underlying maps are equal
        eq-≃ : {X : Set ℓ} {Y : Set ℓ₁} → (e e' : X ≃ Y) → proj₁ e ≡ proj₁ e' → e ≡ e'
        eq-≃ (f , ef) (f' , ef') q =
          eq-pair (f , ef) (f' , ef') (q , is-prop-to-is-prop' (equiv-is-prop f') (tr is-equiv q ef) ef')

        -- injectivity of inl, as a constructor
        inl-inj : {A : Set ℓ} {B : Set ℓ₁} {a b : A} → _≡_ {A = A ⊎ B} (inl a) (inl b) → a ≡ b
        inl-inj refl = refl

        -- (helper: the underlying map of concat-≃, since it's stuck on an abstract equivalence)
        concat-≃-apply : {A : Set ℓ} {B : Set ℓ₁} {C : Set ℓ₂} (e1 : A ≃ B) (e2 : B ≃ C) (x : A)
          → proj₁ (concat-≃ e1 e2) x ≡ proj₁ e2 (proj₁ e1 x)
        concat-≃-apply (f , ((sf , fsf) , (rf , rff))) (g , ((sg , gsg) , (rg , rgg))) x = refl

        ⊎-equiv-left-inl : {A : Set ℓ} {A' : Set ℓ₁} {B : Set ℓ₂} (e : A ≃ A') (x : A)
          → proj₁ (⊎-equiv-left {B = B} e) (inl x) ≡ inl (proj₁ e x)
        ⊎-equiv-left-inl (f , ef) x = refl

        ⊎-equiv-left-inr : {A : Set ℓ} {A' : Set ℓ₁} {B : Set ℓ₂} (e : A ≃ A') (y : B)
          → proj₁ (⊎-equiv-left {B = B} e) (inr y) ≡ inr y
        ⊎-equiv-left-inr (f , ef) y = refl

        swap-inr-fix : (z : Fin (succℕ n)) → swap z (inr *) ≡ z
        swap-inr-fix z with Fin-decidable-eq (succℕ n) z (inr *)
        ... | inl q = inv q
        ... | inr nq = refl

        fwd-bwd : (e : Fin (succℕ n) ≃ Fin (succℕ n)) → fwd (bwd e) ≡ e
        fwd-bwd e = {!   !}

        bwd-fwd : (p : Fin (succℕ n) × (Fin n ≃ Fin n)) → bwd (fwd p) ≡ p
        bwd-fwd (z , g) = eq-pair (bwd (fwd (z , g))) (z , g) (p1 , tr-triv p1 p2)
          where
            h : Fin (succℕ n) → Fin (succℕ n)
            h = proj₁ (fwd (z , g))

            he : is-equiv h
            he = proj₂ (fwd (z , g))

            h-inl : (i : Fin n) → h (inl i) ≡ swap z (inl (proj₁ g i))
            h-inl i = concat (concat-≃-apply (⊎-equiv-left g) (transp z) (inl i))
                              (ap (proj₁ (transp z)) (⊎-equiv-left-inl g i))

            h-inr* : h (inr *) ≡ swap z (inr *)
            h-inr* = concat (concat-≃-apply (⊎-equiv-left g) (transp z) (inr *))
                             (ap (proj₁ (transp z)) (⊎-equiv-left-inr g *))

            -- the last point of fwd (z , g) does land on z
            p1 : h (inr *) ≡ z
            p1 = concat h-inr* (swap-inr-fix z)

            -- the permutation extracted back out of fwd (z , g) is g, pointwise
            g-hom : (i : Fin n) → map-⊎-𝟙 h he i ≡ proj₁ g i
            g-hom i with Fin-decidable-eq (succℕ n) z (inl (proj₁ g i))
            g-hom i | inl r = concat (map-⊎-𝟙-inr h he i hp) (inl-inj (concat (proj₂ (star-value h he i hp)) hinr))
              where
                hp : h (inl i) ≡ inr *
                hp = concat (h-inl i) (swap-eq z (inl (proj₁ g i)) r)
                hinr : h (inr *) ≡ inl (proj₁ g i)
                hinr = concat p1 r
            g-hom i | inr nr = map-⊎-𝟙-inl h he i (proj₁ g i) hp
              where
                hp : h (inl i) ≡ inl (proj₁ g i)
                hp = concat (h-inl i) (swap-fix z (inl (proj₁ g i)) nr (λ q → inl-ne-inr (proj₁ g i) * q))

            p2 : ⊎-𝟙-equiv-to-equiv (fwd (z , g)) ≡ g
            p2 = eq-≃ (⊎-𝟙-equiv-to-equiv (fwd (z , g))) g (eq-htpy _ _ g-hom)