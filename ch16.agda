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
