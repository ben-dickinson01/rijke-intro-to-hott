module ch8 where

open import ch7 public

is-decidable : Set lzero → Set lzero
is-decidable A = A ⊎ ¬ A

𝟘-is-decidable : is-decidable 𝟘
𝟘-is-decidable = inr id

𝟙-is-decidable : is-decidable 𝟙
𝟙-is-decidable = inl *

𝟚-is-decidable : is-decidable 𝟚
𝟚-is-decidable = inl true

⊎-is-decidable : {A B : Set} → is-decidable A → is-decidable B → is-decidable (A ⊎ B)
⊎-is-decidable (inl a) db = inl (inl a)
⊎-is-decidable (inr na) (inl b) = inl (inr b)
⊎-is-decidable (inr na) (inr nb) = inr (ind⊎ (λ a → na a) (λ b → nb b))

×-is-decidable : {A B : Set} → is-decidable A → is-decidable B → is-decidable (A × B)
×-is-decidable (inl a) (inl b) = inl (a , b)
×-is-decidable (inl a) (inr nb) = inr (λ ab → nb (proj₂ ab))
×-is-decidable (inr na) (inl b) = inr (λ ab → na (proj₁ ab))
×-is-decidable (inr na) (inr nb) = inr (λ ab → na (proj₁ ab))

→-is-decidable : {A B : Set} → is-decidable A → is-decidable B → is-decidable (A → B)
→-is-decidable (inl a) (inl b) = inl (λ _ → b)
→-is-decidable (inl a) (inr nb) = inr (λ f → nb (f a))
→-is-decidable (inr na) (inl b) = inl (λ _ → b)
→-is-decidable (inr na) (inr nb) = inl (λ a → ex-falso (na a))

¬-is-decidable : {A : Set} → is-decidable A → is-decidable (¬ A)
¬-is-decidable (inl a) = inr (λ na → na a)
¬-is-decidable (inr na) = inl na

Eq-ℕ-is-decidable : (m n : ℕ) → is-decidable (Eq-ℕ m n)
Eq-ℕ-is-decidable 0ℕ 0ℕ = 𝟙-is-decidable
Eq-ℕ-is-decidable 0ℕ (succℕ n) = 𝟘-is-decidable
Eq-ℕ-is-decidable (succℕ m) 0ℕ = 𝟘-is-decidable
Eq-ℕ-is-decidable (succℕ m) (succℕ n) = Eq-ℕ-is-decidable m n

≤ℕ-is-decidable : (m n : ℕ) → is-decidable (m ≤ℕ n)
≤ℕ-is-decidable 0ℕ 0ℕ = 𝟙-is-decidable
≤ℕ-is-decidable 0ℕ (succℕ n) = 𝟙-is-decidable
≤ℕ-is-decidable (succℕ m) 0ℕ = 𝟘-is-decidable
≤ℕ-is-decidable (succℕ m) (succℕ n) = ≤ℕ-is-decidable m n

<ℕ-is-decidable : (m n : ℕ) → is-decidable (m <ℕ n)
<ℕ-is-decidable 0ℕ 0ℕ = 𝟘-is-decidable
<ℕ-is-decidable 0ℕ (succℕ n) = 𝟙-is-decidable
<ℕ-is-decidable (succℕ m) 0ℕ = 𝟘-is-decidable
<ℕ-is-decidable (succℕ m) (succℕ n) = <ℕ-is-decidable m n

has-decidable-eq : (A : Set) → Set
has-decidable-eq A = (x y : A) → is-decidable (x ≡ y)

iff-to-iff-decidable : (A B : Set) → (A ↔ B) → is-decidable A ↔ is-decidable B
iff-to-iff-decidable A B (A→B , B→A) = (⊎functor (A→B) (contrapositive B→A) , ⊎functor (B→A) (contrapositive A→B))

ℕ-decidable-eq : has-decidable-eq ℕ
ℕ-decidable-eq 0ℕ 0ℕ = inl refl
ℕ-decidable-eq 0ℕ (succℕ y) = inr (zero-ne-succℕ y)
ℕ-decidable-eq (succℕ x) 0ℕ = inr λ p → zero-ne-succℕ x (inv p)
ℕ-decidable-eq (succℕ x) (succℕ y) = ⊎functor (proj₁ (succ-injℕ x y)) (contrapositive (proj₂ (succ-injℕ x y))) (ℕ-decidable-eq x y)

Eq-Fin-is-decidable : (k : ℕ) → (x y : Fin k) → is-decidable (Eq-Fin k x y)
Eq-Fin-is-decidable (succℕ k) (inl x) (inl y) = Eq-Fin-is-decidable k x y
Eq-Fin-is-decidable (succℕ k) (inl x) (inr *) = 𝟘-is-decidable
Eq-Fin-is-decidable (succℕ k) (inr *) (inl y) = 𝟘-is-decidable
Eq-Fin-is-decidable (succℕ k) (inr *) (inr *) = 𝟙-is-decidable

Fin-decidable-eq : (k : ℕ) → has-decidable-eq (Fin k)
Fin-decidable-eq (succℕ k) x y =
  proj₁ (iff-to-iff-decidable (Eq-Fin (succℕ k) x y) (x ≡ y)
    (Eq-Fin-to-≡Fin (succℕ k) x y , ≡Fin-to-Eq-Fin (succℕ k) x y))
    (Eq-Fin-is-decidable (succℕ k) x y)

zero-div-to-≡0ℕ : (x : ℕ) → 0ℕ ∣ x → x ≡ 0ℕ
zero-div-to-≡0ℕ x (0ℕ , refl) = refl
zero-div-to-≡0ℕ x (succℕ k , refl) = refl

zero-div-iff-≡0ℕ : (x : ℕ) → (0ℕ ∣ x) ↔ (x ≡ 0ℕ)
zero-div-iff-≡0ℕ x = (zero-div-to-≡0ℕ x , λ p → (0ℕ , inv p))

divℕ-is-decidable : (d x : ℕ) → is-decidable (d ∣ x)
divℕ-is-decidable 0ℕ 0ℕ = proj₂ (iff-to-iff-decidable (0ℕ ∣ 0ℕ) (0ℕ ≡ 0ℕ) (zero-div-iff-≡0ℕ 0ℕ)) (inl refl)
divℕ-is-decidable 0ℕ (succℕ x) = proj₂ (iff-to-iff-decidable (0ℕ ∣ succℕ x) (succℕ x ≡ 0ℕ) (zero-div-iff-≡0ℕ (succℕ x))) (inr λ p → zero-ne-succℕ x (inv p))
divℕ-is-decidable (succℕ d) x =
  proj₁ (iff-to-iff-decidable ([ x ] (succℕ d) ≡ [ 0ℕ ] (succℕ d)) ((succℕ d) ∣ x)
    ((λ p → tr ((succℕ d) ∣_) (dist-zero-rightℕ x) (proj₁ (Fin-k-is-ℕmod-k d x 0ℕ) p)) ,
     (λ q → proj₂ (Fin-k-is-ℕmod-k d x 0ℕ) (tr ((succℕ d) ∣_) (inv (dist-zero-rightℕ x)) q))))
    (Fin-decidable-eq (succℕ d) ([ x ] (succℕ d)) ([ 0ℕ ] (succℕ d)))

is-evenℕ : (n : ℕ) → is-decidable (2ℕ ∣ n)
is-evenℕ n = divℕ-is-decidable 2ℕ n

collatz-helper : (n : ℕ) → is-decidable (2ℕ ∣ n) → ℕ
collatz-helper n (inl (k , p)) = k
collatz-helper n (inr d) = 3ℕ ·ℕ n +ℕ 1ℕ

collatz : ℕ → ℕ
collatz n = collatz-helper n (is-evenℕ n)

×-is-decidable-with : (A B : Set) → is-decidable A → (A → is-decidable B) → is-decidable (A × B)
×-is-decidable-with A B (inl x) f with f x
... | inl b = inl (x , b)
... | inr nb = inr λ ab → nb (proj₂ ab)
×-is-decidable-with A B (inr x) f = inr λ p → x (proj₁ p)

→-is-decidable-with : (A B : Set) → is-decidable A → (A → is-decidable B) → is-decidable (A → B)
→-is-decidable-with A B (inl x) f with f x
... | inl b = inl λ a → b
... | inr nb = inr λ ab → nb (ab x)
→-is-decidable-with A B (inr x) f = inl λ a → ex-falso (x a)

Πℕ-is-decidable : (P : ℕ → Set) → ((x : ℕ) → is-decidable (P x)) → (m : ℕ) → is-decidable ((x : ℕ) → (m ≤ℕ x) → P x) → is-decidable ((x : ℕ) → P x)
Πℕ-is-decidable P dP 0ℕ (inl f) = inl (λ n → f n (0ℕ-leℕ n))
Πℕ-is-decidable P dP 0ℕ (inr nf) = inr (λ g → nf (λ n _ → g n))
Πℕ-is-decidable P dP (succℕ m) dxmP with dP 0ℕ
... | inr np0 = inr (λ f → np0 (f 0ℕ))
... | inl p0 = ⊎functor
  (λ g → λ { 0ℕ → p0 ; (succℕ n) → g n })
  (λ ng f → ng (λ n → f (succℕ n)))
  (Πℕ-is-decidable (λ x → P (succℕ x)) (λ x → dP (succℕ x)) m
    (⊎functor (λ f x h → f (succℕ x) h) (λ nf g → nf (λ { 0ℕ () ; (succℕ x) h → g x h })) dxmP))

Π-→-is-decidableℕ : (P Q : ℕ → Set) → ((x : ℕ) → is-decidable (P x)) → ((x : ℕ) → is-decidable (Q x)) →
  (m : ℕ) → ((x : ℕ) → P x → x <ℕ m) →
  is-decidable ((n : ℕ) → P n → Q n)
Π-→-is-decidableℕ P Q dP dQ m ub =
  Πℕ-is-decidable (λ n → P n → Q n) (λ n → →-is-decidable-with (P n) (Q n) (dP n) (λ _ → dQ n)) m
    (inl (λ x h px → ex-falso (<-to-≱ x m (ub x px) h)))
