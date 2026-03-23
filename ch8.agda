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

0ℕdiv : (x : ℕ) → 0ℕ ∣ x → x ≡ 0ℕ
0ℕdiv x (0ℕ , refl) = refl
0ℕdiv x (succℕ k , refl) = refl

0ℕdiv-iff-eq0ℕ : (x : ℕ) → (0ℕ ∣ x) ↔ (x ≡ 0ℕ)
0ℕdiv-iff-eq0ℕ x = (0ℕdiv x , λ p → (0ℕ , inv p))

divℕ-decidable : (d x : ℕ) → is-decidable (d ∣ x)
divℕ-decidable 0ℕ 0ℕ = proj₂ (iff-to-iff-decidable (0ℕ ∣ 0ℕ) (0ℕ ≡ 0ℕ) (0ℕdiv-iff-eq0ℕ 0ℕ)) (inl refl)
divℕ-decidable 0ℕ (succℕ x) = proj₂ (iff-to-iff-decidable (0ℕ ∣ succℕ x) (succℕ x ≡ 0ℕ) (0ℕdiv-iff-eq0ℕ (succℕ x))) (inr λ p → zero-ne-succℕ x (inv p))
divℕ-decidable (succℕ d) x =
  proj₁ (iff-to-iff-decidable ([ x ] (succℕ d) ≡ [ 0ℕ ] (succℕ d)) ((succℕ d) ∣ x)
    ((λ p → tr ((succℕ d) ∣_) (dist-zero-rightℕ x) (proj₁ (Fin-k-is-ℕmod-k d x 0ℕ) p)) ,
     (λ q → proj₂ (Fin-k-is-ℕmod-k d x 0ℕ) (tr ((succℕ d) ∣_) (inv (dist-zero-rightℕ x)) q))))
    (Fin-decidable-eq (succℕ d) ([ x ] (succℕ d)) ([ 0ℕ ] (succℕ d)))

is-evenℕ : (n : ℕ) → is-decidable (2ℕ ∣ n)
is-evenℕ n = divℕ-decidable 2ℕ n

collatz-helper : (n : ℕ) → is-decidable (2ℕ ∣ n) → ℕ
collatz-helper n (inl (k , p)) = k
collatz-helper n (inr d) = 3ℕ ·ℕ n +ℕ 1ℕ

collatz : ℕ → ℕ
collatz n = collatz-helper n (is-evenℕ n)

with-decidable-prod : (A B : Set) → is-decidable A → (A → is-decidable B) → is-decidable (A × B)
with-decidable-prod A B (inl x) f with f x
... | inl b = inl (x , b)
... | inr nb = inr λ ab → nb (proj₂ ab)
with-decidable-prod A B (inr x) f = inr λ p → x (proj₁ p)

with-decidable-arrow : (A B : Set) → is-decidable A → (A → is-decidable B) → is-decidable (A → B)
with-decidable-arrow A B (inl x) f with f x
... | inl b = inl λ a → b
... | inr nb = inr λ ab → nb (ab x)
with-decidable-arrow A B (inr x) f = inl λ a → ex-falso (x a)

pi-type-decidable : (P : ℕ → Set) → ((x : ℕ) → is-decidable (P x)) → (m : ℕ) → is-decidable ((x : ℕ) → (m ≤ℕ x) → P x) → is-decidable ((x : ℕ) → P x)
pi-type-decidable P dP 0ℕ (inl f) = inl (λ n → f n (0ℕ-leℕ n))
pi-type-decidable P dP 0ℕ (inr nf) = inr (λ g → nf (λ n _ → g n))
pi-type-decidable P dP (succℕ m) dxmP with dP 0ℕ
... | inr np0 = inr (λ f → np0 (f 0ℕ))
... | inl p0 = ⊎functor
  (λ g → λ { 0ℕ → p0 ; (succℕ n) → g n })
  (λ ng f → ng (λ n → f (succℕ n)))
  (pi-type-decidable (λ x → P (succℕ x)) (λ x → dP (succℕ x)) m
    (⊎functor (λ f x h → f (succℕ x) h) (λ nf g → nf (λ { 0ℕ () ; (succℕ x) h → g x h })) dxmP))

pi-arrow-decidable : (P Q : ℕ → Set) → ((x : ℕ) → is-decidable (P x)) → ((x : ℕ) → is-decidable (Q x)) →
  (m : ℕ) → ((x : ℕ) → P x → x <ℕ m) →
  is-decidable ((n : ℕ) → P n → Q n)
pi-arrow-decidable P Q dP dQ m ub =
  pi-type-decidable (λ n → P n → Q n) (λ n → with-decidable-arrow (P n) (Q n) (dP n) (λ _ → dQ n)) m
    (inl (λ x h px → ex-falso (<-to-≱ x m (ub x px) h)))

is-lower-bound : (P : ℕ → Set) → (n : ℕ) → Set
is-lower-bound P n = (x : ℕ) → P x → n ≤ℕ x

is-upper-bound : (P : ℕ → Set) → (n : ℕ) → Set
is-upper-bound P n = (x : ℕ) → P x → x ≤ℕ n

-- Theorem 8.3.2: Well-ordering principle of ℕ.
-- By induction on the witness n:
--   Base case: n = 0 means P 0 holds, and 0 is trivially a lower bound.
--   Inductive step: n = succ n'. Check P 0.
--     If P 0: same as base case.
--     If ¬P 0: shift the family to Q(x) = P(succ x). Then Q is decidable
--       and Q(n') = P(succ n') holds. By IH on n', get minimal m' for Q.
--       Then succ m' is minimal for P.
ℕ-well-order-aux : (n : ℕ) → (P : ℕ → Set) → ((x : ℕ) → is-decidable (P x)) →
  P n → Σ ℕ (λ m → P m × is-lower-bound P m)
ℕ-well-order-aux 0ℕ P dP P0 = (0ℕ , (P0 , (λ x _ → 0ℕ-leℕ x)))
ℕ-well-order-aux (succℕ n) P dP Psn with dP 0ℕ
... | inl P0 = (0ℕ , (P0 , (λ x _ → 0ℕ-leℕ x)))
... | inr ¬P0 with ℕ-well-order-aux n (λ x → P (succℕ x)) (λ x → dP (succℕ x)) Psn
... | (m' , (Pm' , lb)) = (succℕ m' , (Pm' , shifted-lb))
  where
  shifted-lb : is-lower-bound P (succℕ m')
  shifted-lb 0ℕ P0 = ex-falso (¬P0 P0)
  shifted-lb (succℕ x) Psx = lb x Psx

ℕ-well-ordered : (P : ℕ → Set) → ((x : ℕ) → is-decidable (P x)) →
  Σ ℕ (λ n → P n) →
  Σ ℕ (λ m → P m × is-lower-bound P m)
ℕ-well-ordered P dP (n , Pn) = ℕ-well-order-aux n P dP Pn

is-gcdℕ : (a b d : ℕ) → Set
is-gcdℕ a b d = (x : ℕ) → ((x ∣ a) × (x ∣ b)) ↔ (x ∣ d)

gcd-uniqueℕ : (a b : ℕ) → (d d' : ℕ) → (is-gcdℕ a b d) → (is-gcdℕ a b d') → d ≡ d'
gcd-uniqueℕ a b d e dgcd egcd = div-antisymℕ d e (proj₁ (egcd d) (proj₂ (dgcd d) (div-rflℕ d))) (proj₁ (dgcd e) (proj₂ (egcd e) (div-rflℕ e)))

gcd-helper-type : (a b n : ℕ) → Set
gcd-helper-type a b n = ¬ (a +ℕ b ≡ 0ℕ) → ¬ (n ≡ 0ℕ) × ((x : ℕ) → ((x ∣ a) × (x ∣ b)) → (x ∣ n))

divℕ-to-≤ℕ : (d x : ℕ) → (d ∣ x) → ¬ (x ≡ 0ℕ) → d ≤ℕ x
divℕ-to-≤ℕ d x (0ℕ , p) xne0 = ex-falso (xne0 (concat (inv p) (zero-mulℕ d)))
divℕ-to-≤ℕ d x (succℕ k , p) xne0 = ≤-transℕ {d} {succℕ k ·ℕ d} {x} (≤-transℕ {d} {d +ℕ k ·ℕ d} {succℕ k ·ℕ d} (add-≤ℕ d 0ℕ (k ·ℕ d) (0ℕ-leℕ (k ·ℕ d))) (≡-to-≤ℕ (concat (add-commℕ d (k ·ℕ d)) (inv (succ-mulℕ k d))))) (≡-to-≤ℕ p)

≤-to-<-succℕ : (m n : ℕ) → m ≤ℕ n → m <ℕ succℕ n
≤-to-<-succℕ 0ℕ n p = *
≤-to-<-succℕ (succℕ m) (succℕ n) p = ≤-to-<-succℕ m n p

gcd-helper-decidable : (a b : ℕ) → (n : ℕ) → is-decidable (gcd-helper-type a b n)
gcd-helper-decidable a b n = with-decidable-arrow (¬ (a +ℕ b ≡ 0ℕ)) (¬ (n ≡ 0ℕ) × ((x : ℕ) → ((x ∣ a) × (x ∣ b)) → (x ∣ n))) (with-decidable-arrow (a +ℕ b ≡ 0ℕ) Empty (ℕ-decidable-eq (a +ℕ b) 0ℕ) λ p → inr id) λ abne0 → with-decidable-prod (¬ (n ≡ 0ℕ)) ((x : ℕ) → x ∣ a × x ∣ b → x ∣ n) ((with-decidable-arrow (n ≡ 0ℕ) Empty (ℕ-decidable-eq n 0ℕ) (λ p → inr id))) λ nneq0 → pi-arrow-decidable (λ x → x ∣ a × x ∣ b) (λ x → x ∣ n) (λ x → ×-is-decidable (divℕ-decidable x a) (divℕ-decidable x b)) (λ x → divℕ-decidable x n) (succℕ (a +ℕ b)) (λ x p → ≤-to-<-succℕ x (a +ℕ b) (divℕ-to-≤ℕ x (a +ℕ b) (div-sumℕ a b x (proj₁ p) (proj₂ p)) abne0))

gcd-helper-add : (a b : ℕ) → gcd-helper-type a b (a +ℕ b)
gcd-helper-add a b = λ sumne0 → (sumne0 , λ x p → div-sumℕ a b x (proj₁ p) (proj₂ p))

gcdℕ : ℕ → ℕ → ℕ
gcdℕ a b = proj₁ (ℕ-well-ordered (gcd-helper-type a b) (λ n → gcd-helper-decidable a b n) (((a +ℕ b) , gcd-helper-add a b)))

gcdℕ-0-to-ab-0ℕ : (a b : ℕ) → gcdℕ a b ≡ 0ℕ → a +ℕ b ≡ 0ℕ
gcdℕ-0-to-ab-0ℕ a b g = f (ℕ-decidable-eq (a +ℕ b) 0ℕ)
  where
    gcd-full = ℕ-well-ordered (gcd-helper-type a b) (λ n → gcd-helper-decidable a b n) ((a +ℕ b) , gcd-helper-add a b)
    gcd-prop = proj₁ (proj₂ gcd-full)
    f : is-decidable (a +ℕ b ≡ 0ℕ) → a +ℕ b ≡ 0ℕ
    f (inl p) = p
    f (inr np) = ex-falso (proj₁ (gcd-prop np) g)

ab-0ℕ-to-gcd-0ℕ : (a b : ℕ) → (a +ℕ b ≡ 0ℕ) → gcdℕ a b ≡ 0ℕ
ab-0ℕ-to-gcd-0ℕ 0ℕ 0ℕ refl = refl
ab-0ℕ-to-gcd-0ℕ 0ℕ (succℕ b) ()
ab-0ℕ-to-gcd-0ℕ (succℕ a) 0ℕ ()
ab-0ℕ-to-gcd-0ℕ (succℕ a) (succℕ b) ()

div-mulℕ : (d n q : ℕ) → d ∣ n → d ∣ (q ·ℕ n)
div-mulℕ d n q (k , p) = ((q ·ℕ k) , concat (mul-assocℕ q k d) (ap (q ·ℕ_) p))

gcd-dividesℕ : (a b c : ℕ) → ¬ (a +ℕ b ≡ 0ℕ) →
  ((x : ℕ) → (x ∣ a) × (x ∣ b) → x ∣ c) → gcdℕ a b ∣ c
gcd-dividesℕ a b c abne0 cdiv = result (ℕ-decidable-eq r 0ℕ)
  where
  gcd-full = ℕ-well-ordered (gcd-helper-type a b) (λ n → gcd-helper-decidable a b n) ((a +ℕ b) , gcd-helper-add a b)
  gcd-prop = proj₁ (proj₂ gcd-full) abne0
  ed = euclidean-divℕ c (gcdℕ a b) (proj₁ gcd-prop)
  q = proj₁ ed
  r = proj₁ (proj₂ ed)
  c≡qg+r = proj₁ (proj₂ (proj₂ ed))
  result : is-decidable (r ≡ 0ℕ) → gcdℕ a b ∣ c
  result (inl r≡0) = (q , concat (ap (q ·ℕ gcdℕ a b +ℕ_) (inv r≡0)) (inv c≡qg+r))
  result (inr rne0) = ex-falso (<-to-≱ r (gcdℕ a b) (proj₂ (proj₂ (proj₂ ed)))
    (proj₂ (proj₂ gcd-full) r (λ _ → (rne0 , λ x p →
      div-sum-partℕ r (q ·ℕ gcdℕ a b) x
        (tr (x ∣_) (concat c≡qg+r (add-commℕ (q ·ℕ gcdℕ a b) r)) (cdiv x p))
        (div-mulℕ x (gcdℕ a b) q (proj₂ gcd-prop x p))))))

gcd-is-gcdℕ : (a b : ℕ) → is-gcdℕ a b (gcdℕ a b)
gcd-is-gcdℕ a b x = (to , from)
  where
  gcd-full = ℕ-well-ordered (gcd-helper-type a b) (λ n → gcd-helper-decidable a b n) ((a +ℕ b) , gcd-helper-add a b)
  to : (x ∣ a) × (x ∣ b) → x ∣ gcdℕ a b
  to p = f (ℕ-decidable-eq (a +ℕ b) 0ℕ)
    where
    f : is-decidable (a +ℕ b ≡ 0ℕ) → x ∣ gcdℕ a b
    f (inl ab0) = tr (x ∣_) (inv (ab-0ℕ-to-gcd-0ℕ a b ab0)) (div-zeroℕ x)
    f (inr abne0) = proj₂ (proj₁ (proj₂ gcd-full) abne0) x p
  from : x ∣ gcdℕ a b → (x ∣ a) × (x ∣ b)
  from xg = f (ℕ-decidable-eq (a +ℕ b) 0ℕ)
    where
    f : is-decidable (a +ℕ b ≡ 0ℕ) → (x ∣ a) × (x ∣ b)
    f (inl ab0) = (tr (x ∣_) (inv (proj₁ (add-to-zeroℕ a b ab0))) (div-zeroℕ x) ,
                   tr (x ∣_) (inv (proj₂ (add-to-zeroℕ a b ab0))) (div-zeroℕ x))
    f (inr abne0) = (div-transℕ x (gcdℕ a b) a xg (gcd-dividesℕ a b a abne0 (λ x p → proj₁ p)) ,
                     div-transℕ x (gcdℕ a b) b xg (gcd-dividesℕ a b b abne0 (λ x p → proj₂ p)))

-- 8.5 Infinitude of Primes
is-proper-divisorℕ : (n d : ℕ) → Set
is-proper-divisorℕ n d = ¬ (d ≡ n) × (d ∣ n)

is-primeℕ : ℕ → Set
is-primeℕ n = (x : ℕ) → (is-proper-divisorℕ n x ↔ (x ≡ 1ℕ))

is-prime'ℕ : ℕ → Set
is-prime'ℕ n = (¬ (n ≡ 1ℕ)) × ((x : ℕ) → is-proper-divisorℕ n x → (x ≡ 1ℕ))

is-prime-to-is-prime'ℕ : (n : ℕ) → is-primeℕ n → is-prime'ℕ n
is-prime-to-is-prime'ℕ n nprime =
  ((λ n≡1 → proj₁ (proj₂ (nprime 1ℕ) refl) (inv n≡1)) , λ x div → proj₁ (nprime x) div)

is-prime'-to-is-primeℕ : (n : ℕ) → is-prime'ℕ n → is-primeℕ n
is-prime'-to-is-primeℕ n (n≢1 , f) = λ x →
  ((λ div → f x div) , λ x≡1 → (tr (λ z → ¬ (z ≡ n)) (inv x≡1) (λ p → n≢1 (inv p)) , tr (_∣ n) (inv x≡1) (one-divℕ n)))

is-prime-decidableℕ : (n : ℕ) →  is-decidable (is-primeℕ n)
is-prime-decidableℕ 0ℕ = proj₂ (iff-to-iff-decidable (is-primeℕ 0ℕ) (is-prime'ℕ 0ℕ) ((is-prime-to-is-prime'ℕ 0ℕ , is-prime'-to-is-primeℕ 0ℕ))) (with-decidable-prod (¬ (0ℕ ≡ 1ℕ)) ((x : ℕ) → is-proper-divisorℕ 0ℕ x → (x ≡ 1ℕ)) (with-decidable-arrow (0ℕ ≡ 1ℕ) (Empty) (ℕ-decidable-eq 0ℕ 1ℕ) λ x → inr id) λ nne1 → inr λ f → zero-ne-succℕ 0ℕ (inv (proj₂ (succ-injℕ 1ℕ 0ℕ) (f 2ℕ (((λ p → zero-ne-succℕ 1ℕ (inv p)) , ((0ℕ , refl))))))))
is-prime-decidableℕ (succℕ n) = proj₂ (iff-to-iff-decidable (is-primeℕ (succℕ n)) (is-prime'ℕ (succℕ n)) ((is-prime-to-is-prime'ℕ (succℕ n) , is-prime'-to-is-primeℕ (succℕ n)))) (with-decidable-prod (¬ ((succℕ n) ≡ 1ℕ)) ((x : ℕ) → is-proper-divisorℕ (succℕ n) x → (x ≡ 1ℕ)) (with-decidable-arrow ((succℕ n) ≡ 1ℕ) (Empty) (ℕ-decidable-eq (succℕ n) 1ℕ) λ x → inr id) λ nne1 → pi-arrow-decidable (is-proper-divisorℕ (succℕ n)) (λ x → x ≡ 1ℕ) (λ x → with-decidable-prod (¬ (x ≡ (succℕ n))) (x ∣ (succℕ n)) (with-decidable-arrow (x ≡ succℕ n) Empty (ℕ-decidable-eq x (succℕ n)) λ _ → inr id) λ xnesn → divℕ-decidable x (succℕ n)) (λ x → ℕ-decidable-eq x 1ℕ) (succℕ (succℕ n)) λ x div → ≤-to-<-succℕ x (succℕ n) (divℕ-to-≤ℕ x (succℕ n) (proj₂ div) λ p → zero-ne-succℕ n (inv p)))
