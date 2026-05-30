module ch08 where

open import ch07 public

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

iff-to-iff-decidable : {A B : Set} → (A ↔ B) → is-decidable A ↔ is-decidable B
iff-to-iff-decidable (A→B , B→A) = (⊎functor (A→B) (contrapositive B→A) , ⊎functor (B→A) (contrapositive A→B))

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
  proj₁ (iff-to-iff-decidable
    (Eq-Fin-to-≡Fin (succℕ k) x y , ≡Fin-to-Eq-Fin (succℕ k) x y))
    (Eq-Fin-is-decidable (succℕ k) x y)

0ℕdiv : (x : ℕ) → 0ℕ ∣ x → x ≡ 0ℕ
0ℕdiv x (0ℕ , refl) = refl
0ℕdiv x (succℕ k , refl) = refl

0ℕdiv-iff-eq0ℕ : (x : ℕ) → (0ℕ ∣ x) ↔ (x ≡ 0ℕ)
0ℕdiv-iff-eq0ℕ x = (0ℕdiv x , λ p → (0ℕ , inv p))

divℕ-decidable : (d x : ℕ) → is-decidable (d ∣ x)
divℕ-decidable 0ℕ 0ℕ = proj₂ (iff-to-iff-decidable (0ℕdiv-iff-eq0ℕ 0ℕ)) (inl refl)
divℕ-decidable 0ℕ (succℕ x) = proj₂ (iff-to-iff-decidable (0ℕdiv-iff-eq0ℕ (succℕ x))) (inr λ p → zero-ne-succℕ x (inv p))
divℕ-decidable (succℕ d) x =
  proj₁ (iff-to-iff-decidable
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

with-decidable-prod : {A B : Set} → is-decidable A → (A → is-decidable B) → is-decidable (A × B)
with-decidable-prod (inl x) f with f x
... | inl b = inl (x , b)
... | inr nb = inr λ ab → nb (proj₂ ab)
with-decidable-prod (inr x) f = inr λ p → x (proj₁ p)

with-decidable-arrow : {A B : Set} → is-decidable A → (A → is-decidable B) → is-decidable (A → B)
with-decidable-arrow (inl x) f with f x
... | inl b = inl λ a → b
... | inr nb = inr λ ab → nb (ab x)
with-decidable-arrow (inr x) f = inl λ a → ex-falso (x a)

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
  pi-type-decidable (λ n → P n → Q n) (λ n → with-decidable-arrow (dP n) (λ _ → dQ n)) m
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
gcd-helper-decidable a b n = with-decidable-arrow (with-decidable-arrow (ℕ-decidable-eq (a +ℕ b) 0ℕ) λ p → inr id) λ abne0 → with-decidable-prod (with-decidable-arrow (ℕ-decidable-eq n 0ℕ) (λ p → inr id)) λ nneq0 → pi-arrow-decidable (λ x → x ∣ a × x ∣ b) (λ x → x ∣ n) (λ x → ×-is-decidable (divℕ-decidable x a) (divℕ-decidable x b)) (λ x → divℕ-decidable x n) (succℕ (a +ℕ b)) (λ x p → ≤-to-<-succℕ x (a +ℕ b) (divℕ-to-≤ℕ x (a +ℕ b) (div-sumℕ a b x (proj₁ p) (proj₂ p)) abne0))

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
is-prime-decidableℕ 0ℕ = proj₂ (iff-to-iff-decidable ((is-prime-to-is-prime'ℕ 0ℕ , is-prime'-to-is-primeℕ 0ℕ))) (with-decidable-prod (with-decidable-arrow (ℕ-decidable-eq 0ℕ 1ℕ) λ x → inr id) λ nne1 → inr λ f → zero-ne-succℕ 0ℕ (inv (proj₂ (succ-injℕ 1ℕ 0ℕ) (f 2ℕ (((λ p → zero-ne-succℕ 1ℕ (inv p)) , ((0ℕ , refl))))))))
is-prime-decidableℕ (succℕ n) = proj₂ (iff-to-iff-decidable ((is-prime-to-is-prime'ℕ (succℕ n) , is-prime'-to-is-primeℕ (succℕ n)))) (with-decidable-prod (with-decidable-arrow (ℕ-decidable-eq (succℕ n) 1ℕ) λ x → inr id) λ nne1 → pi-arrow-decidable (is-proper-divisorℕ (succℕ n)) (λ x → x ≡ 1ℕ) (λ x → with-decidable-prod (with-decidable-arrow (ℕ-decidable-eq x (succℕ n)) λ _ → inr id) λ xnesn → divℕ-decidable x (succℕ n)) (λ x → ℕ-decidable-eq x 1ℕ) (succℕ (succℕ n)) λ x div → ≤-to-<-succℕ x (succℕ n) (divℕ-to-≤ℕ x (succℕ n) (proj₂ div) λ p → zero-ne-succℕ n (inv p)))

infinitude-helperℕ : (n m : ℕ) → Set
infinitude-helperℕ n m = (n <ℕ m) × ((x : ℕ) → (x ≤ℕ n) → ((x ∣ m) → (x ≡ 1ℕ)))

infinitude-helper-decidable : (n m : ℕ) → is-decidable (infinitude-helperℕ n m)
infinitude-helper-decidable n m = with-decidable-prod (<ℕ-is-decidable n m) λ n>m → pi-arrow-decidable (λ x → x ≤ℕ n) (λ x → x ∣ m → x ≡ 1ℕ) (λ x → ≤ℕ-is-decidable x n) (λ x → with-decidable-arrow (divℕ-decidable x m) λ xdivm → ℕ-decidable-eq x 1ℕ) (succℕ n) λ x p → ≤-to-<-succℕ x n p

not-0ℕ-div-x : (x : ℕ) → ¬ (x ≡ 0ℕ) → ¬ (0ℕ ∣ x)
not-0ℕ-div-x x xne0 0divx = xne0 (0ℕdiv x 0divx)

≤0ℕ-to-≡0ℕ : (x : ℕ) → x ≤ℕ 0ℕ → x ≡ 0ℕ
≤0ℕ-to-≡0ℕ 0ℕ p = refl

1≤-factorialℕ : (x : ℕ) → 1ℕ ≤ℕ factorialℕ x
1≤-factorialℕ 0ℕ = *
1≤-factorialℕ (succℕ n) = ≤-transℕ {succℕ 0ℕ} {succℕ n} {succℕ n ·ℕ factorialℕ n} (0ℕ-leℕ n) (≤-mul-leftℕ 1ℕ (factorialℕ n) (succℕ n) (1≤-factorialℕ n))

≤-factorialℕ : (x : ℕ) → x ≤ℕ factorialℕ x
≤-factorialℕ 0ℕ = *
≤-factorialℕ (succℕ x) = ≤-mul-leftℕ 1ℕ (factorialℕ x) (succℕ x) (1≤-factorialℕ x)

relatively-prime-factorialℕ : (n : ℕ) → infinitude-helperℕ n (factorialℕ n +ℕ 1ℕ)
relatively-prime-factorialℕ 0ℕ = (* , λ x xle0 xdiv2 → ex-falso (not-0ℕ-div-x 2ℕ (λ 2eq0 → zero-ne-succℕ 1ℕ (inv 2eq0)) (div-transℕ 0ℕ x 2ℕ (proj₂ (0ℕdiv-iff-eq0ℕ x) (≤0ℕ-to-≡0ℕ x xle0) ) xdiv2)))
relatively-prime-factorialℕ (succℕ n) = (n<fact1 , relprime)
  where
  fact≠0 : ¬ (factorialℕ (succℕ n) ≡ 0ℕ)
  fact≠0 factsneq0 = tr (succℕ n ≤ℕ_) factsneq0 (≤-factorialℕ (succℕ n))
  n<fact1 : succℕ n <ℕ factorialℕ (succℕ n) +ℕ 1ℕ
  n<fact1 = ≤-to-<-succℕ (succℕ n) (factorialℕ (succℕ n)) (divℕ-to-≤ℕ (succℕ n) (factorialℕ (succℕ n)) (factorialℕ n , mul-commℕ (factorialℕ n) (succℕ n)) fact≠0)
  relprime : (x : ℕ) → x ≤ℕ succℕ n → x ∣ (factorialℕ (succℕ n) +ℕ 1ℕ) → x ≡ 1ℕ
  relprime x x≤sn xdivfactsn1 = div-antisymℕ x 1ℕ (div-sum-partℕ 1ℕ (factorialℕ (succℕ n)) x (tr (x ∣_) (add-commℕ (factorialℕ (succℕ n)) 1ℕ) xdivfactsn1) (le-to-div-fact (succℕ n) x xne0 x≤sn)) (one-divℕ x)
    where
    xne0 : ¬ (x ≡ 0ℕ)
    xne0 x≡0 = zero-ne-succℕ (factorialℕ (succℕ n)) (inv (0ℕdiv (factorialℕ (succℕ n) +ℕ 1ℕ) (tr (_∣ (factorialℕ (succℕ n) +ℕ 1ℕ)) x≡0 xdivfactsn1)))

n-≤-prime : (n : ℕ) → Σ ℕ (λ p → (is-primeℕ p) × (n <ℕ p))
n-≤-prime 0ℕ = (2ℕ , (2-is-primeℕ , *))
  where
  2≠1 : ¬ (2ℕ ≡ 1ℕ)
  2≠1 p = zero-ne-succℕ 0ℕ (inv (proj₂ (succ-injℕ 1ℕ 0ℕ) p))
  2-proper-divℕ : (x : ℕ) → is-proper-divisorℕ 2ℕ x → x ≡ 1ℕ
  2-proper-divℕ 0ℕ (_ , div) = ex-falso (zero-ne-succℕ 1ℕ (inv (0ℕdiv 2ℕ div)))
  2-proper-divℕ (succℕ 0ℕ) _ = refl
  2-proper-divℕ (succℕ (succℕ 0ℕ)) (ne , _) = ex-falso (ne refl)
  2-proper-divℕ (succℕ (succℕ (succℕ x))) (_ , div) = ex-falso (divℕ-to-≤ℕ (succℕ (succℕ (succℕ x))) 2ℕ div (λ p → zero-ne-succℕ 1ℕ (inv p)))
  2-is-primeℕ : is-primeℕ 2ℕ
  2-is-primeℕ = is-prime'-to-is-primeℕ 2ℕ (2≠1 , 2-proper-divℕ)
n-≤-prime (succℕ n) = (m , (m-is-prime , n<m))
  where
  well-ord = ℕ-well-ordered (infinitude-helperℕ (succℕ n)) (infinitude-helper-decidable (succℕ n)) ((factorialℕ (succℕ n) +ℕ 1ℕ) , relatively-prime-factorialℕ (succℕ n))
  m = proj₁ well-ord
  m-R = proj₁ (proj₂ well-ord)
  m-lb = proj₂ (proj₂ well-ord)
  n<m = proj₁ m-R
  m-relprime = proj₂ m-R
  m≠0 : ¬ (m ≡ 0ℕ)
  m≠0 m≡0 = tr (succℕ n <ℕ_) m≡0 n<m
  m≠1 : ¬ (m ≡ 1ℕ)
  m≠1 m≡1 = tr (succℕ (succℕ n) ≤ℕ_) m≡1 (<-to-succ-≤ℕ (succℕ n) m n<m)
  prime-forward : (x : ℕ) → is-proper-divisorℕ m x → x ≡ 1ℕ
  prime-forward x (x≠m , x∣m) = m-relprime x x≤sn x∣m
    where
    x≤m = divℕ-to-≤ℕ x m x∣m m≠0
    x<m : x <ℕ m
    x<m = ind⊎ {P = λ _ → x <ℕ m} (λ z → z) (λ m≤x → ex-falso (x≠m (≤-antisymℕ x m x≤m m≤x))) (<-or-≤ℕ x m)
    ¬Rnx : ¬ (infinitude-helperℕ (succℕ n) x)
    ¬Rnx Rnx = <-to-≱ x m x<m (m-lb x Rnx)
    second : (y : ℕ) → y ≤ℕ succℕ n → y ∣ x → y ≡ 1ℕ
    second y y≤sn y∣x = m-relprime y y≤sn (div-transℕ y x m y∣x x∣m)
    x≤sn : x ≤ℕ succℕ n
    x≤sn = ind⊎ {P = λ _ → x ≤ℕ succℕ n} (λ sn<x → ex-falso (¬Rnx (sn<x , second))) (λ z → z) (<-or-≤ℕ (succℕ n) x)
  m-is-prime : is-primeℕ m
  m-is-prime = is-prime'-to-is-primeℕ m (m≠1 , prime-forward)

booleanisation : {A : Set} → is-decidable A → 𝟚
booleanisation (inl a) = true
booleanisation (inr f) = false

reflect : {A : Set} → (d : is-decidable A) → booleanisation d ≡ true → A
reflect (inl a) refl = a

-- Exercises
-- 8.1

Goldbach : (n : ℕ) → Set
Goldbach n = (2ℕ <ℕ n) → (2ℕ ∣ n) → Σ ℕ (λ p → Σ ℕ (λ q → (n ≡ p +ℕ q) × (is-primeℕ p) × (is-primeℕ q)))

Twin-Prime : Set
Twin-Prime = Σ ℕ (λ p → (Σ ℕ (λ q → ((is-primeℕ p) × (is-primeℕ q) × (p +ℕ 2ℕ ≡ q)))))

iterate : {A : Set} → (A → A) → ℕ → A → A
iterate f 0ℕ x = x
iterate f (succℕ n) x = f (iterate f n x)

--8.2

is-decidable-idempotent : {P : Set} → is-decidable (is-decidable P) → is-decidable P
is-decidable-idempotent (inl (inl x)) = inl x
is-decidable-idempotent (inl (inr x)) = inr x
is-decidable-idempotent (inr ndp) = inr (λ p → ndp (inl p))

--8.3
ex-8-3 : (k : ℕ) → (P : Fin k → Set)→ ((x : Fin k) → is-decidable (P x)) → ¬ ((x : Fin k) → P x) → Σ (Fin k) (λ x → ¬ (P x))
ex-8-3 0ℕ P f nxPx = ex-falso (nxPx (λ x → indEmpty {P = λ _ → P x} x))
ex-8-3 (succℕ k) P f nxPx with f (inr *)
... | inl p = (inl (proj₁ ih) , proj₂ ih)
  where
  ih = ex-8-3 k (λ x → P (inl x)) (λ x → f (inl x)) (λ g → nxPx (ind⊎ {P = λ z → P z} g (λ { * → p })))
... | inr np = (inr * , np)

--8.4
primeℕ : ℕ → ℕ
primeℕ 0ℕ = 2ℕ
primeℕ (succℕ n) = proj₁ (ℕ-well-ordered (λ x → (is-primeℕ x) × (primeℕ n <ℕ x)) (λ x → with-decidable-prod (is-prime-decidableℕ x) λ xprime → <ℕ-is-decidable (primeℕ n) x) (n-≤-prime (primeℕ n)))

prime-countingℕ : ℕ → ℕ
prime-countingℕ 0ℕ = 0ℕ
prime-countingℕ (succℕ n) with is-prime-decidableℕ (succℕ n)
... | inl nprime = prime-countingℕ n +ℕ 1ℕ
... | inr nnotprime = prime-countingℕ n

prime-iff-trivial-divℕ  : (n : ℕ) → (is-primeℕ n) ↔ ((2ℕ ≤ℕ n) × ((x : ℕ) → ((x ∣ n) → (x ≡ 1ℕ) ⊎ (x ≡ n))))
prime-iff-trivial-divℕ  n = (to n , from n)
  where
  to : (n : ℕ) → (is-primeℕ n) → ((2ℕ ≤ℕ n) × ((x : ℕ) → ((x ∣ n) → (x ≡ 1ℕ) ⊎ (x ≡ n))))
  to 0ℕ nprime = ex-falso (zero-ne-succℕ 0ℕ (inv (proj₂ (succ-injℕ 1ℕ 0ℕ) (proj₁ (nprime 2ℕ) ((λ p → zero-ne-succℕ 1ℕ (inv p)) , div-zeroℕ 2ℕ)))))
  to (succℕ 0ℕ) nprime = ex-falso (proj₁ (proj₂ (nprime 1ℕ) refl) refl)
  to (succℕ (succℕ k)) nprime = (0ℕ-leℕ k , divisors)
    where
    divisors : (x : ℕ) → x ∣ succℕ (succℕ k) → (x ≡ 1ℕ) ⊎ (x ≡ succℕ (succℕ k))
    divisors x xdivn with ℕ-decidable-eq x (succℕ (succℕ k))
    ... | inl x≡n = inr x≡n
    ... | inr x≠n = inl (proj₁ (nprime x) (x≠n , xdivn))
  from : (n : ℕ) → ((2ℕ ≤ℕ n) × ((x : ℕ) → ((x ∣ n) → (x ≡ 1ℕ) ⊎ (x ≡ n)))) → (is-primeℕ n)
  from n (2≤n , f) x = (forward , backward)
    where
    forward : is-proper-divisorℕ n x → x ≡ 1ℕ
    forward (x≠n , x∣n) = ind⊎ {P = λ _ → x ≡ 1ℕ} (λ z → z) (λ x≡n → ex-falso (x≠n x≡n)) (f x x∣n)
    n≠1 : ¬ (n ≡ 1ℕ)
    n≠1 n≡1 = tr (2ℕ ≤ℕ_) n≡1 2≤n
    backward : x ≡ 1ℕ → is-proper-divisorℕ n x
    backward x≡1 = (tr (λ z → ¬ (z ≡ n)) (inv x≡1) (λ p → n≠1 (inv p)) , tr (_∣ n) (inv x≡1) (one-divℕ n))

ex-8-6i : (A B : Set) → ((A → has-decidable-eq B) × (B → has-decidable-eq A)) ↔ (has-decidable-eq (A × B))
ex-8-6i A B = (to , from)
  where
  to : (A → has-decidable-eq B) × (B → has-decidable-eq A) → (has-decidable-eq (A × B))
  to (AdB , BdA) (a , b) (x , y) with BdA b a x | AdB a b y
  ... | inl refl | inl refl = inl refl
  ... | inl refl | inr q = inr λ abeqay → q (ap proj₂ abeqay)
  ... | inr p | inl refl = inr λ eq → p (ap proj₁ eq)
  ... | inr p | inr q = inr λ eq → p (ap proj₁ eq)

  from : (has-decidable-eq (A × B)) → ((A → has-decidable-eq B) × (B → has-decidable-eq A))
  from dAB = ((λ a b b' → ⊎functor (ap proj₂) (λ ne eq → ne (ap (a ,_) eq)) (dAB (a , b) (a , b'))) ,
    (λ b a a' → ⊎functor (ap proj₁) (λ ne eq → ne (ap (_, b) eq)) (dAB (a , b) (a' , b)))) 

ex-8-6ii : {A B : Set} → (has-decidable-eq A) → (has-decidable-eq B) → has-decidable-eq (A × B)
ex-8-6ii {A} {B} dA dB = proj₁ (ex-8-6i A B) (((λ _ → dB) , λ _ → dA))

--8.7
Eq⊎ : {A B : Set} → A ⊎ B → A ⊎ B → Set
Eq⊎ (inl x) (inl y) = x ≡ y
Eq⊎ (inl x) (inr y) = 𝟘
Eq⊎ (inr x) (inl y) = 𝟘
Eq⊎ (inr x) (inr y) = x ≡ y

≡-to-Eq⊎ : {A B : Set} → (x y : A ⊎ B) → x ≡ y → Eq⊎ x y
≡-to-Eq⊎ (inl x) y refl = refl
≡-to-Eq⊎ (inr x) y refl = refl

Eq⊎-to-≡ : {A B : Set} → (x y : A ⊎ B) → Eq⊎ x y → x ≡ y
Eq⊎-to-≡ (inl x) (inl _) refl = refl
Eq⊎-to-≡ (inl x) (inr x₁) ()
Eq⊎-to-≡ (inr x) (inl x₁) ()
Eq⊎-to-≡ (inr x) (inr _) refl = refl

ex-8-7-b : {A B : Set} → (has-decidable-eq A) → (has-decidable-eq B) → (has-decidable-eq (A ⊎ B))
ex-8-7-b {A} {B} dA dB (inl a) (inl aa) = ⊎functor (ap inl) (λ ne eq → ne (≡-to-Eq⊎ (inl a) (inl aa) eq)) (dA a aa)
ex-8-7-b {A} {B} dA dB (inl a) (inr b) = inr (λ eq → ≡-to-Eq⊎ (inl a) (inr b) eq)
ex-8-7-b {A} {B} dA dB (inr b) (inl a) = inr λ eq → ≡-to-Eq⊎ (inr b) (inl a) eq
ex-8-7-b {A} {B} dA dB (inr b) (inr bb) = ⊎functor (ap inr) (λ ne eq → ne (≡-to-Eq⊎ (inr b) (inr bb) eq )) (dB b bb)


-- Our definition of ℤ is different to Rijke's so we take a different approach to the book, following a similar style to ℕ
Eq-ℤ : ℤ → ℤ → Set
Eq-ℤ 0ℤ 0ℤ = 𝟙
Eq-ℤ 0ℤ (in-neg _) = 𝟘
Eq-ℤ 0ℤ (in-pos _) = 𝟘
Eq-ℤ (in-neg _) 0ℤ = 𝟘
Eq-ℤ (in-neg n) (in-neg m) = n ≡ m
Eq-ℤ (in-neg _) (in-pos _) = 𝟘
Eq-ℤ (in-pos _) 0ℤ = 𝟘
Eq-ℤ (in-pos _) (in-neg _) = 𝟘
Eq-ℤ (in-pos n) (in-pos m) = n ≡ m

≡-to-Eq-ℤ : (x y : ℤ) → x ≡ y → Eq-ℤ x y
≡-to-Eq-ℤ 0ℤ .0ℤ refl = *
≡-to-Eq-ℤ (in-neg n) .(in-neg n) refl = refl
≡-to-Eq-ℤ (in-pos n) .(in-pos n) refl = refl

Eq-ℤ-to-≡ : (x y : ℤ) → Eq-ℤ x y → x ≡ y
Eq-ℤ-to-≡ 0ℤ 0ℤ _ = refl
Eq-ℤ-to-≡ (in-neg n) (in-neg m) p = ap in-neg p
Eq-ℤ-to-≡ (in-pos n) (in-pos m) p = ap in-pos p

ℤ-decidable-eq : has-decidable-eq ℤ
ℤ-decidable-eq 0ℤ 0ℤ = inl refl
ℤ-decidable-eq 0ℤ (in-neg _) = inr (≡-to-Eq-ℤ 0ℤ (in-neg _))
ℤ-decidable-eq 0ℤ (in-pos _) = inr (≡-to-Eq-ℤ 0ℤ (in-pos _))
ℤ-decidable-eq (in-neg _) 0ℤ = inr (≡-to-Eq-ℤ (in-neg _) 0ℤ)
ℤ-decidable-eq (in-neg n) (in-neg m) =
  ⊎functor (ap in-neg) (λ ne eq → ne (≡-to-Eq-ℤ (in-neg n) (in-neg m) eq)) (ℕ-decidable-eq n m)
ℤ-decidable-eq (in-neg _) (in-pos _) = inr (≡-to-Eq-ℤ (in-neg _) (in-pos _))
ℤ-decidable-eq (in-pos _) 0ℤ = inr (≡-to-Eq-ℤ (in-pos _) 0ℤ)
ℤ-decidable-eq (in-pos _) (in-neg _) = inr (≡-to-Eq-ℤ (in-pos _) (in-neg _))
ℤ-decidable-eq (in-pos n) (in-pos m) =
  ⊎functor (ap in-pos) (λ ne eq → ne (≡-to-Eq-ℤ (in-pos n) (in-pos m) eq)) (ℕ-decidable-eq n m)

-- Exercise 8.8
-- (i) → (ii) → (iii)
ex-8-8-a : {A : Set} → {B : A → Set} →
  has-decidable-eq A →
  ((x : A) → has-decidable-eq (B x)) →
  has-decidable-eq (Σ A B)
ex-8-8-a dA dB (x , y) (a , b) with dA x a
... | inr p = inr λ eq → p (ap proj₁ eq)
... | inl refl with dB x y b
... | inl refl = inl refl
... | inr yneqb = inr λ {refl → yneqb refl}


-- (i) → (iii) → (ii)
ex-8-8-b : {A : Set} → {B : A → Set} →
  has-decidable-eq A →
  has-decidable-eq (Σ A B) →
  ((x : A) → has-decidable-eq (B x))
ex-8-8-b dA dΣ x b b' with dΣ (x , b) (x , b')
... | inl refl = inl refl
... | inr np = inr λ {refl → np refl}

--section of B + (ii) + (iii) → (i)
ex-8-8-c : {A : Set} → {B : A → Set} →
  ((x : A) → B x) →
  ((x : A) → has-decidable-eq (B x)) →
  has-decidable-eq (Σ A B) →
  has-decidable-eq A
ex-8-8-c sec dB dΣ a a' with dΣ (a , sec a) (a' , sec a')
... | inl refl = inl refl
... | inr np = inr λ {refl → np refl}

-- 8.9
ex-8-9a : (k : ℕ) → (B : Fin k → Set) → ((x : Fin k) → is-decidable (B x)) → is-decidable ((x : Fin k) → B x)
ex-8-9a 0ℕ B xdBx = inl λ ()
ex-8-9a (succℕ k) B xdBx with xdBx (inr *)
... | inr x = inr λ y → x (y (inr *))
... | inl x with ex-8-9a k (λ n → B (inl n)) (λ n → xdBx (inl n))
... | inl y = inl λ {(inl z) → y z ; (inr *) → x}
... | inr y = inr λ f → y λ z → f (inl z)

-- ex-8-9b is skipped

-- 8.10
bounded-Σℕ-is-decidable : (P : ℕ → Set) → ((n : ℕ) → is-decidable (P n)) → (u : ℕ) → is-upper-bound P u → is-decidable (Σ ℕ (λ n → P n))
bounded-Σℕ-is-decidable P ndPn 0ℕ uub with ndPn 0ℕ
... | inl p0 = inl (0ℕ , p0)
... | inr np0 = inr (λ { (n , pn) → np0 (tr P (≤-antisymℕ n 0ℕ (uub n pn) (0ℕ-leℕ n)) pn) })
bounded-Σℕ-is-decidable P dP (succℕ u') ub with dP (succℕ u')                                
... | inl p = inl (succℕ u' , p)
... | inr np = bounded-Σℕ-is-decidable P dP u'
  (λ n pn → ind⊎ {P = λ _ → n ≤ℕ u'} (λ n<su → <-to-succ-≤ℕ n (succℕ u') n<su) (λ su≤n → ex-falso (np (tr P (≤-antisymℕ n (succℕ u') (ub n pn) su≤n) pn))) (<-or-≤ℕ n (succℕ u')))

upper-bound-to-maxℕ : (P : ℕ → Set) → ((n : ℕ) → is-decidable (P n)) → (u : ℕ) → is-upper-bound P u → (Σ ℕ (λ n → P n)) → (Σ ℕ (λ n → (P n × is-upper-bound P n)))
upper-bound-to-maxℕ P ndPn 0ℕ uub ΣℕPn with ndPn 0ℕ
... | inl p0 = (0ℕ , (p0 , uub))
... | inr np0 = (ex-falso (np0 ((tr P (≤-antisymℕ (proj₁ ΣℕPn) 0ℕ (uub (proj₁ ΣℕPn) (proj₂ ΣℕPn)) (0ℕ-leℕ (proj₁ ΣℕPn))) (proj₂ ΣℕPn)))))
upper-bound-to-maxℕ P ndPn (succℕ u) uub ΣℕPn with ndPn (succℕ u)
... | inl x = (succℕ u , (x , uub))
... | inr x = upper-bound-to-maxℕ P ndPn u
  (λ n pn → ind⊎ {P = λ _ → n ≤ℕ u}
    (λ n<su → <-to-succ-≤ℕ n (succℕ u) n<su)
    (λ su≤n → ex-falso (x (tr P (≤-antisymℕ n (succℕ u) (uub n pn) su≤n) pn)))
    (<-or-≤ℕ n (succℕ u)))
  ΣℕPn

common-divisor : ℕ → ℕ → ℕ → Set
common-divisor a b x = (x ∣ a) × (x ∣ b)

common-divisor-decidable : (a b x : ℕ) → is-decidable (common-divisor a b x)
common-divisor-decidable a b x = ×-is-decidable (divℕ-decidable x a) (divℕ-decidable x b)

common-divisor-upper-bound : (a b : ℕ) → ¬ (a +ℕ b ≡ 0ℕ) →
  is-upper-bound (common-divisor a b) (a +ℕ b)
common-divisor-upper-bound a b abne0 x (xa , xb) =
  divℕ-to-≤ℕ x (a +ℕ b) (div-sumℕ a b x xa xb) abne0

gcd'ℕ : ℕ → ℕ → ℕ
gcd'ℕ a b with ℕ-decidable-eq (a +ℕ b) 0ℕ
... | inl _ = 0ℕ
... | inr abne0 = proj₁ (upper-bound-to-maxℕ
  (common-divisor a b)
  (common-divisor-decidable a b)
  (a +ℕ b)
  (common-divisor-upper-bound a b abne0)
  (1ℕ , (one-divℕ a , one-divℕ b)))

gcd'-is-gcdℕ : (a b : ℕ) → is-gcdℕ a b (gcd'ℕ a b)
gcd'-is-gcdℕ a b with ℕ-decidable-eq (a +ℕ b) 0ℕ
... | inl ab0 = λ x → (to x , from x)
  where
  a0 = proj₁ (add-to-zeroℕ a b ab0)
  b0 = proj₂ (add-to-zeroℕ a b ab0)
  to : (x : ℕ) → (x ∣ a) × (x ∣ b) → x ∣ 0ℕ
  to x _ = div-zeroℕ x
  from : (x : ℕ) → x ∣ 0ℕ → (x ∣ a) × (x ∣ b)
  from x _ = (tr (x ∣_) (inv a0) (div-zeroℕ x) , tr (x ∣_) (inv b0) (div-zeroℕ x))
... | inr abne0 = λ x → (to x , from x)
  where
  result = upper-bound-to-maxℕ
    (common-divisor a b)
    (common-divisor-decidable a b)
    (a +ℕ b)
    (common-divisor-upper-bound a b abne0)
    (1ℕ , (one-divℕ a , one-divℕ b))
  d = proj₁ result
  d-div : common-divisor a b d
  d-div = proj₁ (proj₂ result)
  d-ub : is-upper-bound (common-divisor a b) d
  d-ub = proj₂ (proj₂ result)
  g-div-a : gcdℕ a b ∣ a
  g-div-a = proj₁ (proj₂ (gcd-is-gcdℕ a b (gcdℕ a b)) (div-rflℕ (gcdℕ a b)))
  g-div-b : gcdℕ a b ∣ b
  g-div-b = proj₂ (proj₂ (gcd-is-gcdℕ a b (gcdℕ a b)) (div-rflℕ (gcdℕ a b)))
  d≤g : d ≤ℕ gcdℕ a b
  d≤g = divℕ-to-≤ℕ d (gcdℕ a b)
    (proj₁ (gcd-is-gcdℕ a b d) d-div)
    (λ g0 → abne0 (gcdℕ-0-to-ab-0ℕ a b g0))
  g≤d : gcdℕ a b ≤ℕ d
  g≤d = d-ub (gcdℕ a b) (g-div-a , g-div-b)
  d≡g : d ≡ gcdℕ a b
  d≡g = ≤-antisymℕ d (gcdℕ a b) d≤g g≤d
  from : (x : ℕ) → x ∣ d → (x ∣ a) × (x ∣ b)
  from x xd = (div-transℕ x d a xd (proj₁ d-div) , div-transℕ x d b xd (proj₂ d-div))
  to : (x : ℕ) → (x ∣ a) × (x ∣ b) → x ∣ d
  to x p = tr (x ∣_) (inv d≡g) (proj₁ (gcd-is-gcdℕ a b x) p)

-- 8.11
Bezout-typeℕ : (x y z : ℕ) → Set
Bezout-typeℕ x y z = Σ ℕ (λ k → Σ ℕ (λ l → distℕ (k ·ℕ x) (l ·ℕ y) ≡ z))

-- Helpers for 8.11 (a)

<ℕ-to-≤ℕ : (m n : ℕ) → m <ℕ n → m ≤ℕ n
<ℕ-to-≤ℕ 0ℕ 0ℕ ()
<ℕ-to-≤ℕ 0ℕ (succℕ n) _ = *
<ℕ-to-≤ℕ (succℕ m) 0ℕ ()
<ℕ-to-≤ℕ (succℕ m) (succℕ n) p = <ℕ-to-≤ℕ m n p

dist-zero-leftℕ : (m : ℕ) → distℕ 0ℕ m ≡ m
dist-zero-leftℕ m = concat (dist-symmℕ 0ℕ m) (dist-zero-rightℕ m)

-- If l ≡ q·x + r, then x ∣ (l·y + z) implies x ∣ (r·y + z).
div-reduce-lℕ : (x y z l q r : ℕ) → l ≡ q ·ℕ x +ℕ r →
                x ∣ (l ·ℕ y +ℕ z) → x ∣ (r ·ℕ y +ℕ z)
div-reduce-lℕ x y z l q r leq xdiv =
  div-sum-partℕ (r ·ℕ y +ℕ z) ((q ·ℕ x) ·ℕ y) x
    (tr (x ∣_) expand xdiv)
    ((q ·ℕ y) ,
       concat (mul-assocℕ q y x)
      (concat (ap (λ w → q ·ℕ w) (mul-commℕ y x))
              (inv (mul-assocℕ q x y))))
  where
    expand : l ·ℕ y +ℕ z ≡ (r ·ℕ y +ℕ z) +ℕ (q ·ℕ x) ·ℕ y
    expand = concat (ap (λ w → w ·ℕ y +ℕ z) leq)
            (concat (ap (λ w → w +ℕ z) (right-distribℕ (q ·ℕ x) r y))
            (concat (add-assocℕ ((q ·ℕ x) ·ℕ y) (r ·ℕ y) z)
                    (add-commℕ ((q ·ℕ x) ·ℕ y) (r ·ℕ y +ℕ z))))

-- Bounded versions of the Bezout witness
Bezout-left-boundedℕ : (x y z : ℕ) → Set
Bezout-left-boundedℕ x y z = Σ ℕ (λ l → (l <ℕ x) × (x ∣ (l ·ℕ y +ℕ z)))

Bezout-right-boundedℕ : (x y z : ℕ) → Set
Bezout-right-boundedℕ x y z = Σ ℕ (λ k → (k <ℕ y) × (y ∣ (k ·ℕ x +ℕ z)))

Bezout-left-bounded-decℕ : (x y z : ℕ) → is-decidable (Bezout-left-boundedℕ x y z)
Bezout-left-bounded-decℕ x y z =
  bounded-Σℕ-is-decidable
    (λ l → (l <ℕ x) × (x ∣ (l ·ℕ y +ℕ z)))
    (λ l → ×-is-decidable (<ℕ-is-decidable l x) (divℕ-decidable x (l ·ℕ y +ℕ z)))
    x
    (λ l p → <ℕ-to-≤ℕ l x (proj₁ p))

Bezout-right-bounded-decℕ : (x y z : ℕ) → is-decidable (Bezout-right-boundedℕ x y z)
Bezout-right-bounded-decℕ x y z =
  bounded-Σℕ-is-decidable
    (λ k → (k <ℕ y) × (y ∣ (k ·ℕ x +ℕ z)))
    (λ k → ×-is-decidable (<ℕ-is-decidable k y) (divℕ-decidable y (k ·ℕ x +ℕ z)))
    y
    (λ k p → <ℕ-to-≤ℕ k y (proj₁ p))

-- A bounded solution gives a Bezout solution
Bezout-left-to-typeℕ : (x y z : ℕ) → Bezout-left-boundedℕ x y z → Bezout-typeℕ x y z
Bezout-left-to-typeℕ x y z (l , (l<x , (k , kx-eq))) =
  (k , (l ,
    concat (ap (λ w → distℕ w (l ·ℕ y)) kx-eq)
   (concat (ap (λ w → distℕ w (l ·ℕ y)) (add-commℕ (l ·ℕ y) z))
           (dist-add-rightℕ z (l ·ℕ y)))))

Bezout-right-to-typeℕ : (x y z : ℕ) → Bezout-right-boundedℕ x y z → Bezout-typeℕ x y z
Bezout-right-to-typeℕ x y z (k , (k<y , (l , ly-eq))) =
  (k , (l ,
    concat (ap (λ w → distℕ (k ·ℕ x) w) ly-eq)
   (concat (dist-symmℕ (k ·ℕ x) (k ·ℕ x +ℕ z))
   (concat (ap (λ w → distℕ w (k ·ℕ x)) (add-commℕ (k ·ℕ x) z))
           (dist-add-rightℕ z (k ·ℕ x))))))
-- For x, y ≥ 1, any Bezout solution reduces to a bounded one
Bezout-type-to-boundedℕ : (x y z : ℕ) → ¬ (x ≡ 0ℕ) → ¬ (y ≡ 0ℕ) →
                          Bezout-typeℕ x y z →
                          Bezout-left-boundedℕ x y z ⊎ Bezout-right-boundedℕ x y z
Bezout-type-to-boundedℕ x y z xne yne (k , (l , dist-eq)) with ≤-dichotomyℕ (l ·ℕ y) (k ·ℕ x)
... | inl ly≤kx =
  let kx-eq : k ·ℕ x ≡ l ·ℕ y +ℕ z
      kx-eq = concat (inv (add-distℕ (l ·ℕ y) (k ·ℕ x) ly≤kx))
                     (ap (λ w → l ·ℕ y +ℕ w) (concat (dist-symmℕ (l ·ℕ y) (k ·ℕ x)) dist-eq))
      euclid = euclidean-divℕ l x xne
      q = proj₁ euclid
      r = proj₁ (proj₂ euclid)
      leq = proj₁ (proj₂ (proj₂ euclid))
      r<x = proj₂ (proj₂ (proj₂ euclid))
  in inl (r , (r<x , div-reduce-lℕ x y z l q r leq (k , kx-eq)))
... | inr kx≤ly =
  let ly-eq : l ·ℕ y ≡ k ·ℕ x +ℕ z
      ly-eq = concat (inv (add-distℕ (k ·ℕ x) (l ·ℕ y) kx≤ly))
                     (ap (λ w → k ·ℕ x +ℕ w) dist-eq)
      euclid = euclidean-divℕ k y yne
      q = proj₁ euclid
      r = proj₁ (proj₂ euclid)
      keq = proj₁ (proj₂ (proj₂ euclid))
      r<y = proj₂ (proj₂ (proj₂ euclid))
  in inr (r , (r<y , div-reduce-lℕ y x z k q r keq (l , ly-eq)))

-- Main theorem: decidability of Bezout-typeℕ
Bezout-type-decℕ : (x y z : ℕ) → is-decidable (Bezout-typeℕ x y z)
Bezout-type-decℕ 0ℕ y z with divℕ-decidable y z
... | inl (l , ly≡z) = inl (0ℕ , (l , concat (dist-zero-leftℕ (l ·ℕ y)) ly≡z))
... | inr ne = inr λ { (k , (l , eq)) →
                 ne (l , concat (inv (dist-zero-leftℕ (l ·ℕ y))) eq) }
Bezout-type-decℕ (succℕ x') 0ℕ z with divℕ-decidable (succℕ x') z
... | inl (k , kx≡z) = inl (k , (0ℕ , kx≡z))
... | inr ne = inr λ { (k , (l , eq)) → ne (k , eq) }
Bezout-type-decℕ (succℕ x') (succℕ y') z =
  aux (Bezout-left-bounded-decℕ (succℕ x') (succℕ y') z)
      (Bezout-right-bounded-decℕ (succℕ x') (succℕ y') z)
  where
    aux : is-decidable (Bezout-left-boundedℕ (succℕ x') (succℕ y') z) →
          is-decidable (Bezout-right-boundedℕ (succℕ x') (succℕ y') z) →
          is-decidable (Bezout-typeℕ (succℕ x') (succℕ y') z)
    aux (inl b) _ = inl (Bezout-left-to-typeℕ (succℕ x') (succℕ y') z b)
    aux (inr _) (inl b) = inl (Bezout-right-to-typeℕ (succℕ x') (succℕ y') z b)
    aux (inr nl) (inr nr) = inr λ bez →
      ind⊎ {P = λ _ → 𝟘} nl nr
        (Bezout-type-to-boundedℕ (succℕ x') (succℕ y') z (λ ()) (λ ()) bez)

dist-add-cancelℕ : (a b c : ℕ) → distℕ (a +ℕ c) (b +ℕ c) ≡ distℕ a b
dist-add-cancelℕ a b 0ℕ = refl
dist-add-cancelℕ a b (succℕ c) = dist-add-cancelℕ a b c

Bezout-identity-auxℕ : (n x y : ℕ) → x ≤ℕ n → Σ ℕ (λ d → is-gcdℕ x y d × Bezout-typeℕ x y d)
Bezout-identity-auxℕ n 0ℕ y _ = (y , ((λ z → (proj₂ , λ zy → (div-zeroℕ z , zy))) , (0ℕ , (1ℕ , concat (ap (distℕ 0ℕ) (one-mulℕ y)) (dist-zero-leftℕ y)))))
Bezout-identity-auxℕ 0ℕ (succℕ x') y ()
Bezout-identity-auxℕ (succℕ n) (succℕ x') y x≤n = (d , (gcd-xy , bez))
  where
  ed = euclidean-divℕ y (succℕ x') (λ ())
  q = proj₁ ed
  r = proj₁ (proj₂ ed)
  yeq = proj₁ (proj₂ (proj₂ ed))
  r<x = proj₂ (proj₂ (proj₂ ed))
  r≤n : r ≤ℕ n
  r≤n = ≤-transℕ {r} {x'} {n} (<-to-succ-≤ℕ r (succℕ x') r<x) x≤n
  rec = Bezout-identity-auxℕ n r (succℕ x') r≤n
  d = proj₁ rec
  gcd-rx = proj₁ (proj₂ rec)
  k = proj₁ (proj₂ (proj₂ rec))
  l = proj₁ (proj₂ (proj₂ (proj₂ rec)))
  dist-eq = proj₂ (proj₂ (proj₂ (proj₂ rec)))
  c = k ·ℕ (q ·ℕ succℕ x')
  gcd-xy : is-gcdℕ (succℕ x') y d
  gcd-xy z = (to , from)
    where
    to : (z ∣ succℕ x') × (z ∣ y) → z ∣ d
    to (zx , zy) = proj₁ (gcd-rx z)
      (div-sum-partℕ r (q ·ℕ succℕ x') z
        (tr (z ∣_) (concat yeq (add-commℕ (q ·ℕ succℕ x') r)) zy)
        (div-mulℕ z (succℕ x') q zx) ,
       zx)
    from : z ∣ d → (z ∣ succℕ x') × (z ∣ y)
    from zd = (proj₂ p , tr (z ∣_) (inv yeq) (div-sumℕ (q ·ℕ succℕ x') r z (div-mulℕ z (succℕ x') q (proj₂ p)) (proj₁ p)))
      where p = proj₂ (gcd-rx z) zd
  bezout-proof : distℕ ((l +ℕ k ·ℕ q) ·ℕ succℕ x') (k ·ℕ y) ≡ d
  bezout-proof =
    concat (ap (λ w → distℕ w (k ·ℕ y)) (concat (right-distribℕ l (k ·ℕ q) (succℕ x')) (ap (l ·ℕ succℕ x' +ℕ_) (mul-assocℕ k q (succℕ x')))))
    (concat (ap (distℕ (l ·ℕ succℕ x' +ℕ c)) (concat (ap (k ·ℕ_) yeq) (concat (left-distribℕ k (q ·ℕ succℕ x') r) (add-commℕ c (k ·ℕ r)))))
    (concat (dist-add-cancelℕ (l ·ℕ succℕ x') (k ·ℕ r) c)
    (concat (dist-symmℕ (l ·ℕ succℕ x') (k ·ℕ r)) dist-eq)))
  k' = l +ℕ k ·ℕ q
  bez : Bezout-typeℕ (succℕ x') y d
  bez = (k' , (k , bezout-proof))

Bezout-identityℕ : (x y : ℕ) → Σ ℕ (λ k → Σ ℕ (λ l → distℕ (k ·ℕ x) (l ·ℕ y) ≡ gcdℕ x y))
Bezout-identityℕ x y = (proj₁ bez , (proj₁ (proj₂ bez) , concat (proj₂ (proj₂ bez)) (gcd-uniqueℕ x y d (gcdℕ x y) gcd-xy (gcd-is-gcdℕ x y))))
  where
  aux = Bezout-identity-auxℕ x x y (≤-rflℕ x)
  d = proj₁ aux
  gcd-xy = proj₁ (proj₂ aux)
  bez = proj₂ (proj₂ aux)

has-prime-factorℕ : (n : ℕ) → 2ℕ ≤ℕ n → Σ ℕ (λ p → (is-primeℕ p) × (p ∣ n) × ((d : ℕ) → 2ℕ ≤ℕ d → d ∣ n → p ≤ℕ d))
has-prime-factorℕ n 2len = m , (m-is-prime , (mdivn , (λ d 2≤d d∣n → mlb d (2≤d , d∣n))))
  where
  wo = ℕ-well-ordered (λ m → (2ℕ ≤ℕ m) × (m ∣ n)) (λ x → with-decidable-prod (≤ℕ-is-decidable 2ℕ x) λ 2lex → divℕ-decidable x n) (n , (2len , (1ℕ , one-mulℕ n)))
  m = proj₁ wo
  2≤m = proj₁ (proj₁ (proj₂ wo))
  mdivn = proj₂ (proj₁ (proj₂ wo))
  mlb = proj₂ (proj₂ wo)
  m≠0 : ¬ (m ≡ 0ℕ)
  m≠0 meq0 = tr (2ℕ ≤ℕ_) meq0 2≤m
  m-is-prime : is-primeℕ m
  m-is-prime = is-prime'-to-is-primeℕ m ((λ meq1 → tr (2ℕ ≤ℕ_) meq1 2≤m) , proper-div-is-1)
    where
    proper-div-is-1 : (x : ℕ) → is-proper-divisorℕ m x → x ≡ 1ℕ
    proper-div-is-1 0ℕ (_ , 0∣m) = ex-falso (m≠0 (0ℕdiv m 0∣m))
    proper-div-is-1 (succℕ 0ℕ) _ = refl
    proper-div-is-1 (succℕ (succℕ x)) (xnem , xdivm) =
      ex-falso (<-to-≱ (succℕ (succℕ x)) m x<m (mlb (succℕ (succℕ x)) (0ℕ-leℕ x , div-transℕ (succℕ (succℕ x)) m n xdivm mdivn)))
      where
      x≤m : succℕ (succℕ x) ≤ℕ m
      x≤m = divℕ-to-≤ℕ (succℕ (succℕ x)) m xdivm m≠0
      x<m : succℕ (succℕ x) <ℕ m
      x<m = ind⊎ {P = λ _ → succℕ (succℕ x) <ℕ m} (λ z → z) (λ m≤x → ex-falso (xnem (≤-antisymℕ (succℕ (succℕ x)) m x≤m m≤x))) (<-or-≤ℕ (succℕ (succℕ x)) m)

quotient-<ℕ : (k p n : ℕ) → k ·ℕ p ≡ n → 2ℕ ≤ℕ p → 2ℕ ≤ℕ n → k <ℕ n
quotient-<ℕ 0ℕ p n kp≡n 2≤p 2≤n = ex-falso (tr (2ℕ ≤ℕ_) (concat (inv kp≡n) (zero-mulℕ p)) 2≤n)
quotient-<ℕ (succℕ k') p n kp≡n 2≤p 2≤n = succ-≤-to-<ℕ (succℕ k') n sk≤n
  where
  k = succℕ k'
  1≤k : 1ℕ ≤ℕ k
  1≤k = 0ℕ-leℕ k'
  sk≤kk : succℕ k ≤ℕ (k +ℕ k)
  sk≤kk = add-≤ℕ k 0ℕ k' (0ℕ-leℕ k')
  kk≡k2 : k +ℕ k ≡ k ·ℕ 2ℕ
  kk≡k2 = refl
  k2≤kp : k ·ℕ 2ℕ ≤ℕ k ·ℕ p
  k2≤kp = ≤-mul-leftℕ 2ℕ p k 2≤p
  sk≤n : succℕ k ≤ℕ n
  sk≤n = ≤-transℕ {succℕ k} {k ·ℕ p} {n}
    (≤-transℕ {succℕ k} {k ·ℕ 2ℕ} {k ·ℕ p} sk≤kk k2≤kp)
    (≡-to-≤ℕ kp≡n)

quotient-1ℕ : (k p n : ℕ) → k ·ℕ p ≡ n → 2ℕ ≤ℕ n → ¬ (2ℕ ≤ℕ k) → k ≡ 1ℕ
quotient-1ℕ 0ℕ p n kp≡n 2≤n _ = ex-falso (tr (2ℕ ≤ℕ_) (concat (inv kp≡n) (zero-mulℕ p)) 2≤n)
quotient-1ℕ (succℕ 0ℕ) _ _ _ _ _ = refl
quotient-1ℕ (succℕ (succℕ k')) _ _ _ _ ¬2≤k = ex-falso (¬2≤k (0ℕ-leℕ k'))

all-prime : List ℕ → Set
all-prime [] = 𝟙
all-prime (x ∷ xs) = is-primeℕ x × all-prime xs

is-sorted-from : ℕ → List ℕ → Set
is-sorted-from lb [] = 𝟙
is-sorted-from lb (x ∷ xs) = (lb ≤ℕ x) × is-sorted-from x xs

is-sorted : List ℕ → Set
is-sorted [] = 𝟙
is-sorted (x ∷ xs) = is-sorted-from x xs

prime-factors-auxℕ : (bound n lb : ℕ) → n ≤ℕ bound → 2ℕ ≤ℕ n →
  ((d : ℕ) → 2ℕ ≤ℕ d → d ∣ n → lb ≤ℕ d) →
  Σ (List ℕ) (λ lst → (prod-List lst ≡ n) × all-prime lst × is-sorted-from lb lst)
prime-factors-auxℕ 0ℕ n lb n≤0 2≤n _ = ex-falso (tr (2ℕ ≤ℕ_) (≤0ℕ-to-≡0ℕ n n≤0) 2≤n)
prime-factors-auxℕ (succℕ b) n lb n≤sb 2≤n lb-hyp =
  ((p ∷ proj₁ rec) , (prod-proof , ((p-prime , proj₁ (proj₂ (proj₂ rec))) , (lb-hyp p p-2≤ p∣n , proj₂ (proj₂ (proj₂ rec))))))
  where
  pf = has-prime-factorℕ n 2≤n
  p = proj₁ pf
  p-prime = proj₁ (proj₂ pf)
  p∣n = proj₁ (proj₂ (proj₂ pf))
  p-lb = proj₂ (proj₂ (proj₂ pf))
  k = proj₁ p∣n
  kp≡n = proj₂ p∣n
  p-2≤ : 2ℕ ≤ℕ p
  p-2≤ = proj₁ (proj₁ (prime-iff-trivial-divℕ p) p-prime)
  k<n : k <ℕ n
  k<n = quotient-<ℕ k p n kp≡n p-2≤ 2≤n
  k≤b : k ≤ℕ b
  k≤b = ≤-transℕ {succℕ k} {n} {succℕ b} (<-to-succ-≤ℕ k n k<n) n≤sb
  k∣n : k ∣ n
  k∣n = (p , concat (mul-commℕ p k) kp≡n)
  p-lb-k : (d : ℕ) → 2ℕ ≤ℕ d → d ∣ k → p ≤ℕ d
  p-lb-k d 2≤d d∣k = p-lb d 2≤d (div-transℕ d k n d∣k k∣n)
  rec : Σ (List ℕ) (λ lst → (prod-List lst ≡ k) × all-prime lst × is-sorted-from p lst)
  rec with ≤ℕ-is-decidable 2ℕ k
  ... | inl 2≤k = prime-factors-auxℕ b k p k≤b 2≤k p-lb-k
  ... | inr ¬2≤k = ([] , (inv (quotient-1ℕ k p n kp≡n 2≤n ¬2≤k) , (* , *)))
  prod-proof : p ·ℕ prod-List (proj₁ rec) ≡ n
  prod-proof = concat (ap (p ·ℕ_) (proj₁ (proj₂ rec))) (concat (mul-commℕ p k) kp≡n)

prime-factorsℕ : (n : ℕ) → (2ℕ ≤ℕ n) → List ℕ
prime-factorsℕ n 2≤n = proj₁ (prime-factors-auxℕ n n 2ℕ (≤-rflℕ n) 2≤n (λ d 2≤d _ → 2≤d))

prod-prime-factorsℕ : (n : ℕ) → (2≤n : 2ℕ ≤ℕ n) → prod-List (prime-factorsℕ n 2≤n) ≡ n
prod-prime-factorsℕ n 2≤n = proj₁ (proj₂ (prime-factors-auxℕ n n 2ℕ (≤-rflℕ n) 2≤n (λ d 2≤d _ → 2≤d)))

all-prime-factorsℕ : (n : ℕ) → (2≤n : 2ℕ ≤ℕ n) → all-prime (prime-factorsℕ n 2≤n)
all-prime-factorsℕ n 2≤n = proj₁ (proj₂ (proj₂ (prime-factors-auxℕ n n 2ℕ (≤-rflℕ n) 2≤n (λ d 2≤d _ → 2≤d))))

is-sorted-from-weaken : (lb : ℕ) → (lst : List ℕ) → is-sorted-from lb lst → is-sorted lst
is-sorted-from-weaken lb [] _ = *
is-sorted-from-weaken lb (x ∷ xs) (_ , sf) = sf

sorted-prime-factorsℕ : (n : ℕ) → (2≤n : 2ℕ ≤ℕ n) → is-sorted (prime-factorsℕ n 2≤n)
sorted-prime-factorsℕ n 2≤n = is-sorted-from-weaken 2ℕ (prime-factorsℕ n 2≤n) (proj₂ (proj₂ (proj₂ aux)))
  where aux = prime-factors-auxℕ n n 2ℕ (≤-rflℕ n) 2≤n (λ d 2≤d _ → 2≤d)

-- Multiplication cancellation
mul-cancelℕ : (k a b : ℕ) → succℕ k ·ℕ a ≡ succℕ k ·ℕ b → a ≡ b
mul-cancelℕ k a b p = dist0-to-≡ℕ a b dist-ab-0
  where
  sk-dist-0 : succℕ k ·ℕ distℕ a b ≡ 0ℕ
  sk-dist-0 = concat (inv (dist-linearℕ a b (succℕ k))) (≡-to-dist0ℕ (succℕ k ·ℕ a) (succℕ k ·ℕ b) p)
  dist-ab-0 : distℕ a b ≡ 0ℕ
  dist-ab-0 = proj₂ (add-to-zeroℕ (k ·ℕ distℕ a b) (distℕ a b)
    (concat (inv (succ-mulℕ k (distℕ a b))) sk-dist-0))

-- gcd of prime and non-multiple is 1
gcd-prime-coprimeℕ : (p a : ℕ) → is-primeℕ p → ¬ (p ∣ a) → gcdℕ p a ≡ 1ℕ
gcd-prime-coprimeℕ p a pprime p∤a = ind⊎ {P = λ _ → gcdℕ p a ≡ 1ℕ}
  (λ g≡1 → g≡1)
  (λ g≡p → ex-falso (p∤a (tr (_∣ a) g≡p (proj₂ (proj₂ (gcd-is-gcdℕ p a (gcdℕ p a)) (div-rflℕ (gcdℕ p a)))))))
  (proj₂ (proj₁ (prime-iff-trivial-divℕ p) pprime) (gcdℕ p a) (proj₁ (proj₂ (gcd-is-gcdℕ p a (gcdℕ p a)) (div-rflℕ (gcdℕ p a)))))

-- Euclid's lemma: if p prime and p | a·b then p | a or p | b
euclid-lemmaℕ : (p a b : ℕ) → is-primeℕ p → p ∣ (a ·ℕ b) → (p ∣ a) ⊎ (p ∣ b)
euclid-lemmaℕ p a b pprime p∣ab with divℕ-decidable p a
... | inl p∣a = inl p∣a
... | inr p∤a = inr p∣b
  where
  g≡1 : gcdℕ p a ≡ 1ℕ
  g≡1 = gcd-prime-coprimeℕ p a pprime p∤a
  bez = Bezout-identityℕ p a
  k = proj₁ bez
  l = proj₁ (proj₂ bez)
  bez-eq : distℕ (k ·ℕ p) (l ·ℕ a) ≡ gcdℕ p a
  bez-eq = proj₂ (proj₂ bez)
  dist-eq : distℕ (k ·ℕ p) (l ·ℕ a) ≡ 1ℕ
  dist-eq = concat bez-eq g≡1
  scaled : distℕ (b ·ℕ (k ·ℕ p)) (b ·ℕ (l ·ℕ a)) ≡ b
  scaled = concat (dist-linearℕ (k ·ℕ p) (l ·ℕ a) b)
    (concat (ap (b ·ℕ_) dist-eq) (mul-oneℕ b))
  p∣bkp : p ∣ (b ·ℕ (k ·ℕ p))
  p∣bkp = ((b ·ℕ k) , mul-assocℕ b k p)
  p∣bla : p ∣ (b ·ℕ (l ·ℕ a))
  p∣bla = tr (p ∣_) (concat (inv (mul-assocℕ l a b)) (mul-commℕ (l ·ℕ a) b))
    (div-mulℕ p (a ·ℕ b) l p∣ab)
  p∣b : p ∣ b
  p∣b = tr (p ∣_) scaled (div-distℕ (b ·ℕ (k ·ℕ p)) (b ·ℕ (l ·ℕ a)) p p∣bkp p∣bla)

-- If p and q are both prime and p | q, then p = q
prime-div-primeℕ : (p q : ℕ) → is-primeℕ p → is-primeℕ q → p ∣ q → p ≡ q
prime-div-primeℕ p q pprime qprime p∣q = ind⊎ {P = λ _ → p ≡ q}
  (λ p≡1 → ex-falso (proj₁ (is-prime-to-is-prime'ℕ p pprime) p≡1))
  (λ p≡q → p≡q)
  (proj₂ (proj₁ (prime-iff-trivial-divℕ q) qprime) p p∣q)

-- If p is prime and p | prod(lst) where lst is all-prime and sorted-from lb, then lb ≤ p
prime-div-sorted-geqℕ : (p lb : ℕ) → (lst : List ℕ) → is-primeℕ p → all-prime lst →
  is-sorted-from lb lst → p ∣ prod-List lst → lb ≤ℕ p
prime-div-sorted-geqℕ p lb [] pprime _ _ p∣1 =
  ex-falso (proj₁ (is-prime-to-is-prime'ℕ p pprime) (div-antisymℕ p 1ℕ p∣1 (one-divℕ p)))
prime-div-sorted-geqℕ p lb (q ∷ rest) pprime (qprime , aprest) (lb≤q , sfrest) p∣qr =
  ind⊎ {P = λ _ → lb ≤ℕ p}
    (λ p∣q → tr (lb ≤ℕ_) (inv (prime-div-primeℕ p q pprime qprime p∣q)) lb≤q)
    (λ p∣rest → ≤-transℕ {lb} {q} {p} lb≤q
      (prime-div-sorted-geqℕ p q rest pprime aprest sfrest p∣rest))
    (euclid-lemmaℕ p q (prod-List rest) pprime p∣qr)

-- Cancellation for p ≥ 2
mul-cancel-2≤ℕ : (p a b : ℕ) → 2ℕ ≤ℕ p → p ·ℕ a ≡ p ·ℕ b → a ≡ b
mul-cancel-2≤ℕ (succℕ (succℕ p')) a b _ eq = mul-cancelℕ (succℕ p') a b eq

-- Tail of sorted list is sorted
is-sorted-tail : (x : ℕ) → (xs : List ℕ) → is-sorted (x ∷ xs) → is-sorted xs
is-sorted-tail x [] _ = *
is-sorted-tail x (y ∷ ys) (_ , sys) = sys

-- Product of a list of primes is ≥ 1
1≤-prod-all-primeℕ : (lst : List ℕ) → all-prime lst → 1ℕ ≤ℕ prod-List lst
1≤-prod-all-primeℕ [] _ = *
1≤-prod-all-primeℕ (x ∷ xs) (xprime , apxs) =
  ≤-transℕ {1ℕ} {x} {x ·ℕ prod-List xs}
    (≤-transℕ {1ℕ} {2ℕ} {x} * (proj₁ (proj₁ (prime-iff-trivial-divℕ x) xprime)))
    (≤-mul-leftℕ 1ℕ (prod-List xs) x (1≤-prod-all-primeℕ xs apxs))

-- 2 ≤ prime times product of primes
2≤-cons-prod-all-primeℕ : (p : ℕ) → (rest : List ℕ) → is-primeℕ p → all-prime rest →
  2ℕ ≤ℕ (p ·ℕ prod-List rest)
2≤-cons-prod-all-primeℕ p rest pprime aprest =
  ≤-transℕ {2ℕ} {p} {p ·ℕ prod-List rest}
    (proj₁ (proj₁ (prime-iff-trivial-divℕ p) pprime))
    (≤-mul-leftℕ 1ℕ (prod-List rest) p (1≤-prod-all-primeℕ rest aprest))

-- Uniqueness of prime factorization
unique-prime-factorsℕ : (bound : ℕ) → (lst1 lst2 : List ℕ) →
  prod-List lst1 ≤ℕ bound →
  prod-List lst1 ≡ prod-List lst2 →
  all-prime lst1 → all-prime lst2 →
  is-sorted lst1 → is-sorted lst2 →
  lst1 ≡ lst2
unique-prime-factorsℕ bound [] [] _ _ _ _ _ _ = refl
unique-prime-factorsℕ bound [] (q ∷ rest2) _ prod-eq _ (qprime , _) _ _ =
  ex-falso (proj₁ (is-prime-to-is-prime'ℕ q qprime) q≡1)
  where
  q≡1 : q ≡ 1ℕ
  q≡1 = div-antisymℕ q 1ℕ (tr (q ∣_) (inv prod-eq) ((prod-List rest2) , mul-commℕ (prod-List rest2) q)) (one-divℕ q)
unique-prime-factorsℕ bound (p ∷ rest1) [] _ prod-eq (pprime , _) _ _ _ =
  ex-falso (proj₁ (is-prime-to-is-prime'ℕ p pprime) p≡1)
  where
  p≡1 : p ≡ 1ℕ
  p≡1 = div-antisymℕ p 1ℕ (tr (p ∣_) prod-eq ((prod-List rest1) , mul-commℕ (prod-List rest1) p)) (one-divℕ p)
unique-prime-factorsℕ 0ℕ (p ∷ rest1) (q ∷ rest2) prod≤0 _ (pprime , ap1) _ _ _ =
  ex-falso (tr (2ℕ ≤ℕ_) (≤0ℕ-to-≡0ℕ (p ·ℕ prod-List rest1) prod≤0)
    (2≤-cons-prod-all-primeℕ p rest1 pprime ap1))
unique-prime-factorsℕ (succℕ bound) (p ∷ rest1) (q ∷ rest2) prod≤sb prod-eq
  (pprime , ap1) (qprime , ap2) sorted1 sorted2 =
  concat (ap (λ x → x ∷ rest1) p≡q) (ap (q ∷_) rest-eq)
  where
  p-2≤ : 2ℕ ≤ℕ p
  p-2≤ = proj₁ (proj₁ (prime-iff-trivial-divℕ p) pprime)
  q-2≤ : 2ℕ ≤ℕ q
  q-2≤ = proj₁ (proj₁ (prime-iff-trivial-divℕ q) qprime)
  -- p divides prod of list2
  p∣prod2 : p ∣ (q ·ℕ prod-List rest2)
  p∣prod2 = (prod-List rest1 , concat (mul-commℕ (prod-List rest1) p) prod-eq)
  -- q divides prod of list1
  q∣prod1 : q ∣ (p ·ℕ prod-List rest1)
  q∣prod1 = (prod-List rest2 , concat (mul-commℕ (prod-List rest2) q) (inv prod-eq))
  -- q ≤ p: by Euclid, p | q or p | prod rest2
  q≤p : q ≤ℕ p
  q≤p = ind⊎ {P = λ _ → q ≤ℕ p}
    (λ p∣q → ≡-to-≤ℕ (inv (prime-div-primeℕ p q pprime qprime p∣q)))
    (λ p∣rest2 → prime-div-sorted-geqℕ p q rest2 pprime ap2 sorted2 p∣rest2)
    (euclid-lemmaℕ p q (prod-List rest2) pprime p∣prod2)
  -- p ≤ q: by Euclid, q | p or q | prod rest1
  p≤q : p ≤ℕ q
  p≤q = ind⊎ {P = λ _ → p ≤ℕ q}
    (λ q∣p → ≡-to-≤ℕ (inv (prime-div-primeℕ q p qprime pprime q∣p)))
    (λ q∣rest1 → prime-div-sorted-geqℕ q p rest1 qprime ap1 sorted1 q∣rest1)
    (euclid-lemmaℕ q p (prod-List rest1) qprime q∣prod1)
  p≡q : p ≡ q
  p≡q = ≤-antisymℕ p q p≤q q≤p
  -- Cancel p from both sides
  prod-rest-eq : prod-List rest1 ≡ prod-List rest2
  prod-rest-eq = mul-cancel-2≤ℕ p (prod-List rest1) (prod-List rest2) p-2≤
    (concat prod-eq (ap (λ x → x ·ℕ prod-List rest2) (inv p≡q)))
  -- prod rest1 ≤ bound for recursive call
  n = p ·ℕ prod-List rest1
  n≤sb : n ≤ℕ succℕ bound
  n≤sb = prod≤sb
  2≤n : 2ℕ ≤ℕ n
  2≤n = 2≤-cons-prod-all-primeℕ p rest1 pprime ap1
  rest1<n : prod-List rest1 <ℕ n
  rest1<n = quotient-<ℕ (prod-List rest1) p n
    (concat (mul-commℕ (prod-List rest1) p) refl)
    p-2≤ 2≤n
  rest1≤bound : prod-List rest1 ≤ℕ bound
  rest1≤bound = ≤-transℕ {succℕ (prod-List rest1)} {n} {succℕ bound}
    (<-to-succ-≤ℕ (prod-List rest1) n rest1<n) n≤sb
  -- Recursive call
  rest-eq : rest1 ≡ rest2
  rest-eq = unique-prime-factorsℕ bound rest1 rest2
    rest1≤bound prod-rest-eq ap1 ap2
    (is-sorted-tail p rest1 sorted1)
    (is-sorted-tail q rest2 sorted2)

-- Lemma: product of 1-mod-4 numbers is 1 mod 4
-- Key fact: (4a+1)(4b+1) = 16ab + 4a + 4b + 1 = 4(4ab+a+b) + 1
mul-1-mod-4ℕ : (a b : ℕ) → a ≡ℕ 1ℕ mod 4ℕ → b ≡ℕ 1ℕ mod 4ℕ → (a ·ℕ b) ≡ℕ 1ℕ mod 4ℕ
mul-1-mod-4ℕ a b amod bmod =
  mod-is-transℕ 4ℕ (a ·ℕ b) (1ℕ ·ℕ 1ℕ) 1ℕ
    (mul-≡-modℕ 4ℕ a 1ℕ b 1ℕ amod bmod)
    (eqℕ-to-eq-modℕ 4ℕ (1ℕ ·ℕ 1ℕ) 1ℕ refl)

-- All elements of a list satisfy a predicate
all-satisfy : {A : Set} → (A → Set) → List A → Set
all-satisfy P [] = 𝟙
all-satisfy P (x ∷ xs) = P x × all-satisfy P xs

-- Product of a list of 1-mod-4 numbers is 1 mod 4
prod-1-mod-4ℕ : (lst : List ℕ) → all-satisfy (λ x → x ≡ℕ 1ℕ mod 4ℕ) lst →
  prod-List lst ≡ℕ 1ℕ mod 4ℕ
prod-1-mod-4ℕ [] _ = eqℕ-to-eq-modℕ 4ℕ 1ℕ 1ℕ refl
prod-1-mod-4ℕ (x ∷ xs) (xmod , rest) =
  mul-1-mod-4ℕ x (prod-List xs) xmod (prod-1-mod-4ℕ xs rest)

-- 4 does not divide 1
4-not-div-1ℕ : ¬ (4ℕ ∣ 1ℕ)
4-not-div-1ℕ d4 = divℕ-to-≤ℕ 4ℕ 1ℕ d4 (λ ())

-- 4 does not divide 2
4-not-div-2ℕ : ¬ (4ℕ ∣ 2ℕ)
4-not-div-2ℕ d4 = divℕ-to-≤ℕ 4ℕ 2ℕ d4 (λ ())

-- 2 is not 3 mod 4: distℕ 2 3 = 1, and 4 ∤ 1
2-not-3-mod-4ℕ : ¬ (2ℕ ≡ℕ 3ℕ mod 4ℕ)
2-not-3-mod-4ℕ p = 4-not-div-1ℕ p

-- 1 is not 3 mod 4: distℕ 1 3 = 2, and 4 ∤ 2
1-not-3-mod-4ℕ : ¬ (1ℕ ≡ℕ 3ℕ mod 4ℕ)
1-not-3-mod-4ℕ p = 4-not-div-2ℕ p

-- 2 divides 4
2-div-4ℕ : 2ℕ ∣ 4ℕ
2-div-4ℕ = (2ℕ , refl)

-- Every odd number mod 4 is 1 or 3
odd-mod-4ℕ : (p : ℕ) → ¬ (2ℕ ∣ p) → (p ≡ℕ 1ℕ mod 4ℕ) ⊎ (p ≡ℕ 3ℕ mod 4ℕ)
odd-mod-4ℕ p p-odd with euclidean-divℕ p 4ℕ (λ ())
... | (q , (0ℕ , (peq , _))) = ex-falso (p-odd (tr (2ℕ ∣_) (inv peq) (div-mulℕ 2ℕ 4ℕ q 2-div-4ℕ)))
... | (q , (succℕ 0ℕ , (peq , _))) = inl
  (mod-is-transℕ 4ℕ p (q ·ℕ 4ℕ +ℕ 1ℕ) 1ℕ
    (eqℕ-to-eq-modℕ 4ℕ p (q ·ℕ 4ℕ +ℕ 1ℕ) peq)
    (mod-add-mulℕ 4ℕ q 1ℕ))
... | (q , (succℕ (succℕ 0ℕ) , (peq , _))) = ex-falso (p-odd
  (tr (2ℕ ∣_) (inv peq) (div-sumℕ (q ·ℕ 4ℕ) 2ℕ 2ℕ (div-mulℕ 2ℕ 4ℕ q 2-div-4ℕ) (div-rflℕ 2ℕ))))
... | (q , (succℕ (succℕ (succℕ 0ℕ)) , (peq , _))) = inr
  (mod-is-transℕ 4ℕ p (q ·ℕ 4ℕ +ℕ 3ℕ) 3ℕ
    (eqℕ-to-eq-modℕ 4ℕ p (q ·ℕ 4ℕ +ℕ 3ℕ) peq)
    (mod-add-mulℕ 4ℕ q 3ℕ))
... | (q , (succℕ (succℕ (succℕ (succℕ r'))) , (_ , r<4))) = ex-falso (¬<0ℕ r' r<4)

-- If p is prime and p ≠ 2, then p is odd
prime-ne-2-to-oddℕ : (p : ℕ) → is-primeℕ p → ¬ (p ≡ 2ℕ) → ¬ (2ℕ ∣ p)
prime-ne-2-to-oddℕ p pprime p≠2 2∣p =
  ind⊎ {P = λ _ → Empty}
    (λ 2≡1 → zero-ne-succℕ 0ℕ (inv (proj₂ (succ-injℕ 1ℕ 0ℕ) 2≡1)))
    (λ 2≡p → p≠2 (inv 2≡p))
    (proj₂ (proj₁ (prime-iff-trivial-divℕ p) pprime) 2ℕ 2∣p)

-- Every prime is 2, 1 mod 4, or 3 mod 4
prime-mod-4ℕ : (p : ℕ) → is-primeℕ p → (p ≡ 2ℕ) ⊎ (p ≡ℕ 1ℕ mod 4ℕ) ⊎ (p ≡ℕ 3ℕ mod 4ℕ)
prime-mod-4ℕ p pprime with ℕ-decidable-eq p 2ℕ
... | inl peq2 = inl peq2
... | inr pneq2 = inr (odd-mod-4ℕ p (prime-ne-2-to-oddℕ p pprime pneq2))

-- Every prime factor of an odd number is odd
prime-factor-of-oddℕ : (p n : ℕ) → is-primeℕ p → p ∣ n → ¬ (2ℕ ∣ n) → ¬ (p ≡ 2ℕ)
prime-factor-of-oddℕ p n pprime p∣n n-odd p≡2 = n-odd (tr (_∣ n) p≡2 p∣n)

-- 1 ≤ 4·n! (needed for distℕ reasoning)
1≤4n!ℕ : (n : ℕ) → 1ℕ ≤ℕ (4ℕ ·ℕ factorialℕ n)
1≤4n!ℕ n = ≤-transℕ {1ℕ} {4ℕ} {4ℕ ·ℕ factorialℕ n} * (≤-mul-leftℕ 1ℕ (factorialℕ n) 4ℕ (1≤-factorialℕ n)) 

-- distℕ (4·n!) 1 + 1 ≡ 4·n! (the key identity: M + 1 = 4·n!)
dist-4n!-1-addℕ : (n : ℕ) → distℕ (4ℕ ·ℕ factorialℕ n) 1ℕ +ℕ 1ℕ ≡ 4ℕ ·ℕ factorialℕ n
dist-4n!-1-addℕ n = concat (add-commℕ (distℕ (4ℕ ·ℕ factorialℕ n) 1ℕ) 1ℕ) (concat (ap (λ x → 1ℕ +ℕ x) (dist-symmℕ (4ℕ ·ℕ factorialℕ n) 1ℕ)) (add-distℕ 1ℕ (4ℕ ·ℕ factorialℕ n) (1≤4n!ℕ n)))

-- 4·n! - 1 ≡ 3 mod 4 (since 4·n! ≡ 0 mod 4, subtract 1 gives 3 mod 4)
4n!-1-mod-4ℕ : (n : ℕ) → distℕ (4ℕ ·ℕ factorialℕ n) 1ℕ ≡ℕ 3ℕ mod 4ℕ
4n!-1-mod-4ℕ n = mod-is-transℕ 4ℕ M (q ·ℕ 4ℕ +ℕ 3ℕ) 3ℕ
    (eqℕ-to-eq-modℕ 4ℕ M (q ·ℕ 4ℕ +ℕ 3ℕ) arith)
    (mod-add-mulℕ 4ℕ q 3ℕ)
  where
  f = factorialℕ n
  M = distℕ (4ℕ ·ℕ f) 1ℕ
  q = distℕ f 1ℕ
  q+1≡f : q +ℕ 1ℕ ≡ f
  q+1≡f = concat (add-commℕ q 1ℕ) (concat (ap (1ℕ +ℕ_) (dist-symmℕ f 1ℕ)) (add-distℕ 1ℕ f (1≤-factorialℕ n)))
  rhs+1≡4f : q ·ℕ 4ℕ +ℕ 3ℕ +ℕ 1ℕ ≡ 4ℕ ·ℕ f
  rhs+1≡4f =
    concat (add-assocℕ (q ·ℕ 4ℕ) 3ℕ 1ℕ)          -- q·4 + (3+1) = q·4 + 4
    (concat (inv (right-distribℕ q 1ℕ 4ℕ))         -- (q+1)·4
    (concat (ap (_·ℕ 4ℕ) q+1≡f)                    -- f·4
    (mul-commℕ f 4ℕ)))                              -- 4·f
  arith : M ≡ q ·ℕ 4ℕ +ℕ 3ℕ
  arith = proj₂ (add-injℕ M (q ·ℕ 4ℕ +ℕ 3ℕ) 1ℕ) (concat (dist-4n!-1-addℕ n) (inv rhs+1≡4f))

-- 4·n! - 1 is odd
4n!-1-oddℕ : (n : ℕ) → ¬ (2ℕ ∣ distℕ (4ℕ ·ℕ factorialℕ n) 1ℕ)
4n!-1-oddℕ n 2∣M = divℕ-to-≤ℕ 2ℕ 1ℕ 2∣1 (λ ())
  where
  M = distℕ (4ℕ ·ℕ factorialℕ n) 1ℕ
  2∣4f : 2ℕ ∣ (4ℕ ·ℕ factorialℕ n)
  2∣4f = tr (2ℕ ∣_) (mul-commℕ (factorialℕ n) 4ℕ) (div-mulℕ 2ℕ 4ℕ (factorialℕ n) 2-div-4ℕ)
  2∣1+M : 2ℕ ∣ (1ℕ +ℕ M)
  2∣1+M = tr (2ℕ ∣_) (concat (inv (dist-4n!-1-addℕ n)) (add-commℕ M 1ℕ)) 2∣4f
  2∣1 = div-sum-partℕ 1ℕ M 2ℕ 2∣1+M 2∣M

-- 4·n! - 1 ≥ 2
4n!-1-≥2ℕ : (n : ℕ) → 2ℕ ≤ℕ distℕ (4ℕ ·ℕ factorialℕ n) 1ℕ
4n!-1-≥2ℕ n = tr (3ℕ ≤ℕ_) (inv (dist-4n!-1-addℕ n))
    (≤-transℕ {3ℕ} {4ℕ} {4ℕ ·ℕ factorialℕ n} * (≤-mul-leftℕ 1ℕ (factorialℕ n) 4ℕ (1≤-factorialℕ n)))

-- Search a list of primes for one ≡ 3 mod 4; if none, all are ≡ 1 mod 4
find-3mod4ℕ : (lst : List ℕ) → all-prime lst → ¬ (2ℕ ∣ prod-List lst) →
  (Σ ℕ (λ p → is-primeℕ p × (p ≡ℕ 3ℕ mod 4ℕ) × (p ∣ prod-List lst))) ⊎
  all-satisfy (λ x → x ≡ℕ 1ℕ mod 4ℕ) lst
find-3mod4ℕ [] _ _ = inr *
find-3mod4ℕ (x ∷ xs) (xprime , apxs) prod-odd with prime-mod-4ℕ x xprime
... | inl x≡2 = ex-falso (prod-odd
  (tr (2ℕ ∣_) (mul-commℕ (prod-List xs) x)
    (div-mulℕ 2ℕ x (prod-List xs) (tr (2ℕ ∣_) (inv x≡2) (div-rflℕ 2ℕ)))))
... | inr (inr x3mod4) = inl (x , (xprime , (x3mod4 , (prod-List xs , mul-commℕ (prod-List xs) x))))
... | inr (inl x1mod4) with find-3mod4ℕ xs apxs (λ 2∣xs → prod-odd (div-mulℕ 2ℕ (prod-List xs) x 2∣xs))
... | inl (p , (pprime , (p3mod4 , p∣prodxs))) = inl (p , (pprime , (p3mod4 , div-mulℕ p (prod-List xs) x p∣prodxs)))
... | inr all1mod4 = inr (x1mod4 , all1mod4)

-- If n ≡ 3 mod 4, n ≥ 2, and n is odd, then n has a prime factor ≡ 3 mod 4
3mod4-has-3mod4-prime-factorℕ : (n : ℕ) → 2ℕ ≤ℕ n → n ≡ℕ 3ℕ mod 4ℕ → ¬ (2ℕ ∣ n) →
  Σ ℕ (λ p → is-primeℕ p × (p ≡ℕ 3ℕ mod 4ℕ) × (p ∣ n))
3mod4-has-3mod4-prime-factorℕ n 2≤n nmod n-odd = result (find-3mod4ℕ lst lst-prime odd-lst)
  where
  lst = prime-factorsℕ n 2≤n
  prodeq = prod-prime-factorsℕ n 2≤n
  lst-prime = all-prime-factorsℕ n 2≤n
  odd-lst : ¬ (2ℕ ∣ prod-List lst)
  odd-lst 2∣prod = n-odd (tr (2ℕ ∣_) prodeq 2∣prod)
  result : (Σ ℕ (λ p → is-primeℕ p × (p ≡ℕ 3ℕ mod 4ℕ) × (p ∣ prod-List lst))) ⊎
           all-satisfy (λ x → x ≡ℕ 1ℕ mod 4ℕ) lst →
           Σ ℕ (λ p → is-primeℕ p × (p ≡ℕ 3ℕ mod 4ℕ) × (p ∣ n))
  result (inl (p , (pprime , (p3mod4 , p∣prod)))) = (p , (pprime , (p3mod4 , tr (p ∣_) prodeq p∣prod)))
  result (inr all1mod4) = ex-falso (1-not-3-mod-4ℕ
    (mod-is-transℕ 4ℕ 1ℕ n 3ℕ
      (mod-is-transℕ 4ℕ 1ℕ (prod-List lst) n
        (mod-is-symmℕ 4ℕ (prod-List lst) 1ℕ (prod-1-mod-4ℕ lst all1mod4))
        (eqℕ-to-eq-modℕ 4ℕ (prod-List lst) n prodeq))
      nmod))

-- If p ∣ (4·n! - 1) and p ∣ n!, then p ∣ 1
-- Proof: p ∣ n! implies p ∣ 4·n!. Since 4·n! = (4·n! - 1) + 1,
-- we get p ∣ 1 from div-sum-partℕ.
div-4n!-1-and-n!-to-div-1ℕ : (p n : ℕ) → p ∣ distℕ (4ℕ ·ℕ factorialℕ n) 1ℕ → p ∣ factorialℕ n → p ∣ 1ℕ
div-4n!-1-and-n!-to-div-1ℕ p n p∣M p∣fact = div-sum-rightℕ (distℕ (4ℕ ·ℕ factorialℕ n) 1ℕ) 1ℕ p p∣M (tr (λ x → p ∣ x) (inv (concat (add-commℕ (distℕ (4ℕ ·ℕ factorialℕ n) 1ℕ) 1ℕ) (concat (ap (λ x → 1ℕ +ℕ x) (dist-symmℕ (4ℕ ·ℕ factorialℕ n) 1ℕ)) (add-distℕ 1ℕ (4ℕ ·ℕ factorialℕ n) (≤-transℕ {1ℕ} {4ℕ} {4ℕ ·ℕ factorialℕ n} * (≤-mul-leftℕ 1ℕ (factorialℕ n) 4ℕ (1≤-factorialℕ n))))))) (div-mulℕ p (factorialℕ n) 4ℕ p∣fact) )

-- 3 is prime
3-is-primeℕ : is-primeℕ 3ℕ
3-is-primeℕ = is-prime'-to-is-primeℕ 3ℕ ((λ 3eq1 → zero-ne-succℕ 1ℕ (proj₂ (succ-injℕ 0ℕ 2ℕ) (inv 3eq1))) , 3-proper-div)
  where
  3-proper-div : (x : ℕ) → is-proper-divisorℕ 3ℕ x → x ≡ 1ℕ
  3-proper-div 0ℕ (_ , div) = ex-falso (zero-ne-succℕ 2ℕ (inv (0ℕdiv 3ℕ div)))
  3-proper-div (succℕ 0ℕ) _ = refl
  3-proper-div (succℕ (succℕ 0ℕ)) (_ , div) = ex-falso (divℕ-to-≤ℕ 2ℕ 1ℕ (div-sum-partℕ 1ℕ 2ℕ 2ℕ div (div-rflℕ 2ℕ)) (λ ()))
  3-proper-div (succℕ (succℕ (succℕ 0ℕ))) (ne , _) = ex-falso (ne refl)
  3-proper-div (succℕ (succℕ (succℕ (succℕ x)))) (_ , div) = ex-falso (divℕ-to-≤ℕ (succℕ (succℕ (succℕ (succℕ x)))) 3ℕ div (λ p → zero-ne-succℕ 2ℕ (inv p)))

-- 3 ≡ 3 mod 4
3-mod-4ℕ : 3ℕ ≡ℕ 3ℕ mod 4ℕ
3-mod-4ℕ = 0ℕ , refl

-- Main theorem: infinitely many primes ≡ 3 mod 4
-- Proof sketch: Let M = 4·n! - 1. Then M ≡ 3 mod 4 and M is odd.
-- So M has a prime factor p ≡ 3 mod 4 (by 3mod4-has-3mod4-prime-factorℕ).
-- If p ≤ n, then p ∣ n!, so p ∣ 1 (by div-4n!-1-and-n!-to-div-1ℕ), contradicting p prime.
-- So p > n, and we're done.
infinitely-many-4k+3-primesℕ : (n : ℕ) → Σ ℕ (λ p → (is-primeℕ p) × (p ≡ℕ 3ℕ mod 4ℕ) × (n <ℕ p))
infinitely-many-4k+3-primesℕ n = (p , (pprime , (p-is-3-mod-4 , p>n)))
  where
  M = distℕ (4ℕ ·ℕ factorialℕ n) 1ℕ
  M-is-3-mod-4 : M ≡ℕ 3ℕ mod 4ℕ
  M-is-3-mod-4 = 4n!-1-mod-4ℕ n
  Modd : ¬ (2ℕ ∣ M)
  Modd = 4n!-1-oddℕ n
  2leM : 2ℕ ≤ℕ M
  2leM = 4n!-1-≥2ℕ n
  3mod4 = 3mod4-has-3mod4-prime-factorℕ M 2leM M-is-3-mod-4 Modd
  p = proj₁ (3mod4)
  pprime : is-primeℕ p
  pprime = proj₁ (proj₂ 3mod4)
  p-is-3-mod-4 = proj₁ (proj₂ (proj₂ 3mod4))
  pdivn = proj₂ (proj₂ (proj₂ 3mod4))
  p>n : n <ℕ p
  p>n with <-or-≤ℕ n p
  ... | inl n<p = n<p
  ... | inr p≤n = ex-falso (≤-transℕ {2ℕ} {p} {1ℕ} 2≤p p≤1)
    where
    2≤p : 2ℕ ≤ℕ p
    2≤p = proj₁ (proj₁ (prime-iff-trivial-divℕ p) pprime)
    p≠0 : ¬ (p ≡ 0ℕ)
    p≠0 p≡0 = tr (2ℕ ≤ℕ_) p≡0 2≤p
    p∣fact : p ∣ factorialℕ n
    p∣fact = le-to-div-fact n p p≠0 p≤n
    p∣1 : p ∣ 1ℕ
    p∣1 = div-4n!-1-and-n!-to-div-1ℕ p n pdivn p∣fact
    p≤1 : p ≤ℕ 1ℕ
    p≤1 = divℕ-to-≤ℕ p 1ℕ p∣1 (λ ())
    
-- If x : Fin p is nonzero, then p does not divide ιFin x
nonzero-Fin-to-ndivℕ : (p : ℕ) → (x : ℤ-mod (succℕ p)) → ¬ (x ≡ zero-ℤmod (succℕ p)) → ¬ (succℕ p ∣ ι-ℤmod p x)
nonzero-Fin-to-ndivℕ p x xne0 pdivx = xne0 (Fin-to-ℕ-injective (succℕ p) x (zero-ℤmod (succℕ p)) (concat (<-div-to-zeroℕ (succℕ p) (ι-ℤmod p x) (Fin-to-ℕ-bounded (succℕ p) x) pdivx) (inv (zero-ℤmod-to-zeroℕ p))))
-- Bézout's identity gives k, l with distℕ (k·p) (l·a) = gcd p a = 1.
-- Case-split on which side is bigger:
--   l·a ≥ k·p:  l·a = k·p + 1, witness m = l (and l·a − 1 = k·p).
--   l·a ≤ k·p:  k·p = l·a + 1, so l·a ≡ −1 mod p; witness m = l·l·a, since
--               (l·a)² = (l·a − 1)·k·p + 1 ≡ 1 mod p. (For l·a = 0 this
--               degenerates to k·p = 1, i.e., p = 1, where everything is
--               trivially congruent mod 1.)
{-
bezout-mul-modℕ : (p a : ℕ) → gcdℕ p a ≡ 1ℕ → Σ ℕ (λ k → k ·ℕ a ≡ℕ 1ℕ mod p)
bezout-mul-modℕ p a g≡1 = result
  where
  bez = Bezout-identityℕ p a
  k = proj₁ bez
  l = proj₁ (proj₂ bez)
  dist-eq : distℕ (k ·ℕ p) (l ·ℕ a) ≡ gcdℕ p a
  dist-eq = proj₂ (proj₂ bez)
  eq : distℕ (k ·ℕ p) (l ·ℕ a) ≡ 1ℕ
  eq = concat dist-eq g≡1

  result : Σ ℕ (λ m → m ·ℕ a ≡ℕ 1ℕ mod p)
  result with ≤-dichotomyℕ (k ·ℕ p) (l ·ℕ a)
  ... | inl kp≤la =
    (l , (k , inv (concat (ap (λ x → distℕ x 1ℕ) la-eq)
                          (dist-add-rightℕ (k ·ℕ p) 1ℕ))))
    where
    la-eq : l ·ℕ a ≡ k ·ℕ p +ℕ 1ℕ
    la-eq = concat (inv (add-distℕ (k ·ℕ p) (l ·ℕ a) kp≤la))
                   (ap (λ z → (k ·ℕ p) +ℕ z) eq)
  ... | inr la≤kp = aux (l ·ℕ a) refl
    where
    kp-eq : k ·ℕ p ≡ l ·ℕ a +ℕ 1ℕ
    kp-eq = concat (inv (add-distℕ (l ·ℕ a) (k ·ℕ p) la≤kp))
                   (ap (λ z → (l ·ℕ a) +ℕ z)
                       (concat (dist-symmℕ (l ·ℕ a) (k ·ℕ p)) eq))

    aux : (la : ℕ) → la ≡ l ·ℕ a → Σ ℕ (λ m → m ·ℕ a ≡ℕ 1ℕ mod p)
    aux 0ℕ la0 = (0ℕ , (k , concat kp-1 (inv (ap (λ z → distℕ z 1ℕ) (zero-mulℕ a)))))
      where
      kp-1 : k ·ℕ p ≡ 1ℕ
      kp-1 = concat kp-eq (ap (λ z → z +ℕ 1ℕ) (inv la0))
    aux (succℕ L) suceq = (l ·ℕ l ·ℕ a , (L ·ℕ k , proof))
      where
      square-eq : l ·ℕ l ·ℕ a ·ℕ a ≡ (l ·ℕ a) ·ℕ (l ·ℕ a)
      square-eq = concat
        (ap (λ z → z ·ℕ a)
            (concat (mul-assocℕ l l a)
                    (concat (ap (λ z → l ·ℕ z) (mul-commℕ l a))
                            (inv (mul-assocℕ l a l)))))
        (mul-assocℕ (l ·ℕ a) l a)

      factor-eq : (l ·ℕ a) ·ℕ (l ·ℕ a) +ℕ l ·ℕ a ≡ (l ·ℕ a) ·ℕ (k ·ℕ p)
      factor-eq = concat
        (ap (λ z → (l ·ℕ a) ·ℕ (l ·ℕ a) +ℕ z) (inv (mul-oneℕ (l ·ℕ a))))
        (concat (inv (left-distribℕ (l ·ℕ a) (l ·ℕ a) 1ℕ))
                (ap (λ z → (l ·ℕ a) ·ℕ z) (inv kp-eq)))

      key-eq : l ·ℕ l ·ℕ a ·ℕ a +ℕ k ·ℕ p ≡ (l ·ℕ a) ·ℕ (k ·ℕ p) +ℕ 1ℕ
      key-eq = concat (ap (λ z → z +ℕ k ·ℕ p) square-eq)
        (concat (ap (λ z → (l ·ℕ a) ·ℕ (l ·ℕ a) +ℕ z) kp-eq)
        (concat (inv (add-assocℕ ((l ·ℕ a) ·ℕ (l ·ℕ a)) (l ·ℕ a) 1ℕ))
                (ap (λ z → z +ℕ 1ℕ) factor-eq)))

      chain : (l ·ℕ a) ·ℕ (k ·ℕ p) +ℕ 1ℕ ≡ L ·ℕ (k ·ℕ p) +ℕ 1ℕ +ℕ k ·ℕ p
      chain = concat (ap (λ z → z ·ℕ (k ·ℕ p) +ℕ 1ℕ) (inv suceq))
        (concat (ap (λ z → z +ℕ 1ℕ) (succ-mulℕ L (k ·ℕ p)))
        (concat (add-assocℕ (L ·ℕ (k ·ℕ p)) (k ·ℕ p) 1ℕ)
        (concat (ap (λ z → L ·ℕ (k ·ℕ p) +ℕ z) (add-commℕ (k ·ℕ p) 1ℕ))
                (inv (add-assocℕ (L ·ℕ (k ·ℕ p)) 1ℕ (k ·ℕ p))))))

      final-eq : l ·ℕ l ·ℕ a ·ℕ a ≡ L ·ℕ (k ·ℕ p) +ℕ 1ℕ
      final-eq = proj₂ (add-injℕ (l ·ℕ l ·ℕ a ·ℕ a) (L ·ℕ (k ·ℕ p) +ℕ 1ℕ) (k ·ℕ p))
                       (concat key-eq chain)

      proof : L ·ℕ k ·ℕ p ≡ distℕ (l ·ℕ l ·ℕ a ·ℕ a) 1ℕ
      proof = concat (mul-assocℕ L k p)
              (concat (inv (dist-add-rightℕ (L ·ℕ (k ·ℕ p)) 1ℕ))
                      (ap (λ z → distℕ z 1ℕ) (inv final-eq)))
-}
{-

-- Proof idea:
--   p = 0 case: ℤ-mod 0 should have a unique element (zero), so xne0
--     immediately gives ex-falso. If ℤ-mod 0 is defined as 𝟘 instead,
--     pattern-match x.
--   p = succ p' case: feed bezout-mul-modℕ; the inner hole asks for
--     gcd (succ p) (ι x) ≡ 1. Since p is prime and (succ p) ∤ ι x
--     (which is exactly nonzero-Fin-to-ndivℕ above), the only divisor of
--     succ p sharing a factor with ι x is 1 — use prime-iff-trivial-divℕ
--     and that gcd divides both arguments.
inv-modℤ : (p : ℕ) → (is-primeℕ p) → (x : ℤ-mod p) → ¬ (x ≡ zero-ℤmod p) → ℤ-mod p
inv-modℤ 0ℕ pprime x xne0 = {!!}
inv-modℤ (succℕ p) pprime x xne0 = [ proj₁ (bezout-mul-modℕ p (ι-ℤmod p x) {!!}) ] (succℕ p)

-- Proof idea: by definition of inv-modℤ via Bézout, k·(ι x) ≡ 1 mod p,
-- which transports along the projection ℕ → ℤ-mod p to give the result.
-- Need a lemma that ℤ-mod multiplication agrees with ℕ multiplication
-- after reduction (likely already available as part of the ℤ-mod ring).
inv-mul-modℤ : (p : ℕ) → (pprime : is-primeℕ p) → (x : ℤ-mod p) → (xne0 : ¬ (x ≡ zero-ℤmod p)) → mul-ℤ-mod p (inv-modℤ p pprime x xne0) x ≡ one-ℤmod p
inv-mul-modℤ p pprime x xne0 = {!!}

-- Proof idea: combine inv-mul-modℤ with commutativity of mul-ℤ-mod.
mul-inv-modℤ : (p : ℕ) → (pprime : is-primeℕ p) → (x : ℤ-mod p) → (xne0 : ¬ (x ≡ zero-ℤmod p)) → mul-ℤ-mod p x (inv-modℤ p pprime x xne0) ≡ one-ℤmod p
mul-inv-modℤ p pprime x xne0 = {!!}

-- Proof idea (Pisano period of n): least k > 0 with n ∣ F_k. Hole is the
-- existence witness for ℕ-well-ordered. Strategy: F mod n is eventually
-- periodic by pigeonhole on consecutive pairs (F_i mod n, F_{i+1} mod n)
-- ∈ Fin n × Fin n; once a pair repeats, F is purely periodic from index 0
-- since the recurrence runs backwards too, so some k > 0 has F_k ≡ 0 mod n.
cofib : ℕ → ℕ
cofib n = proj₁ (ℕ-well-ordered (λ x → (0ℕ <ℕ x) × (n ∣ fibℕ x)) (λ x → with-decidable-prod (<ℕ-is-decidable 0ℕ x) λ 0<x → divℕ-decidable n (fibℕ x)) {!(!})

-- Proof idea: the key arithmetic fact is the addition formula
--   F_{a+b} = F_a · F_{b+1} + F_{a-1} · F_b
-- reduced mod n.
--   to: write m = q · cofib n + r with r < cofib n. The formula gives
--     F_m ≡ F_r · F_{cofib n + 1}^q · ... mod n; more directly, induct on q
--     using F_{a + cofib n} ≡ F_a · F_{cofib n + 1} mod n. Minimality of
--     cofib n then forces r = 0.
--   from: similarly, write m = q · cofib n + r; n ∣ F_m and the addition
--     formula give n ∣ F_r, and minimality forces r = 0, so cofib n ∣ m.
cofib-prop : (n m : ℕ) → ((cofib n ∣ m) ↔ (n ∣ fibℕ m))
cofib-prop n m = (to , from)
  where
  cofib-wo = (ℕ-well-ordered (λ x → (0ℕ <ℕ x) × (n ∣ fibℕ x)) (λ x → with-decidable-prod (<ℕ-is-decidable 0ℕ x) λ 0<x → divℕ-decidable n (fibℕ x)) {!(!})
  to : (cofib n ∣ m) → (n ∣ fibℕ m)
  to = λ cofibndivm → {!!}
  from : (n ∣ fibℕ m) → (cofib n ∣ m)
  from = λ ndivfibm → {!!}

-}
