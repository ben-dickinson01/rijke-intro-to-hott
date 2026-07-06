{-# OPTIONS --without-K #-}
module ch12 where

open import ch11 public

is-prop : (A : Set) → Set
is-prop A = (x y : A) → is-contr (x ≡ y)

hProp : Set₁
hProp = Σ Set is-prop

empty-prop : is-prop 𝟘
empty-prop = λ ()

unit-prop : is-prop 𝟙
unit-prop = λ {* * → refl , (λ {refl → refl})}

is-prop' : (A : Set) → Set
is-prop' A = (x y : A) → x ≡ y

is-prop-to-is-prop' : {A : Set} → is-prop A → is-prop' A
is-prop-to-is-prop' {A} propA x y =  proj₁ (propA x y)

is-prop'-to-inhab-contr : {A : Set} → is-prop' A → A → is-contr A
is-prop'-to-inhab-contr {A} propA' a = a , λ x → propA' x a

inhab-emb-to-emb : {X Y : Set} → (f : X → Y) → (X → is-emb f) → is-emb f
inhab-emb-to-emb f emb x y = emb x x y

inhab-contr-to-emb-𝟙 : {A : Set} → (A → is-contr A) → is-emb (const {A} {𝟙} {*})
inhab-contr-to-emb-𝟙 {A} f = inhab-emb-to-emb (const {A} {𝟙} {*}) λ a → equiv-to-emb (const {A} {𝟙} {*}) (A-contr-to-const𝟙-equiv (f a)) 

emb-𝟙-to-is-prop : {A : Set} → is-emb (const {A} {𝟙} {*}) → is-prop A
emb-𝟙-to-is-prop {A} emb x y = equiv-contr-to-contr (ap (const {A} {𝟙} {*})) (unit-prop * *) (emb x y)

≃-to-iff : {P Q : Set} → is-prop P → is-prop Q → (P ≃ Q) → (P ↔ Q)
≃-to-iff propP propQ (f , ((g , fg) , (h , hf))) = f , g

iff-to-≃ : {P Q : Set} → is-prop P → is-prop Q → (P ↔ Q) → (P ≃ Q)
iff-to-≃ propP propQ (f , g) = f , ((g , λ x → proj₁ (propQ (f (g x)) x)) , (g , λ x → proj₁ (propP (g (f x)) x)))

is-subtype : (A : Set) → (B : A → Set) → Set
is-subtype A B = (x : A) → is-prop (B x)

≃-to-iff-prop : {A B : Set} → A ≃ B → is-prop A ↔ is-prop B
≃-to-iff-prop (f , ((g , fg) , (h , hf))) =
  (λ propA x y →
    concat (inv (fg x)) (concat (ap f (proj₁ (propA (g x) (g y)))) (fg y)) ,
    (λ p → concat
      (concat
        (inv (ap-id p))
        (concat
          (inv (left-unit (ap id p)))
          (concat
            (inv (ap (λ q → concat q (ap id p)) (left-inv (fg x))))
            (concat
              (assoc (inv (fg x)) (fg x) (ap id p))
              (concat
                (inv (ap (concat (inv (fg x))) (nat-htpy fg p)))
                (inv (ap (λ q → concat (inv (fg x)) (concat q (fg y)))
                         (ap-comp g f p))))))))
      (ap (λ q → concat (inv (fg x)) (concat (ap f q) (fg y)))
          (proj₂ (propA (g x) (g y)) (ap g p))))) ,
  (λ propB x y →
    concat (inv (hf x)) (concat (ap h (proj₁ (propB (f x) (f y)))) (hf y)) , 
    (λ p → concat
      (concat
        (inv (ap-id p))
        (concat
          (inv (left-unit (ap id p)))
          (concat
            (inv (ap (λ q → concat q (ap id p)) (left-inv (hf x))))
            (concat
              (assoc (inv (hf x)) (hf x) (ap id p))
              (concat
                (inv (ap (concat (inv (hf x))) (nat-htpy hf p)))
                (inv (ap (λ q → concat (inv (hf x)) (concat q (hf y)))
                         (ap-comp f h p))))))))
      (ap (λ q → concat (inv (hf x)) (concat (ap h q) (hf y)))
          (proj₂ (propB (f x) (f y)) (ap f p)))))

emb-to-fib-prop : {A B : Set} → (f : A → B) → is-emb f → (b : B) → is-prop (fib f b)
emb-to-fib-prop {A} {B} f femb b (a , p) (a' , p') = 
  equiv-contr-to-contr
    (pair-eq (a , p) (a' , p'))
    (equiv-to-contr-map
      (λ α → tr (λ z → f z ≡ b) α p)
      (htpy-of-equiv-is-equiv
        (λ α → concat (inv (ap f α)) p)
        (λ α → tr (λ z → f z ≡ b) α p)
        (λ α → inv (tr-fib f α p))
        (equiv-comp (inv ∘ ap f) (λ q → concat q p)
          (equiv-comp (ap f) inv (femb a a') (is-equiv-inv (f a) (f a')))
          (is-equiv-concat' p)))
      p')
    (pair-eq-is-equiv (a , p) (a' , p'))
    
fib-prop-to-emb : {A B : Set} → (f : A → B) → ((b : B) → is-prop (fib f b)) → is-emb f
fib-prop-to-emb {A} {B} f bpropfib x y =
  contr-map-to-equiv (ap f) (λ q →
    equiv-contr-to-contr
      (tot (λ p e →
        concat (tr-fib f p q)
               (concat (ap (concat (inv (ap f p))) (inv e))
                       (left-inv (ap f p)))))
      (contr-equiv-to-contr
        (pair-eq (x , q) (y , refl))
        (bpropfib (f y) (x , q) (y , refl))
        (pair-eq-is-equiv (x , q) (y , refl)))
      (fam-equiv-to-tot-equiv
        (λ p e →
          concat (tr-fib f p q)
                 (concat (ap (concat (inv (ap f p))) (inv e))
                         (left-inv (ap f p))))
        (λ p →
          equiv-comp
            (λ e → concat (ap (concat (inv (ap f p))) (inv e)) (left-inv (ap f p)))
            (concat (tr-fib f p q))
            (equiv-comp
              (λ e → ap (concat (inv (ap f p))) (inv e))
              (λ e → concat e (left-inv (ap f p)))
              (equiv-comp
                inv
                (λ r → ap (concat (inv (ap f p))) r)
                (is-equiv-inv (ap f p) q)
                (equiv-to-emb (concat (inv (ap f p)))
                              (is-equiv-concat (inv (ap f p))) q (ap f p)))
              (is-equiv-concat' (left-inv (ap f p))))
            (is-equiv-concat (tr-fib f p q)))))

proj₁-of-subtype-is-emb : {A : Set} → (P : A → Set) → is-subtype A P → is-emb (proj₁ {A = A} {B = P})
proj₁-of-subtype-is-emb {A} P PsubA =
  fib-prop-to-emb proj₁ (λ a →
    proj₂ (≃-to-iff-prop (_ , is-equiv-fib-proj₁ a)) (PsubA a))

-- 12.3 Sets
is-set : (A : Set) → Set
is-set A = (x y : A) → is-prop (x ≡ y)

Eq-ℕ-prop : (n m : ℕ) → is-prop (Eq-ℕ n m)
Eq-ℕ-prop 0ℕ 0ℕ = unit-prop
Eq-ℕ-prop 0ℕ (succℕ m) = empty-prop
Eq-ℕ-prop (succℕ n) 0ℕ = empty-prop
Eq-ℕ-prop (succℕ n) (succℕ m) = Eq-ℕ-prop n m

ℕ-set : is-set ℕ
ℕ-set n m =
  proj₂ (≃-to-iff-prop (≡-to-Eqℕ n m , ≡-to-Eqℕ-equiv n m)) (Eq-ℕ-prop n m)

axiom-K : (A : Set) → Set
axiom-K A = (x : A) → (p : x ≡ x) → refl ≡ p

set-to-K : {A : Set} → is-set A → axiom-K A
set-to-K Aset a p = proj₁ (Aset a a refl p)


K-to-set : {A : Set} → axiom-K A → is-set A
K-to-set KA a a' =
  emb-𝟙-to-is-prop
    (inhab-contr-to-emb-𝟙
      (is-prop'-to-inhab-contr all-paths-eq))
  where
    all-paths-eq : (p p' : a ≡ a') → p ≡ p'
    all-paths-eq p p' =
      concat
        (inv (right-unit p))
        (concat
          (ap (concat p) (inv (left-inv p')))
          (concat
            (inv (assoc p (inv p') p'))
            (concat
              (ap (λ q → concat q p') (inv (KA a (concat p (inv p')))))
              (left-unit p'))))

-- Theorem 12.3.4

rfl-prop-rel-to-equiv : {A : Set} → (R : A → A → Set) → ((x y : A) → is-prop (R x y)) → (ρ : (x : A) → R x x) → (f : (x y : A) → R x y → x ≡ y) → (x y : A) → (g : x ≡ y → R x y) → is-equiv g
rfl-prop-rel-to-equiv {A} R Rprop ρ f x y g =
  htpy-of-equiv-is-equiv (ind-eq x (ρ x) y) g
    (λ p → proj₁ (Rprop x y _ _))
    (total-contr-to-fam-equiv (ρ x) (ind-eq x (ρ x)) refl
      (retr-to-contr-to-contr
        (λ { (a , Rxa) → a , f x a Rxa })
        ( (λ { (a , p) → a , ind-eq x (ρ x) a p })
        , (λ { (b , q) → eq-pair _ _ (refl , proj₁ (Rprop x b (ind-eq x (ρ x) b (f x b q)) q)) }))
        (Σ-≡-contractible x))
      y)
  where
    ind-eq : (x : A) → R x x → (y : A) → (x ≡ y) → R x y
    ind-eq x ρx .x refl = ρx

rfl-prop-rel-to-set : {A : Set} → (R : A → A → Set) → ((x y : A) → is-prop (R x y)) → (ρ : (x : A) → R x x) → (f : (x y : A) → R x y → x ≡ y) → is-set A
rfl-prop-rel-to-set {A} R Rprop ρ f x y =
  proj₂ (≃-to-iff-prop (ind-eq x (ρ x) y , rfl-prop-rel-to-equiv R Rprop ρ f x y (ind-eq x (ρ x) y))) (Rprop x y)
  where
    ind-eq : (x : A) → R x x → (y : A) → (x ≡ y) → R x y
    ind-eq x ρx .x refl = ρx

Hedberg : {A : Set} → has-decidable-eq A → is-set A
Hedberg {A} Adeq = rfl-prop-rel-to-set R Rprop ρ f
  where
    R : (x y : A) → Set
    R x y with Adeq x y
    ... | inl p = 𝟙
    ... | inr np = 𝟘
    Rprop : (x y : A) → is-prop (R x y)
    Rprop x y with Adeq x y
    ... | inl p = unit-prop
    ... | inr np = empty-prop
    ρ : (x : A) → R x x
    ρ x with Adeq x x
    ... | inl p = *
    ... | inr np = np refl
    f : (x y : A) → R x y → x ≡ y
    f x y with Adeq x y
    ... | inl p = λ {* → p}
    ... | inr np = λ ()

  -- 12.4 General Truncation Levels
data 𝕋 : Set where
  -2𝕋 : 𝕋
  succ𝕋 : 𝕋 → 𝕋

ιℕ𝕋 : ℕ → 𝕋
ιℕ𝕋 0ℕ = succ𝕋 (succ𝕋 -2𝕋)
ιℕ𝕋 (succℕ n) = succ𝕋 (ιℕ𝕋 n)

is-trunc : 𝕋 → Set → Set
is-trunc -2𝕋 A = is-contr A
is-trunc (succ𝕋 t) A = (x y : A) → is-trunc t (x ≡ y)

is-trunc-map : {A B : Set} → (k : 𝕋) → (f : A → B) → Set
is-trunc-map {A} {B} k f = (x : B) → is-trunc k (fib f x)

type-is-succ-type : {A : Set} → {t : 𝕋} → is-trunc t A → is-trunc (succ𝕋 t) A
type-is-succ-type {t = -2𝕋} trunctA = λ x y → concat (proj₂ (trunctA) x) (inv (proj₂ (trunctA) y)) , λ {refl → inv (right-inv (proj₂ (trunctA) x))}
type-is-succ-type {t = succ𝕋 t} trunctA x y = type-is-succ-type (trunctA x y)

k-type-has-k-type-ids : {A : Set} → {k : 𝕋} → is-trunc k A → (x y : A) → is-trunc k (x ≡ y)
k-type-has-k-type-ids {k = -2𝕋} truncA x y = type-is-succ-type truncA x y
k-type-has-k-type-ids {k = succ𝕋 k} truncA x y = type-is-succ-type (truncA x y)

equiv-to-same-k-type : {A B : Set} → {k : 𝕋} → A ≃ B → is-trunc k B → is-trunc k A
equiv-to-same-k-type {k = -2𝕋} (e , eequiv) truncB = retr-to-contr-to-contr e (proj₂ eequiv) truncB
equiv-to-same-k-type {k = succ𝕋 k} (e , eequiv) truncB x y =
  equiv-to-same-k-type (ap e , equiv-to-emb e eequiv x y) (truncB (e x) (e y))

emb-to-same-k-type : {A B : Set} → {k : 𝕋} → (f : A → B) → is-emb f → is-trunc (succ𝕋 k) B → is-trunc (succ𝕋 k) A
emb-to-same-k-type f femb truncB x y = equiv-to-same-k-type (ap f , femb x y) (truncB (f x) (f y))

k+1-trunc-map-to-ap-k-trunc : {A B : Set} → {k : 𝕋} → (f : A → B) → is-trunc-map (succ𝕋 k) f → (x y : A) → is-trunc-map k (ap f {x = x} {y = y})
k+1-trunc-map-to-ap-k-trunc {A} {B} {k} f truncf x y fp = equiv-to-same-k-type fibequiv (truncf (f y) (x , fp) (y , refl))
  where
    fibequiv : fib (ap f {x} {y}) fp ≃ ((x , fp) ≡ (y , refl {a = f y}))
    fibequiv = (λ {(refl , refl) → eq-pair _ _ (refl , refl)}) , (((λ {refl → refl , refl}) , λ {refl → refl}) , ((λ {refl → refl , refl}) , λ {(refl , refl) → refl}))

ap-k-trunc-to-k+1-trunc-map : {A B : Set} → {k : 𝕋} → (f : A → B) → ((x y : A) → is-trunc-map k (ap f {x} {y})) → is-trunc-map (succ𝕋 k) f
ap-k-trunc-to-k+1-trunc-map f apftrunc b (x , p) (y , q) =
  equiv-to-same-k-type (pair-eq (x , p) (y , q) , pair-eq-is-equiv (x , p) (y , q))
    (equiv-to-same-k-type (tot Eq-to-fib , fam-equiv-to-tot-equiv Eq-to-fib Eq-to-fib-equiv)
      (apftrunc x y (concat p (inv q))))
  where
    inv-bridge : (α : x ≡ y) → inv (concat (inv (ap f α)) p) ≡ concat (inv p) (ap f α)
    inv-bridge α = concat (distrib-inv-concat (inv (ap f α)) p)
                          (ap (concat (inv p)) (inv-inv (ap f α)))
    cancel-path : (α : x ≡ y) → concat p (concat (inv p) (ap f α)) ≡ ap f α
    cancel-path α = concat (inv (assoc p (inv p) (ap f α)))
                      (concat (ap (λ e → concat e (ap f α)) (right-inv p))
                              (left-unit (ap f α)))
    Eq-to-fib : (α : x ≡ y) → tr (λ z → f z ≡ b) α p ≡ q → ap f α ≡ concat p (inv q)
    Eq-to-fib α h =
      concat (inv (cancel-path α))
        (ap (concat p)
          (concat (inv (inv-bridge α))
            (ap inv (concat (inv (tr-fib f α p)) h))))
    Eq-to-fib-equiv : (α : x ≡ y) → is-equiv (Eq-to-fib α)
    Eq-to-fib-equiv α =
      equiv-comp
        (λ h → concat (inv (tr-fib f α p)) h)
        (λ e → concat (inv (cancel-path α)) (ap (concat p) (concat (inv (inv-bridge α)) (ap inv e))))
        (is-equiv-concat (inv (tr-fib f α p)))
        (equiv-comp
          (ap inv)
          (λ e → concat (inv (cancel-path α)) (ap (concat p) (concat (inv (inv-bridge α)) e)))
          (equiv-to-emb inv (is-equiv-inv (f y) b) (concat (inv (ap f α)) p) q)
          (equiv-comp
            (concat (inv (inv-bridge α)))
            (λ e → concat (inv (cancel-path α)) (ap (concat p) e))
            (is-equiv-concat (inv (inv-bridge α)))
            (equiv-comp
              (ap (concat p))
              (concat (inv (cancel-path α)))
              (equiv-to-emb (concat p) (is-equiv-concat p) (concat (inv p) (ap f α)) (inv q))
              (is-equiv-concat (inv (cancel-path α))))))

-- Exercises
-- 12.1

𝟚-set : is-set 𝟚
𝟚-set true true refl refl = refl , λ {refl → refl}
𝟚-set false false refl refl = refl , λ {refl → refl}

𝟚-set-obseq : is-set 𝟚
𝟚-set-obseq = rfl-prop-rel-to-set Eq-𝟚 propR ρ (λ b1 b2 → proj₂ (≡-iff-Eq𝟚 b1 b2))
  where
    propR : (b1 b2 : 𝟚) → is-prop (Eq-𝟚 b1 b2)
    propR true  true  = unit-prop
    propR true  false = empty-prop
    propR false true  = empty-prop
    propR false false = unit-prop
    ρ : (b : 𝟚) → Eq-𝟚 b b
    ρ true  = *
    ρ false = *

-- 12.2

is-poset : (A : Set) → (_≤A_ : A → A → Set) → Set
is-poset A _≤A_ = (((a b : A) → is-prop (a ≤A b)) × ((x : A) → x ≤A x) × ((a b : A) → a ≤A b → b ≤A a → a ≡ b) × ((a b c : A) → a ≤A b → b ≤A c → a ≤A c))

prop-× : {A B : Set} → is-prop A → is-prop B → is-prop (A × B)
prop-× {A} {B} Aprop Bprop (a , b) (a' , b') =
  equiv-contr-to-contr
    (pair-eq (a , b) (a' , b'))
    (retr-to-contr-to-contr proj₁
      ( (λ α → α , proj₁ (Bprop (tr (λ (_ : A) → B) α b) b'))
      , λ { (α , h) → ap (λ e → (α , e)) (inv (proj₂ (Bprop (tr (λ (_ : A) → B) α b) b') h)) } )
      (Aprop a a'))
    (pair-eq-is-equiv (a , b) (a' , b'))

poset-is-set : {A : Set} → {≤A : A → A → Set} → is-poset A ≤A → is-set A
poset-is-set {A} {≤A} (≤prop , (≤rfl , (≤antisym , ≤trans))) = 
  rfl-prop-rel-to-set (λ a b → (≤A a  b) × (≤A b a)) (λ a b → prop-× (≤prop a b) (≤prop b a)) (λ x → ≤rfl x , (≤rfl x)) (λ {a b (a≤b , b≤a) → ≤antisym a b a≤b b≤a})

-- 12.3
inj-to-set-is-emb : {A B : Set} → (f : A → B) → ((x y : A) → (f x ≡ f y) → (x ≡ y)) → is-set B → is-emb f
inj-to-set-is-emb f finj Bset a a' = (finj a a' , λ {fafa' → proj₁ (Bset (f a) (f a') ((ap f ∘ finj a a') fafa') fafa')}) , ((finj a a') , (λ {refl → proj₁ (Aset a a (finj a a refl) refl)}))
  where
    Aset = rfl-prop-rel-to-set (λ a b → f a ≡ f b) (λ a b → Bset (f a) (f b)) (λ _ → refl) finj

inj-into-set-to-set : {A B : Set} → (f : A → B) → ((x y : A) → f x ≡ f y → x ≡ y) → is-set B → is-set A
inj-into-set-to-set f finj Bset = emb-to-same-k-type f (inj-to-set-is-emb f finj Bset) Bset

left-+ℕ-emb : (m : ℕ) → is-emb (λ (n : ℕ) → m +ℕ n)
left-+ℕ-emb m = inj-to-set-is-emb (λ n → m +ℕ n)
  (λ n n' p → proj₂ (add-injℕ n n' m)
    (concat (inv (add-commℕ m n)) (concat p (add-commℕ m n'))))
  ℕ-set

≤-propℕ : (m n : ℕ) → is-prop (m ≤ℕ n)
≤-propℕ 0ℕ 0ℕ = unit-prop
≤-propℕ 0ℕ (succℕ n) = unit-prop
≤-propℕ (succℕ m) (succℕ n) = ≤-propℕ m n

≤-Σ-+ℕ-≡ℕ : (m n : ℕ) → (m ≤ℕ n) ≃ Σ ℕ (λ k → m +ℕ k ≡ n)
≤-Σ-+ℕ-≡ℕ m n = iff-to-≃ (≤-propℕ m n) (emb-to-fib-prop _ (left-+ℕ-emb m) n) (forward m n , backward m n)
  where
  forward : (m n : ℕ) → (m ≤ℕ n) → Σ ℕ (λ k → m +ℕ k ≡ n)
  forward 0ℕ 0ℕ * = 0ℕ , refl
  forward 0ℕ (succℕ n) * = succℕ n , zero-addℕ (succℕ n)
  forward (succℕ m) (succℕ n) mlen = (k , concat (succ-addℕ m k) (ap succℕ p))
    where
      k = proj₁ (forward m n mlen)
      p = proj₂ (forward m n mlen)
  backward : (m n : ℕ) → Σ ℕ (λ k → m +ℕ k ≡ n) → (m ≤ℕ n)
  backward 0ℕ 0ℕ (k , p) = *
  backward 0ℕ (succℕ n) (k , p) = *
  backward (succℕ m) 0ℕ (k , p) = ex-falso (zero-ne-succℕ (m +ℕ k) (concat (inv p) (succ-addℕ m k)))
  backward (succℕ m) (succℕ n) (k , p) = backward m n (k , proj₂ (succ-injℕ (m +ℕ k) n) (concat (inv (succ-addℕ m k)) p)) 

  left-·ℕ-emb : (m : ℕ) → is-emb (λ (n : ℕ) → succℕ m ·ℕ n)
  left-·ℕ-emb m = inj-to-set-is-emb (λ n → succℕ m ·ℕ n)
    (λ n n' p → proj₂ (mul-injℕ n n' m)
      (concat (inv (mul-commℕ (succℕ m) n)) (concat p (mul-commℕ (succℕ m) n'))))
    ℕ-set

divℕ-prop : (d n : ℕ) → is-prop (succℕ d ∣ n)
divℕ-prop d n = emb-to-fib-prop _ (inj-to-set-is-emb (λ k → k ·ℕ succℕ d)
  (λ k k' p → proj₂ (mul-injℕ k k' d) p) ℕ-set) n

-- 12.4
contr-⊎-not-contr : {A B : Set} → is-contr A → is-contr B → ¬ (is-contr (A ⊎ B))
contr-⊎-not-contr (a , eqa) (b , eqb) (inl x , eqx) = proj₁ (inr-≡-inl-equiv b x) (eqx (inr b))
contr-⊎-not-contr (a , eqa) (b , eqb) (inr y , eqy) = proj₁ (inl-≡-inr-equiv a y) (eqy (inl a))

infix 1 _⊕_
_⊕_ : Set → Set → Set
P ⊕ Q = (P × ¬ Q) ⊎ (Q × ¬ P)

contr-⊎-to-⊕ : {P Q : Set} → is-contr (P ⊎ Q) → P ⊕ Q
contr-⊎-to-⊕ {P} {Q} (inl p , eqpq) = inl (p , λ q → proj₁ (inr-≡-inl-equiv q p) (eqpq (inr q)))
contr-⊎-to-⊕ {P} {Q} (inr q , eqpq) = inr (q , (λ p → (proj₁ (inl-≡-inr-equiv p q) (eqpq (inl p)))))

⊕-to-contr-⊎ : {P Q : Set} → P ⊕ Q → is-prop P → is-prop Q → is-contr (P ⊎ Q)
⊕-to-contr-⊎ (inl (p , nq)) Pprop Qprop = inl p , λ {(inl x) → ap inl (proj₁ (Pprop x p))
                                       ; (inr x) → ex-falso (nq x)}
⊕-to-contr-⊎ (inr (q , np)) Pprop Qprop = (inr q) , (λ {(inl x) → ex-falso (np x)
                                                      ; (inr x) → ap inr (proj₁ (Qprop x q))})

prop-⊎-to-to-neg : {P Q : Set} → is-prop P → is-prop Q → is-prop (P ⊎ Q) → P → ¬ Q
prop-⊎-to-to-neg Pprop Qprop PQprop p q = (proj₁ (inl-≡-inr-equiv p q)) (proj₁ (PQprop (inl p) (inr q)))

to-neg-to-prop-⊎ : {P Q : Set} → is-prop P → is-prop Q → (P → ¬ Q) → is-prop (P ⊎ Q)
to-neg-to-prop-⊎ Pprop Qprop pnq (inl p) (inl p') = (ap inl (proj₁ (Pprop p p'))) , (λ {refl → ap (ap inl) (proj₂ (Pprop p p) refl)})
to-neg-to-prop-⊎ Pprop Qprop pnq (inl p) (inr q) = ex-falso (pnq p q)
to-neg-to-prop-⊎ Pprop Qprop pnq (inr q) (inl p) = ex-falso (pnq p q)
to-neg-to-prop-⊎ Pprop Qprop pnq (inr q) (inr q') = (ap inr (proj₁ (Qprop q q'))) , (λ {refl → ap (ap inr) (proj₂ (Qprop q q) refl)})

k+2-⊎-is-k+2 : {P Q : Set} → {k : 𝕋} → is-trunc (succ𝕋 (succ𝕋 k)) P → is-trunc (succ𝕋 (succ𝕋 k)) Q → is-trunc (succ𝕋 (succ𝕋 k)) (P ⊎ Q)
k+2-⊎-is-k+2 Ptrunc Qtrunc (inl p) (inl p') = equiv-to-same-k-type (inl-≡-inl-equiv p p') (Ptrunc p p')
k+2-⊎-is-k+2 Ptrunc Qtrunc (inl p) (inr q)  = equiv-to-same-k-type (inl-≡-inr-equiv p q) (λ ())
k+2-⊎-is-k+2 Ptrunc Qtrunc (inr q) (inl p)  = equiv-to-same-k-type (inr-≡-inl-equiv q p) (λ ())
k+2-⊎-is-k+2 Ptrunc Qtrunc (inr q) (inr q') = equiv-to-same-k-type (inr-≡-inr-equiv q q') (Qtrunc q q')

-- Tangent to prove our construction of ℤ is equivalent to Rijke's
ℤ-≃-ℕ⊎𝟙⊎ℕ : ℤ ≃ (ℕ ⊎ (𝟙 ⊎ ℕ))
ℤ-≃-ℕ⊎𝟙⊎ℕ =
  f , ((g , λ { (inl n) → refl ; (inr (inl *)) → refl ; (inr (inr n)) → refl })
     , (g , λ { 0ℤ → refl ; (in-neg n) → refl ; (in-pos n) → refl }))
  where
    f : ℤ → ℕ ⊎ (𝟙 ⊎ ℕ)
    f 0ℤ        = inr (inl *)
    f (in-neg n) = inl n
    f (in-pos n) = inr (inr n)
    g : ℕ ⊎ (𝟙 ⊎ ℕ) → ℤ
    g (inl n)        = in-neg n
    g (inr (inl *))  = 0ℤ
    g (inr (inr n))  = in-pos n

unit-set : is-set 𝟙
unit-set * * refl refl = refl , (λ {refl → refl})

ℤ-set : is-set ℤ
ℤ-set = equiv-to-same-k-type ℤ-≃-ℕ⊎𝟙⊎ℕ (k+2-⊎-is-k+2 ℕ-set (k+2-⊎-is-k+2 unit-set ℕ-set))

-- 12.5
δ : (A : Set) → A → A × A
δ A x = x , x

equiv-diag-to-prop : {A : Set} → is-equiv (δ A) → is-prop A
equiv-diag-to-prop ((f , δf) , (g , gδ)) a b =
  type-is-succ-type
    (a , λ x → concat (inv (ap proj₂ (δf (a , x)))) (ap proj₁ (δf (a , x))))
    a b

prop-to-equiv-diag : {A : Set} → is-prop A → is-equiv (δ A)
prop-to-equiv-diag propA = ((λ {(a , b) → a}) , λ {(a , b) → eq-pair _ _ (refl , proj₁ (propA a b))}) , (((λ {(a , b) → a}) , λ {a → refl}))

fib-δ-≃-≡ : {A : Set} → (x y : A) → fib (δ A) (x , y) ≃ (x ≡ y)
fib-δ-≃-≡ x y = (λ {(a , refl) → refl}) , (((λ {refl → x , refl}) , λ {refl → refl}) , ((λ {refl → x , refl}) , λ {(x , refl) → refl}))

k+1-trunc-to-diag-k-trunc : {A : Set} → {k : 𝕋} → is-trunc (succ𝕋 k) A → is-trunc-map k (δ A)
k+1-trunc-to-diag-k-trunc Atrunc (x , y) = equiv-to-same-k-type (fib-δ-≃-≡ x y) (Atrunc x y)

diag-k-trunc-to-k+1-trunc : {A : Set} → {k : 𝕋} → is-trunc-map k (δ A) → is-trunc (succ𝕋 k) A
diag-k-trunc-to-k+1-trunc {A} {k} diagtrunc x y = equiv-to-same-k-type (inv-≃ (fib-δ-≃-≡ x y)) (diagtrunc (x , y))

-- 12.6
fam-trunc-to-Σ-trunc : {A : Set} → {B : A → Set} → {k : 𝕋} → is-trunc k A → ((x : A) → is-trunc k (B x)) → is-trunc k (Σ A B)
fam-trunc-to-Σ-trunc {k = -2𝕋} Acontr aBcontr = (a , b) , λ { (x , y) → eq-pair _ _ (proj₂ Acontr x , proj₂ (aBcontr a) (tr _ (proj₂ Acontr x) y)) }
  where
    a = proj₁ Acontr
    b = proj₁ (aBcontr a)
fam-trunc-to-Σ-trunc {k = succ𝕋 k} Atrunc aBtrunc (a , b) (a' , b') =
  equiv-to-same-k-type
    (pair-eq (a , b) (a' , b') , pair-eq-is-equiv (a , b) (a' , b'))
    (fam-trunc-to-Σ-trunc (Atrunc a a') (λ p → aBtrunc a' (tr _ p b) b'))

Σ-trunc-to-fam-trunc : {A : Set} → {B : A → Set} → {k : 𝕋} → is-trunc k A → is-trunc k (Σ A B)  → ((x : A) → is-trunc k (B x)) 
Σ-trunc-to-fam-trunc Atrunc ABtrunc a =
  equiv-to-same-k-type
    (inv-≃ (_ , is-equiv-fib-proj₁ a))
    (fam-trunc-to-Σ-trunc ABtrunc (λ s → k-type-has-k-type-ids Atrunc (proj₁ s) a))

trunc-to-trunc-map : {A B : Set} → {k : 𝕋} → (f : A → B) → is-trunc k B → is-trunc k A → is-trunc-map k f
trunc-to-trunc-map {A} {B} {k} f Btrunc Atrunc b = fam-trunc-to-Σ-trunc Atrunc (λ a → k-type-has-k-type-ids Btrunc (f a) b)

-- 12.7
trunc-funs-to-prod-trunc : {A B : Set} {k : 𝕋} → (B → is-trunc (succ𝕋 k) A) → (A → is-trunc (succ𝕋 k) B) → is-trunc (succ𝕋 k) (A × B)
trunc-funs-to-prod-trunc f g (a , b) (x , y) = equiv-to-same-k-type ((pair-eq _ _) , (pair-eq-is-equiv _ _)) (fam-trunc-to-Σ-trunc (f b a x) λ {refl → g a b y})

retr-k-type : {A B : Set} → {k : 𝕋} → (f : A → B) → retr f → is-trunc k B → is-trunc k A
retr-k-type {k = -2𝕋} f (g , gf) (b , eqb) = (g b) , λ x → concat (inv (gf x)) (ap g (eqb (f x)))
retr-k-type {k = succ𝕋 k} f (g , gf) Btrunc a a' = 
  retr-k-type {k = k} 
    (ap f) 
    ((λ fafa' → concat (inv (gf a)) (concat (ap g (fafa')) (gf a'))) , 
      λ {refl → concat (ap (concat (inv (gf a))) (left-unit (gf a))) (left-inv (gf a))}) 
    (Btrunc (f a) (f a'))

prod-trunc-to-trunc-funs : {A B : Set} {k : 𝕋} → is-trunc (succ𝕋 k) (A × B) → (B → is-trunc (succ𝕋 k) A) × (A → is-trunc (succ𝕋 k) B)
prod-trunc-to-trunc-funs ABtrunc =
  (λ b → retr-k-type (λ z → (z , b)) (proj₁ , λ _ → refl) ABtrunc) ,
  (λ a → retr-k-type (λ z → (a , z)) (proj₂ , λ _ → refl) ABtrunc)


fac-trunc-to-prod-trunc : {A B : Set} {k : 𝕋} → is-trunc k A → is-trunc k B → is-trunc k (A × B)
fac-trunc-to-prod-trunc {k = -2𝕋} (a , eqa) (b , eqb) = (a , b) , λ {(x , y) → eq-pair _ _ ((eqa x) , (eqb (tr (λ _ → _) (eqa x) y)))}
fac-trunc-to-prod-trunc {k = succ𝕋 k} Atrunc Btrunc = trunc-funs-to-prod-trunc (λ b → Atrunc) λ a → Btrunc

inhab-prod-trunc-to-fac-trunc : {A B : Set} {k : 𝕋} → A → B → is-trunc k (A × B) → is-trunc k A × is-trunc k B
inhab-prod-trunc-to-fac-trunc {k = -2𝕋} a b ABcontr = prod-contr-to-contr ABcontr
inhab-prod-trunc-to-fac-trunc {k = succ𝕋 k} a b ABtrunc = f b , g a
  where
    funs = prod-trunc-to-trunc-funs (ABtrunc)
    f = proj₁ funs
    g = proj₂ funs

-- 12.8
retr-ap : {A B : Set} (i : A → B) → retr i → {x y : A} → retr (ap i {x = x} {y = y})
retr-ap i (f , fi) {x = x} {y = y} = (λ {ixiy → concat (inv (fi x)) (concat (ap f ixiy) (fi y))}) , λ {refl → concat  (ap (concat (inv (fi x))) (left-unit (fi x))) (left-inv (fi x))}

-- 12.8b is retr-k-type proven earlier

-- 12.9

tail-List : {A : Set} → List A → List A
tail-List []       = []
tail-List (_ ∷ l)  = l

nil-ne-cons : {A : Set} (a : A) (l : List A) → ¬ ([] ≡ a ∷ l)
nil-ne-cons a l p = tr (λ { [] → 𝟙 ; (_ ∷ _) → 𝟘 }) p *

fib-concat-List : {A : Set} → List A → Set
fib-concat-List {A} lst = fib (λ (p : List A × List A) → concat-List (proj₁ p) (proj₂ p)) lst

fib-concat-nil : {A : Set} → is-contr (fib-concat-List {A} [])
fib-concat-nil =
  (([] , []) , refl) ,
  λ { (([]     , .[]) , refl) → refl
    ; (((a ∷ l₀) , l') , p)  → ex-falso (nil-ne-cons a (concat-List l₀ l') (inv p)) }

fib-concat-cons : {A : Set} (a : A) (lst' : List A)
  → fib-concat-List (a ∷ lst') ≃ (𝟙 ⊎ fib-concat-List lst')
fib-concat-cons {A} a lst' = fwd , ((bwd , sec-htpy) , (bwd , retr-htpy))
  where
    head-fn : List A → A
    head-fn []      = a
    head-fn (c ∷ _) = c

    fwd : fib-concat-List (a ∷ lst') → 𝟙 ⊎ fib-concat-List lst'
    fwd (([]       , l') , p) = inl *
    fwd (((b ∷ l₀) , l') , p) = inr ((l₀ , l') , ap tail-List p)

    bwd : 𝟙 ⊎ fib-concat-List lst' → fib-concat-List (a ∷ lst')
    bwd (inl *)               = (([] , (a ∷ lst')) , refl)
    bwd (inr ((l₀ , l') , q)) = (((a ∷ l₀) , l') , ap (a ∷_) q)

    sec-htpy : fwd ∘ bwd ∼ id
    sec-htpy (inl *) = refl
    sec-htpy (inr ((l₀ , l') , q)) =
      ap (λ t → inr ((l₀ , l') , t)) (concat (ap-comp (a ∷_) tail-List q) (ap-id q))

    cons-path-split : (b : A) (xs : List A) (c : A) (ys : List A) → (p : b ∷ xs ≡ c ∷ ys)
      → p ≡ concat (ap (λ d → d ∷ xs) (ap head-fn p)) (ap (c ∷_) (ap tail-List p))
    cons-path-split b xs .b .xs refl = refl

    retr-htpy : bwd ∘ fwd ∼ id
    retr-htpy (([]       , .(a ∷ lst')) , refl) = refl
    retr-htpy (((b ∷ l₀) , l')         , p)    =
      eq-pair (((a ∷ l₀) , l') , ap (a ∷_) te) (((b ∷ l₀) , l') , p) (pair-h , pp)
      where
        he     = ap head-fn p
        te     = ap tail-List p
        pair-h = ap (λ c → ((c ∷ l₀) , l')) (inv he)
        pp     =
          concat (tr-fib (λ lr → concat-List (proj₁ lr) (proj₂ lr)) pair-h (ap (a ∷_) te))
          (concat (ap (λ q → concat q (ap (a ∷_) te))
                     (concat
                       (ap inv (ap-comp (λ c → ((c ∷ l₀) , l'))
                                        (λ lr → concat-List (proj₁ lr) (proj₂ lr))
                                        (inv he)))
                       (concat (ap inv (ap-inv (λ c → c ∷ concat-List l₀ l') he))
                               (inv-inv (ap (λ c → c ∷ concat-List l₀ l') he)))))
                  (inv (cons-path-split b (concat-List l₀ l') a lst' p)))

list-concat-0-trunc : {A : Set} → is-trunc-map (succ𝕋 (succ𝕋 -2𝕋)) (λ (p : List A × List A) → concat-List (proj₁ p) (proj₂ p))
list-concat-0-trunc {A} lst = ind lst
  where
    ind : (lst : List A) → is-trunc (succ𝕋 (succ𝕋 -2𝕋)) (fib-concat-List lst)
    ind []        = type-is-succ-type (type-is-succ-type fib-concat-nil)
    ind (a ∷ lst') = equiv-to-same-k-type (fib-concat-cons a lst') (k+2-⊎-is-k+2 unit-set (ind lst'))

-- 12.10
k+1-trunc-to-const-k-trunc : {A : Set} → {k : 𝕋} → is-trunc (succ𝕋 k) A → (x : A) → is-trunc-map k (const {𝟙} {A} {x})
k+1-trunc-to-const-k-trunc Atrunc x a = equiv-to-same-k-type ((λ {(* , p) → p}) , 
  (((_,_ *) , λ x₁ → refl) , ((_,_ *) , λ {(* , p) → refl}))) 
  (Atrunc (const *) a)

const-k-trunc-to-k+1-trunc : {A : Set} → {k : 𝕋} → ((x : A) → is-trunc-map k (const {𝟙} {A} {x})) → is-trunc (succ𝕋 k) A
const-k-trunc-to-k+1-trunc constTrunc a x =
  equiv-to-same-k-type
    (inv-≃ ((λ {(* , p) → p}) , (((_,_ *) , λ x₁ → refl) , ((_,_ *) , λ {(* , p) → refl}))))
    (constTrunc a x)

-- 12.11
fib-htpy-equiv : {A B : Set} → (f f' : A → B) → f ∼ f' → (y : B) → fib f y ≃ fib f' y
fib-htpy-equiv f f' Hf y =
  tot (λ a → concat (inv (Hf a))) ,
  fam-equiv-to-tot-equiv (λ a → concat (inv (Hf a))) (λ a → is-equiv-concat (inv (Hf a)))

fib-fib-triangle-≃-fib-h : {A B X : Set} → (f : A → X) → (g : B → X) → (h : A → B)
  → (H : triangle-commutes f h g) → (x : X) → (w : fib g x)
  → fib (fib-triangle f g h H x) w ≃ fib h (proj₁ w)
fib-fib-triangle-≃-fib-h f g h H x w =
  concat-≃
    (fib-htpy-equiv (fib-triangle f g h H x) (base-change h D ∘ tot g') (λ { (a , p) → refl }) w)
    (concat-≃
      ( base-change (tot g') (λ z → base-change h D z ≡ w)
      , f-equiv-to-base-change-equiv (tot g') (λ z → base-change h D z ≡ w) g'-equiv)
      (fib-base-change-equiv-fib h D w))
  where
    D : _ → Set
    D b = g b ≡ x
    g' : (a : _) → (f a ≡ x) → (g (h a) ≡ x)
    g' a = concat (inv (H a))
    g'-equiv : is-equiv (tot g')
    g'-equiv = fam-equiv-to-tot-equiv g' (λ a → is-equiv-concat (inv (H a)))

comm-tri-k-trunc-g-to-k-trunc-h-to-k-trunc-f : {A B X : Set} {k : 𝕋}
  → (f : A → X) → (g : B → X) → (h : A → B)
  → triangle-commutes f h g → is-trunc-map k g → is-trunc-map k h
  → is-trunc-map k f
comm-tri-k-trunc-g-to-k-trunc-h-to-k-trunc-f f g h H kg kh x =
  equiv-to-same-k-type
    (proj₁ (fib-repl (fib-triangle f g h H x)))
    (fam-trunc-to-Σ-trunc (kg x)
      (λ w → equiv-to-same-k-type (fib-fib-triangle-≃-fib-h f g h H x w) (kh (proj₁ w))))

comm-tri-k-trunc-g-to-k-trunc-f-to-k-trunc-h : {A B X : Set} {k : 𝕋}
  → (f : A → X) → (g : B → X) → (h : A → B)
  → triangle-commutes f h g → is-trunc-map k g → is-trunc-map k f
  → is-trunc-map k h
comm-tri-k-trunc-g-to-k-trunc-f-to-k-trunc-h f g h H kg kf b =
  equiv-to-same-k-type
    (inv-≃ (fib-fib-triangle-≃-fib-h f g h H (g b) (b , refl)))
    (trunc-to-trunc-map (fib-triangle f g h H (g b)) (kg (g b)) (kf (g b)) (b , refl))

-- 12.12
fam-k-trunc-map-to-tot-k-trunc-map : {A : Set} → {B C : A → Set} → {k : 𝕋}
  → (f : (x : A) → B x → C x)
  → ((x : A) → is-trunc-map k (f x))
  → is-trunc-map k (tot f)
fam-k-trunc-map-to-tot-k-trunc-map {A} {B} {C} {k} f famtrunc (a , c) = equiv-to-same-k-type (fib-tot-equiv-fib (λ x → f x) ((a , c))) (famtrunc a c)

tot-k-trunc-map-to-fam-k-trunc-map : {A : Set} → {B C : A → Set} → {k : 𝕋}
  → (f : (x : A) → B x → C x)
  → is-trunc-map k (tot f)
  → ((x : A) → is-trunc-map k (f x))
tot-k-trunc-map-to-fam-k-trunc-map f tottrunc a ca = equiv-to-same-k-type (inv-≃ (fib-tot-equiv-fib f ((a , ca)))) (tottrunc (a , ca))

-- 12.13
fib-incl : {A : Set} → (B : A → Set) → (a : A) → B a → Σ A B
fib-incl B a y = a , y

fib-fib-incl-≃-≡ : {A : Set} → (B : A → Set) → (a x : A) → (bx : B x)
  → fib (fib-incl B a) (x , bx) ≃ (a ≡ x)
fib-fib-incl-≃-≡ B a x bx =
  (λ {(ba , refl) → refl}) ,
  ( ((λ {refl → bx , refl}) , λ {refl → refl})
  , ((λ {refl → bx , refl}) , λ {(ba , refl) → refl}))

k+1-trunc-to-fib-incl-k-trunc : {A : Set} → {k : 𝕋}
  → is-trunc (succ𝕋 k) A
  → (B : A → Set) → (a : A) → is-trunc-map k (fib-incl B a)
k+1-trunc-to-fib-incl-k-trunc Atrunc B a (x , bx) =
  equiv-to-same-k-type (fib-fib-incl-≃-≡ B a x bx) (Atrunc a x)

fib-incl-k-trunc-to-k+1-trunc : {A : Set} → {k : 𝕋}
  → ((B : A → Set) → (a : A) → is-trunc-map k (fib-incl B a))
  → is-trunc (succ𝕋 k) A
fib-incl-k-trunc-to-k+1-trunc BatruncBa a a' = equiv-to-same-k-type (inv-≃ (fib-fib-incl-≃-≡ (λ _ → 𝟙) a a' *)) (BatruncBa (λ _ → 𝟙) a (a' , *))

set-to-fib-incl-emb : {A : Set}
  → is-set A
  → (B : A → Set) → (a : A) → is-emb (fib-incl B a)
set-to-fib-incl-emb Aset B a = fib-prop-to-emb (λ x → fib-incl B a x) (k+1-trunc-to-fib-incl-k-trunc Aset B a)

-- 12.14
is-isolated : {A : Set} → (a : A) → Set
is-isolated {A} a = (x : A) → ((a ≡ x) ⊎ ¬ (a ≡ x))

isolated-to-const-dec-fib : {A : Set} → (a : A) → is-isolated a → (x : A) → is-decidable (fib (const {𝟙} {A} {a}) x)
isolated-to-const-dec-fib {A} a aiso x with (aiso x)
... | inl p = inl (* , p)
... | inr np = inr λ {(* , refl) → np refl}

const-dec-fib-to-isolated : {A : Set} → (a : A) → ((x : A) → is-decidable (fib (const {𝟙} {A} {a}) x)) → is-isolated a
const-dec-fib-to-isolated a xdecfib x with (xdecfib x)
... | inl (* , aeqx) = inl aeqx
... | inr np = inr λ z → np (* , z)

isolated-to-eq-prop : {A : Set} → (a : A) → is-isolated a → (x : A) → is-prop (a ≡ x)
isolated-to-eq-prop {A} a aiso x = emb-𝟙-to-is-prop (inhab-contr-to-emb-𝟙 (is-prop'-to-inhab-contr all-paths-eq))
  where 
    collapse-path : (y : A) → a ≡ y → a ≡ y
    collapse-path y p with aiso y
    ... | inl q = q
    ... | inr nq = ex-falso (nq p)

    collapse-path-eq : (y : A) → (p q : a ≡ y) → collapse-path y p ≡ collapse-path y q
    collapse-path-eq y p q with aiso y
    ... | inl aeqy = refl
    ... | inr aneqy = ex-falso (aneqy p)

    collapse-factor : (y : A) → (p : a ≡ y) → p ≡ concat (inv (collapse-path a refl)) (collapse-path y p)
    collapse-factor y refl = inv (left-inv (collapse-path a refl))

    all-paths-eq : (p q : a ≡ x) → p ≡ q
    all-paths-eq p q =
      concat (collapse-factor x p)
        (concat (ap (concat (inv (collapse-path a refl))) (collapse-path-eq x p q))
                (inv (collapse-factor x q)))

isolated-to-const-emb : {A : Set} → (a : A) → is-isolated a → is-emb (const {𝟙} {A} {a})
isolated-to-const-emb {A} a aiso = fib-prop-to-emb (const {𝟙} {A} {a})
  (λ b → proj₂ (≃-to-iff-prop ((λ {(* , p) → p}) , (((_,_ *) , λ _ → refl) , ((_,_ *) , λ {(* , p) → refl})))) (isolated-to-eq-prop a aiso b))