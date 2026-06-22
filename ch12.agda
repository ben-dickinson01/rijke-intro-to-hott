{-# OPTIONS --without-K #-}
module ch12 where

open import ch11 public

is-prop : (A : Set) → Set
is-prop A = (x y : A) → is-contr (x ≡ y)

Prop : Set₁
Prop = Σ Set is-prop

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