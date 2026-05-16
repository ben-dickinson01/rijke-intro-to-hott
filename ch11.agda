module ch11 where

open import ch10 public

equiv-comp : {A B C : Set} → (f : A → B) → (g : B → C)
  → is-equiv f → is-equiv g → is-equiv (g ∘ f)
equiv-comp f g ((hf , fhf) , (kf , kff)) ((hg , fhg) , (kg , kfg)) =
  ( ((λ z → hf (hg z)) , λ z → concat (ap g (fhf (hg z))) (fhg z))
  , ((λ z → kf (kg z)) , λ x → concat (ap kf (kfg (f x))) (kff x))
  )

is-equiv-fam : {A : Set} → {B C : A → Set} → (f : (x : A) → B x → C x) → Set
is-equiv-fam {A} f = (x : A) → is-equiv (f x)

tot : {A : Set} → {B C : A → Set} → (f : (x : A) → (B x → C x)) → Σ A B → Σ A C

tot f x = proj₁ x , f (proj₁ x) (proj₂ x)

fib-tot-equiv-fib : {A : Set} → {B C : A → Set} → (f : (x : A) → B x → C x) → (t : Σ A C) → fib (tot f) t ≃ fib (f (proj₁ t)) (proj₂ t)
fib-tot-equiv-fib {A} {B} {C} f (a , c) = (λ { ((a , b) , refl) → b , refl}) , (((λ { (bta , p) → (a , bta) , eq-pair (a , f a bta) (a , c) (refl , p)}) , λ { (bta , refl) → refl}) , ((λ { (ba , refl) → (a , ba) , refl}) , λ { ((a , b) , refl) → refl}))

fam-equiv-to-tot-equiv : {A : Set} → {B C : A → Set} → (f : (x : A) → B x → C x) → is-equiv-fam f → is-equiv (tot f)
fam-equiv-to-tot-equiv {A} {B} {C} f x→equivfx =
  ((λ { (a , c) → a , g a c}) ,
   (λ { (a , c) → eq-pair (a , f a (g a c)) (a , c) (refl , gh a c)})) ,
  ((λ {(a , c) → a , h a c}) , λ { (a , b) → eq-pair (a , h a (f a b)) (a , b) (refl , hh a b)})
  where
    g : (a : A) → C a → B a
    g a = proj₁ (proj₁ (x→equivfx a))
    gh : (a : A) → (c : C a) → f a (g a c) ≡ c
    gh a = proj₂ (proj₁ (x→equivfx a))
    h : (a : A) → C a → B a
    h a = proj₁ (proj₂ (x→equivfx a))
    hh : (a : A) → (b : B a) → h a (f a b) ≡ b
    hh a = proj₂ (proj₂ (x→equivfx a))

tot-equiv-to-fam-equiv : {A : Set} → {B C : A → Set} → (f : (x : A) → B x → C x) → is-equiv (tot f) → is-equiv-fam f
tot-equiv-to-fam-equiv {A} {B} {C} f e a = contr-map-to-equiv (f a) (λ c →
    contr-equiv-to-contr (proj₁ (fib-tot-equiv-fib f (a , c)))
              (equiv-to-contr-map (tot f) e (a , c))
              (proj₂ (fib-tot-equiv-fib f (a , c))))

base-change : {A B : Set} → (f : A → B) → (C : B → Set) → Σ A (λ x → C (f x)) → Σ B C
base-change f C x = f (proj₁ x) , proj₂ x

fib-base-change-equiv-fib : {A B : Set} → (f : A → B) → (C : B → Set) → (t : Σ B C) → fib (base-change f C) t ≃ fib f (proj₁ t)
fib-base-change-equiv-fib f C (b , c) =
  (λ { ((x , z) , refl) → x , refl}) ,
  (((λ { (x , refl) → (x , c) , refl}) , (λ { (x , refl) → refl})) ,
   ((λ { (x , refl) → (x , c) , refl}) , (λ { ((x , z) , refl) → refl})))

f-equiv-to-base-change-equiv : {A B : Set} → (f : A → B) → (C : B → Set) → is-equiv f → is-equiv (base-change f C)
f-equiv-to-base-change-equiv f C e = contr-map-to-equiv (base-change f C) (λ { (b , c) →
  equiv-contr-to-contr (proj₁ (fib-base-change-equiv-fib f C (b , c)))
             (equiv-to-contr-map f e b)
             (proj₂ (fib-base-change-equiv-fib f C (b , c)))})

tot-fam : {A B : Set}  → {C : A → Set} → {D : B → Set}
  → (f : A → B) → (g : (x : A) → C x → D (f x)) → Σ A C → Σ B D
tot-fam f g x = f (proj₁ x) , g (proj₁ x) (proj₂ x)

g-equiv-to-tot-fam-equiv : {A B : Set} → {C : A → Set} → {D : B → Set}
  → (f : A → B) → (g : (x : A) → C x → D (f x))
  → is-equiv f → is-equiv-fam g
  → is-equiv (tot-fam {A} {B} {C} {D} f g)
g-equiv-to-tot-fam-equiv {A} {B} {C} {D} f g f-equiv gx-equiv =
  equiv-comp (tot g) (base-change f D)
             (fam-equiv-to-tot-equiv g gx-equiv)
             (f-equiv-to-base-change-equiv f D f-equiv)
  
tot-fam-equiv-to-g-equiv : {A B : Set} → {C : A → Set} → {D : B → Set}
  → (f : A → B) → (g : (x : A) → C x → D (f x))
  → is-equiv f → is-equiv (tot-fam {A} {B} {C} {D} f g)
  → is-equiv-fam g
tot-fam-equiv-to-g-equiv {A} {B} {C} {D} f g fe te =
  tot-equiv-to-fam-equiv g
    (3-for-2-f-g-to-h (tot-fam f g) (base-change f D) (tot g)
       (λ _ → refl) te (f-equiv-to-base-change-equiv f D fe))

is-id-sys : (A : Set) → (B : A → Set) → (a : A) → (b : B a) → Set₁
is-id-sys A B a b = (P : (x : A) → B x → Set) → sec (λ (h : (x : A) → (y : B x) → P x y) → h a b)

-- FUNDAMENTAL THEOREM OF IDENTITY TYPES
-- i → ii
fam-equiv-to-total-contr : {A : Set} → {a : A} → {B : A → Set} → (b : B a) → (f : (x : A) → (a ≡ x) → B x) → (p : f a refl ≡ b) → is-equiv-fam f → is-contractible (Σ A B)
fam-equiv-to-total-contr {A} {a} {B} b f p f-equiv =
  contr-equiv-to-contr (tot f) (Σ-≡-contractible a) (fam-equiv-to-tot-equiv f f-equiv)

-- ii → iii
total-contr-to-id-sys : {A : Set} → {a : A} → {B : A → Set} → (b : B a) → (f : (x : A) → (a ≡ x) → B x) → (p : f a refl ≡ b) → is-contractible (Σ A B) → is-id-sys A B a b
total-contr-to-id-sys {A} {a} {B} b f p Σ-contr P =
  (λ pab x y → s (x , y) pab) , sh
  where
    P' : Σ A B → Set
    P' z = P (proj₁ z) (proj₂ z)
    si : sec (λ (g : (z : Σ A B) → P' z) → g (a , b))
    si = contr-to-sing-ind (Σ A B) (a , b) Σ-contr P'
    s : (z : Σ A B) → P' (a , b) → P' z
    s z pab = proj₁ si pab z
    sh : (λ (h : (x : A) → (y : B x) → P x y) → h a b) ∘
         (λ pab x y → s (x , y) pab) ∼ id
    sh = proj₂ si

-- iii → i
id-sys-to-fam-equiv : {A : Set} → {a : A} → {B : A → Set} → (b : B a) → (f : (x : A) → (a ≡ x) → B x) → (p : f a refl ≡ b) → is-id-sys A B a b → (x : A) → is-equiv (f x)
id-sys-to-fam-equiv {A} {a} {B} b f refl id-sys x =
  (g-fam x , sec-htpy x) , (g-fam x , retr-htpy x)
  where
    g-sec : sec (λ (h : (x' : A) → (y : B x') → a ≡ x') → h a b)
    g-sec = id-sys (λ x' _ → a ≡ x')
    g-fam : (x' : A) → B x' → a ≡ x'
    g-fam = proj₁ g-sec refl
    g-htpy : g-fam a b ≡ refl
    g-htpy = proj₂ g-sec refl
    sec-htpy : (x' : A) → (y : B x') → f x' (g-fam x' y) ≡ y
    sec-htpy = proj₁ (id-sys (λ x' y → f x' (g-fam x' y) ≡ y)) (ap (f a) g-htpy)
    retr-htpy : (x' : A) → (q : a ≡ x') → g-fam x' (f x' q) ≡ q
    retr-htpy _ refl = g-htpy

-- ii → i (derived)
total-contr-to-fam-equiv : {A : Set} → {a : A} → {B : A → Set} → (b : B a) → (f : (x : A) → (a ≡ x) → B x) → (p : f a refl ≡ b) → is-contractible (Σ A B) → is-equiv-fam f
total-contr-to-fam-equiv b f p Σ-contr =
  id-sys-to-fam-equiv b f p (total-contr-to-id-sys b f p Σ-contr)

Σ-Eqℕ-contr : (m : ℕ) → is-contractible (Σ ℕ (Eq-ℕ m))
Σ-Eqℕ-contr m = (m , rfl-Eq-ℕ m) , contraction m
  where
    contraction : (k : ℕ) → (z : Σ ℕ (Eq-ℕ k)) → z ≡ (k , rfl-Eq-ℕ k)
    contraction 0ℕ (0ℕ , *) = refl
    contraction 0ℕ (succℕ n , ())
    contraction (succℕ k) (0ℕ , ())
    contraction (succℕ k) (succℕ n , e) =
      ap (λ z → succℕ (proj₁ z) , proj₂ z) (contraction k (n , e))

≡-to-Eqℕ : (m n : ℕ) → (m ≡ n) → Eq-ℕ m n
≡-to-Eqℕ m .m refl = rfl-Eq-ℕ m

≡-to-Eqℕ-equiv : (m n : ℕ) → is-equiv (≡-to-Eqℕ m n)
≡-to-Eqℕ-equiv m =
  total-contr-to-fam-equiv (rfl-Eq-ℕ m) (≡-to-Eqℕ m) refl (Σ-Eqℕ-contr m)

is-emb : {A B : Set} → (f : A → B) → Set
is-emb {A} f = (x y : A) → is-equiv (ap f {x} {y})

infix 1 _↪_
_↪_ : (A B : Set) → Set
A ↪ B = Σ (A → B) (λ f → is-emb f)

equiv-to-emb : {A B : Set} → (f : A → B) → is-equiv f → is-emb f
equiv-to-emb {A} {B} f f-equiv x =
  total-contr-to-fam-equiv {A} {x} {λ y → f x ≡ f y}
    refl (λ y p → ap f p) refl
    (contr-equiv-to-contr
       (tot {A} {λ y → f y ≡ f x} {λ y → f x ≡ f y} (λ y → inv))
       (equiv-to-contr-map f f-equiv (f x))
       (fam-equiv-to-tot-equiv (λ y → inv) (λ y → is-equiv-inv (f y) (f x))))

-- Observational equality of coproducts (Definition 11.5.2)
Eq-copr : {A B : Set} → A ⊎ B → A ⊎ B → Set
Eq-copr (inl x) (inl y) = x ≡ y
Eq-copr (inl x) (inr y) = 𝟘
Eq-copr (inr x) (inl y) = 𝟘
Eq-copr (inr x) (inr y) = x ≡ y

rfl-Eq-copr : {A B : Set} → (s : A ⊎ B) → Eq-copr s s
rfl-Eq-copr (inl x) = refl
rfl-Eq-copr (inr y) = refl

-- Lemma 11.5.3
≡-to-Eq-copr : {A B : Set} → (s t : A ⊎ B) → s ≡ t → Eq-copr s t
≡-to-Eq-copr (inl x) .(inl x) refl = refl
≡-to-Eq-copr (inr y) .(inr y) refl = refl

-- Proposition 11.5.4
total-copr-space-contr : {A B : Set} → (s : A ⊎ B) → is-contractible (Σ (A ⊎ B) (Eq-copr s))
total-copr-space-contr (inl x) = (inl x , refl) , λ { (inl x , refl) → refl}
total-copr-space-contr (inr y) = (inr y , refl) , λ { (inr y , refl) → refl}

-- Main theorem: ≡-to-Eq-copr is a family of equivalences (via fundamental theorem 11.2.2)
≡-to-Eq-copr-equiv : {A B : Set} → (s t : A ⊎ B) → is-equiv (≡-to-Eq-copr s t)
≡-to-Eq-copr-equiv {A} {B} (inl x) t =
  total-contr-to-fam-equiv {A ⊎ B} {inl x} {Eq-copr {A} {B} (inl x)}
    (rfl-Eq-copr {A} {B} (inl x)) (≡-to-Eq-copr {A} {B} (inl x))
    refl (total-copr-space-contr {A} {B} (inl x)) t
≡-to-Eq-copr-equiv {A} {B} (inr y) t =
  total-contr-to-fam-equiv {A ⊎ B} {inr y} {Eq-copr {A} {B} (inr y)}
    (rfl-Eq-copr {A} {B} (inr y)) (≡-to-Eq-copr {A} {B} (inr y))
    refl (total-copr-space-contr {A} {B} (inr y)) t

-- Theorem 11.5.1 (corollaries of ≡-to-Eq-copr-equiv by definitional unfolding of Eq-copr)
inl-≡-inl-equiv : {A B : Set} → (x x' : A) → (inl {A} {B} x ≡ inl x') ≃ (x ≡ x')
inl-≡-inl-equiv x x' = ≡-to-Eq-copr (inl x) (inl x') , ≡-to-Eq-copr-equiv (inl x) (inl x')

inl-≡-inr-equiv : {A B : Set} → (x : A) → (y' : B) → (inl {A} {B} x ≡ inr y') ≃ 𝟘
inl-≡-inr-equiv x y' = ≡-to-Eq-copr (inl x) (inr y') , ≡-to-Eq-copr-equiv (inl x) (inr y')

inr-≡-inl-equiv : {A B : Set} → (y : B) → (x' : A) → (inr {A} {B} y ≡ inl x') ≃ 𝟘
inr-≡-inl-equiv y x' = ≡-to-Eq-copr (inr y) (inl x') , ≡-to-Eq-copr-equiv (inr y) (inl x')

inr-≡-inr-equiv : {A B : Set} → (y y' : B) → (inr {A} {B} y ≡ inr y') ≃ (y ≡ y')
inr-≡-inr-equiv y y' = ≡-to-Eq-copr (inr y) (inr y') , ≡-to-Eq-copr-equiv (inr y) (inr y')

-- Definition 11.6.1 (dependent identity system)
is-dep-id-sys : (A : Set) → (B C : A → Set) → (a : A) → (b : B a) → (c : C a)
  → is-id-sys A C a c
  → (D : (x : A) → B x → C x → Set) → (d : D a b c) → Set₁
is-dep-id-sys A B C a b c _ D d = is-id-sys (B a) (λ y → D a y c) b d

-- Theorem 11.6.2 (Structure identity principle)

-- The key total-space equivalence: swap order of (B,C) Σ's
SIP-Σ-equiv : (A : Set) → (B C : A → Set)
  → (D : (x : A) → B x → C x → Set)
  → Σ (Σ A B) (λ z → Σ (C (proj₁ z)) (λ w → D (proj₁ z) (proj₂ z) w))
  ≃ Σ (Σ A C) (λ z → Σ (B (proj₁ z)) (λ y → D (proj₁ z) y (proj₂ z)))
SIP-Σ-equiv A B C D = (λ { ((a , b) , (c , d)) → (a , c) , (b , d)}) , (((λ {((a , c) ,  (b , d)) → (a , b) , (c , d)}) , λ { ((a , c) , (b , d)) → refl}) , (((λ {((a , c) ,  (b , d)) → (a , b) , (c , d)}) , λ { ((a , c) , (b , d)) → refl})))

-- (ii) ⇒ (v): contractibility of inner total space implies contractibility of outer
inner-contr-to-outer-contr : (A : Set) → (B C : A → Set) → (a : A) → (b : B a) → (c : C a)
  → is-id-sys A C a c
  → (D : (x : A) → B x → C x → Set)
  → is-contractible (Σ (B a) (λ y → D a y c))
  → is-contractible (Σ (Σ A B) (λ z → Σ (C (proj₁ z)) (λ w → D (proj₁ z) (proj₂ z) w)))
inner-contr-to-outer-contr A B C a b c C-id-sys D inner-contr = equiv-contr-to-contr (collapse ∘ swap) inner-contr (equiv-comp swap collapse swap-equiv collapse-equiv)
  where
  swap : Σ (Σ A B) (λ z → Σ (C (proj₁ z)) (λ w → D (proj₁ z) (proj₂ z) w)) → Σ (Σ A C) (λ z → Σ (B (proj₁ z)) (λ y → D (proj₁ z) y (proj₂ z)))
  swap ((a , b) , (c , d)) = (a , c) , (b , d)
  swap-inv : Σ (Σ A C) (λ z → Σ (B (proj₁ z)) (λ y → D (proj₁ z) y (proj₂ z)))
    → Σ (Σ A B) (λ z → Σ (C (proj₁ z)) (λ w → D (proj₁ z) (proj₂ z) w))
  swap-inv ((x , z) , (y , w)) = (x , y) , (z , w)
  swap-equiv : is-equiv swap
  swap-equiv = (swap-inv , λ {((a , c) , (b , d)) → refl}) , (swap-inv , λ {((a , b) , (c , d)) → refl})
  P : (x' : A) → C x' → Set
  P x' z' = Σ (B x') (λ y → D x' y z') → Σ (B a) (λ y → D a y c)
  ext : (x' : A) → (z' : C x') → P x' z'
  ext = proj₁ (C-id-sys P) id
  collapse : Σ (Σ A C) (λ z → Σ (B (proj₁ z)) (λ y → D (proj₁ z) y (proj₂ z))) → Σ (B a) (λ y → D a y c)
  collapse ((x , z) , bd) = ext x z bd
  collapse-equiv : is-equiv collapse
  collapse-equiv =
    (collapse-inv , sec-htpy) ,
    (collapse-inv , ret-htpy)
    where
      collapse-inv : Σ (B a) (λ y → D a y c)
                   → Σ (Σ A C) (λ z → Σ (B (proj₁ z)) (λ y → D (proj₁ z) y (proj₂ z)))
      collapse-inv yw = (a , c) , yw

      ext-eq : ext a c ≡ id
      ext-eq = proj₂ (C-id-sys P) id

      sec-htpy : (yw : Σ (B a) (λ y → D a y c)) → ext a c yw ≡ yw
      sec-htpy yw = ap (λ f → f yw) ext-eq

      Q : (x' : A) → C x' → Set
      Q x' z' = (yw : Σ (B x') (λ y → D x' y z'))
              → ((a , c) , ext x' z' yw) ≡ ((x' , z') , yw)

      Q-base : Q a c
      Q-base yw = ap (λ v → ((a , c) , v)) (sec-htpy yw)

      ret-htpy : (xzyw : Σ (Σ A C) (λ z → Σ (B (proj₁ z)) (λ y → D (proj₁ z) y (proj₂ z))))
               → collapse-inv (collapse xzyw) ≡ xzyw
      ret-htpy ((x , z) , yw) = proj₁ (C-id-sys Q) Q-base x z yw
-- (v) ⇒ (ii): converse
outer-contr-to-inner-contr : (A : Set) → (B C : A → Set) → (a : A) → (b : B a) → (c : C a)
  → is-id-sys A C a c
  → (D : (x : A) → B x → C x → Set)
  → is-contractible (Σ (Σ A B) (λ z → Σ (C (proj₁ z)) (λ w → D (proj₁ z) (proj₂ z) w)))
  → is-contractible (Σ (B a) (λ y → D a y c))
outer-contr-to-inner-contr A B C a b c C-id-sys D outer-contr =
  contr-equiv-to-contr (collapse ∘ swap) outer-contr (equiv-comp swap collapse swap-equiv collapse-equiv)
  where
  swap : Σ (Σ A B) (λ z → Σ (C (proj₁ z)) (λ w → D (proj₁ z) (proj₂ z) w)) → Σ (Σ A C) (λ z → Σ (B (proj₁ z)) (λ y → D (proj₁ z) y (proj₂ z)))
  swap ((a , b) , (c , d)) = (a , c) , (b , d)
  swap-inv : Σ (Σ A C) (λ z → Σ (B (proj₁ z)) (λ y → D (proj₁ z) y (proj₂ z)))
    → Σ (Σ A B) (λ z → Σ (C (proj₁ z)) (λ w → D (proj₁ z) (proj₂ z) w))
  swap-inv ((x , z) , (y , w)) = (x , y) , (z , w)
  swap-equiv : is-equiv swap
  swap-equiv = (swap-inv , λ {((a , c) , (b , d)) → refl}) , (swap-inv , λ {((a , b) , (c , d)) → refl})
  P : (x' : A) → C x' → Set
  P x' z' = Σ (B x') (λ y → D x' y z') → Σ (B a) (λ y → D a y c)
  ext : (x' : A) → (z' : C x') → P x' z'
  ext = proj₁ (C-id-sys P) id
  collapse : Σ (Σ A C) (λ z → Σ (B (proj₁ z)) (λ y → D (proj₁ z) y (proj₂ z))) → Σ (B a) (λ y → D a y c)
  collapse ((x , z) , bd) = ext x z bd
  collapse-equiv : is-equiv collapse
  collapse-equiv =
    (collapse-inv , sec-htpy) ,
    (collapse-inv , ret-htpy)
    where
      collapse-inv : Σ (B a) (λ y → D a y c)
                   → Σ (Σ A C) (λ z → Σ (B (proj₁ z)) (λ y → D (proj₁ z) y (proj₂ z)))
      collapse-inv yw = (a , c) , yw

      ext-eq : ext a c ≡ id
      ext-eq = proj₂ (C-id-sys P) id

      sec-htpy : (yw : Σ (B a) (λ y → D a y c)) → ext a c yw ≡ yw
      sec-htpy yw = ap (λ f → f yw) ext-eq

      Q : (x' : A) → C x' → Set
      Q x' z' = (yw : Σ (B x') (λ y → D x' y z'))
              → ((a , c) , ext x' z' yw) ≡ ((x' , z') , yw)

      Q-base : Q a c
      Q-base yw = ap (λ v → ((a , c) , v)) (sec-htpy yw)

      ret-htpy : (xzyw : Σ (Σ A C) (λ z → Σ (B (proj₁ z)) (λ y → D (proj₁ z) y (proj₂ z))))
               → collapse-inv (collapse xzyw) ≡ xzyw
      ret-htpy ((x , z) , yw) = proj₁ (C-id-sys Q) Q-base x z yw

-- (i) ⇔ (ii) ⇔ (iii):  apply total-contr-to-fam-equiv / fam-equiv-to-total-contr
-- to the inner family.  Concretely: given any (f, p) with f : (y : B a) → (b ≡ y) → D a y c
-- and p : f b refl ≡ d, f is a family of equivalences iff Σ (B a) (λ y → D a y c) is contractible.

-- (iv) ⇔ (v) ⇔ (vi): apply the same to the outer family on Σ A B at (a , b).

-- Main theorem direction: (iii) ⇒ (vi)
dep-id-sys-to-Σ-id-sys : (A : Set) → (B C : A → Set) → (a : A) → (b : B a) → (c : C a)
  → (C-id-sys : is-id-sys A C a c)
  → (D : (x : A) → B x → C x → Set) → (d : D a b c)
  → is-dep-id-sys A B C a b c C-id-sys D d
  → is-id-sys (Σ A B) (λ z → Σ (C (proj₁ z)) (λ w → D (proj₁ z) (proj₂ z) w)) (a , b) (c , d)
dep-id-sys-to-Σ-id-sys A B C a b c C-id-sys D d D-dep-id-sys =
  total-contr-to-id-sys (c , d) f-outer refl outer-contr
  where
    f-inner : (y : B a) → (b ≡ y) → D a y c
    f-inner .b refl = d

    inner-contr : is-contractible (Σ (B a) (λ y → D a y c))
    inner-contr = fam-equiv-to-total-contr d f-inner refl (id-sys-to-fam-equiv d f-inner refl D-dep-id-sys) 

    outer-contr : is-contractible (Σ (Σ A B) (λ z → Σ (C (proj₁ z)) (λ w → D (proj₁ z) (proj₂ z) w)))
    outer-contr = inner-contr-to-outer-contr A B C a b c C-id-sys D inner-contr

    f-outer : (z : Σ A B) → ((a , b) ≡ z) → Σ (C (proj₁ z)) (λ w → D (proj₁ z) (proj₂ z) w)
    f-outer .(a , b) refl = c , d

-- and the converse
Σ-id-sys-to-dep-id-sys : (A : Set) → (B C : A → Set) → (a : A) → (b : B a) → (c : C a)
  → (C-id-sys : is-id-sys A C a c)
  → (D : (x : A) → B x → C x → Set) → (d : D a b c)
  → is-id-sys (Σ A B) (λ z → Σ (C (proj₁ z)) (λ w → D (proj₁ z) (proj₂ z) w)) (a , b) (c , d)
  → is-dep-id-sys A B C a b c C-id-sys D d
Σ-id-sys-to-dep-id-sys A B C a b c C-id-sys D d Σ-id-sys =
  total-contr-to-id-sys d f-inner refl inner-contr
  where
    f-outer : (z : Σ A B) → ((a , b) ≡ z) → Σ (C (proj₁ z)) (λ w → D (proj₁ z) (proj₂ z) w)
    f-outer .(a , b) refl = c , d

    outer-contr : is-contractible (Σ (Σ A B) (λ z → Σ (C (proj₁ z)) (λ w → D (proj₁ z) (proj₂ z) w)))
    outer-contr = fam-equiv-to-total-contr (c , d) f-outer refl (id-sys-to-fam-equiv (c , d) f-outer refl Σ-id-sys)

    inner-contr : is-contractible (Σ (B a) (λ y → D a y c))
    inner-contr = outer-contr-to-inner-contr A B C a b c C-id-sys D outer-contr

    f-inner : (y : B a) → (b ≡ y) → D a y c
    f-inner .b refl = d

-- Example 11.6.3: characterization of the identity type of fib

-- The identity-system structure on path types
path-id-sys : {A : Set} → (x : A) → is-id-sys A (λ y → x ≡ y) x refl
path-id-sys x = λ P → (λ { z a refl → z}) , λ z → refl

-- The D family for Example 11.6.3
fib-D : {A B : Set} → (f : A → B) → (b : B) → (x : A) → (p : f x ≡ b)
  → (y : A) → (f y ≡ b) → (x ≡ y) → Set
fib-D f b x p y q α = ap f α ≡ concat p (inv q)

-- The basepoint d : fib-D f b x p x p refl
-- Goal: ap f refl ≡ concat p (inv p), i.e., refl ≡ concat p (inv p)
fib-d : {A B : Set} → (f : A → B) → (b : B) → (x : A) → (p : f x ≡ b)
  → fib-D f b x p x p refl
fib-d f b x refl = refl

-- Inner contractibility: Σ (q : f x ≡ b) (refl ≡ concat p (inv q)) is contractible
fib-inner-contr : {A B : Set} → (f : A → B) → (b : B) → (x : A) → (p : f x ≡ b)
  → is-contractible (Σ (f x ≡ b) (λ q → fib-D f b x p x q refl))
fib-inner-contr {A} {B} f b x p =
  equiv-contr-to-contr (tot algebra) (Σ-≡-contractible p)
    (fam-equiv-to-tot-equiv algebra algebra-equiv)
  where
  algebra : (q : f x ≡ b) → (refl ≡ concat p (inv q)) → (p ≡ q)
  algebra refl e = concat (inv (right-unit p)) (inv e)
  algebra-equiv : (q : f x ≡ b) → is-equiv (algebra q)
  algebra-equiv refl =
    equiv-comp inv (concat (inv (right-unit p)))
      (is-equiv-inv refl (concat p refl))
      (is-equiv-concat (inv (right-unit p)))

-- The dependent identity system property for D
fib-D-dep-id-sys : {A B : Set} → (f : A → B) → (b : B) → (x : A) → (p : f x ≡ b)
  → is-dep-id-sys A (λ y → f y ≡ b) (λ y → x ≡ y) x p refl
      (path-id-sys x) (fib-D f b x p) (fib-d f b x p)
fib-D-dep-id-sys f b x refl = total-contr-to-id-sys refl (λ { refl p → refl}) refl (fib-inner-contr f b x refl)

-- Main equivalence (Example 11.6.3)
fib-≡-equiv : {A B : Set} → (f : A → B) → (b : B)
  → (x y : A) → (p : f x ≡ b) → (q : f y ≡ b)
  → ((x , p) ≡ (y , q)) ≃ Σ (x ≡ y) (λ α → ap f α ≡ concat p (inv q))
fib-≡-equiv {A} {B} f b x y p q =
  canonical-map (y , q) ,
  id-sys-to-fam-equiv (refl , fib-d f b x p) canonical-map refl Σ-id-sys (y , q)
  where
  canonical-map : (z : Σ A (λ y' → f y' ≡ b))
                → ((x , p) ≡ z)
                → Σ (x ≡ proj₁ z) (λ α → ap f α ≡ concat p (inv (proj₂ z)))
  canonical-map .(x , p) refl = refl , fib-d f b x p

  Σ-id-sys : is-id-sys (Σ A (λ y' → f y' ≡ b))
               (λ z → Σ (x ≡ proj₁ z) (λ α → ap f α ≡ concat p (inv (proj₂ z))))
               (x , p) (refl , fib-d f b x p)
  Σ-id-sys = dep-id-sys-to-Σ-id-sys A (λ y' → f y' ≡ b) (λ y' → x ≡ y')
               x p refl (path-id-sys x)
               (fib-D f b x p) (fib-d f b x p)
               (fib-D-dep-id-sys f b x p)


-- Exercises
-- Ex 11.1
-- a
empty-embeds : (A : Set) → (f : 𝟘 → A) → is-emb f
empty-embeds A f () ()

-- b
inl-emb : (A B : Set) → is-emb (inl {A} {B}) 
inl-emb A B x y = ((λ { refl → refl}) , λ {refl → refl}) , ((λ { refl → refl}) , λ {refl → refl})

inr-emb : (A B : Set) → is-emb (inr {A} {B})
inr-emb A B x y = ((λ { refl → refl}) , λ {refl → refl}) , ((λ { refl → refl}) , λ {refl → refl})

--c
inl-equiv-to-B-empty : (A B : Set) → is-equiv (inl {A} {B}) → is-empty B
inl-equiv-to-B-empty A B ((f , inf) , (g , gin)) x = ≡-to-Eq-copr (inl (f (inr x))) (inr x) (inf (inr x)) 

B-empty-to-inl-equiv : (A B : Set) → is-empty B → is-equiv (inl {A} {B})
B-empty-to-inl-equiv A B Bempty = (⊎-elim-left Bempty , λ { (inl x) → refl ; (inr x) → ex-falso (Bempty x)}) , ((⊎-elim-left Bempty , λ { x → refl }))

inr-equiv-to-A-empty : (A B : Set) → is-equiv (inr {A} {B}) → is-empty A
inr-equiv-to-A-empty A B ((f , inf) , (g , gin)) x = ≡-to-Eq-copr (inr (f (inl x))) (inl x) (inf (inl x)) 

A-empty-to-inr-equiv : (A B : Set) → is-empty A → is-equiv (inr {A} {B})
A-empty-to-inr-equiv A B Aempty = (⊎-elim-right Aempty , λ { (inr x) → refl ; (inl x) → ex-falso (Aempty x)}) , ((⊎-elim-right Aempty , λ { x → refl }))

-- Ex 11.2
--a
adj-equiv : {A B : Set} → (e : A ≃ B) → (x : A) → (y : B) → ((proj₁ e) x ≡ y) ≃ (x ≡ proj₁ (proj₁ (proj₂ e)) y)
adj-equiv {A} {B} (e' , ((f , ef) , (g , ge))) x y = forward , forward-equiv
  where
    inv-of-e : is-equiv e'
    inv-of-e = (f , ef) , (g , ge)

    has-inv-e' : has-inverse e'
    has-inv-e' = equiv-to-inverse e' inv-of-e

    fe : (a : A) → f (e' a) ≡ a
    fe = proj₂ (proj₂ has-inv-e')

    f-equiv : is-equiv f
    f-equiv = inv-equiv-is-equiv e' inv-of-e has-inv-e'

    forward : (e' x ≡ y) → (x ≡ f y)
    forward p = concat (inv (fe x)) (ap f p)

    forward-equiv : is-equiv forward
    forward-equiv =
      equiv-comp (ap f) (concat (inv (fe x)))
        (equiv-to-emb f f-equiv (e' x) y)
        (is-equiv-concat (inv (fe x)))
