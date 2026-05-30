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

is-id-sys : {A : Set} → (B : A → Set) → (a : A) → (b : B a) → Set₁
is-id-sys {A} B a b = (P : (x : A) → B x → Set) → sec (λ (h : (x : A) → (y : B x) → P x y) → h a b)

-- FUNDAMENTAL THEOREM OF IDENTITY TYPES
-- i → ii
fam-equiv-to-total-contr : {A : Set} → {a : A} → {B : A → Set} → (b : B a) → (f : (x : A) → (a ≡ x) → B x) → (p : f a refl ≡ b) → is-equiv-fam f → is-contractible (Σ A B)
fam-equiv-to-total-contr {A} {a} {B} b f p f-equiv =
  contr-equiv-to-contr (tot f) (Σ-≡-contractible a) (fam-equiv-to-tot-equiv f f-equiv)

-- ii → iii
total-contr-to-id-sys : {A : Set} → {a : A} → {B : A → Set} → (b : B a) → (f : (x : A) → (a ≡ x) → B x) → (p : f a refl ≡ b) → is-contractible (Σ A B) → is-id-sys B a b
total-contr-to-id-sys {A} {a} {B} b f p Σ-contr P =
  (λ pab x y → s (x , y) pab) , sh
  where
    P' : Σ A B → Set
    P' z = P (proj₁ z) (proj₂ z)
    si : sec (λ (g : (z : Σ A B) → P' z) → g (a , b))
    si = contr-to-sing-ind (a , b) Σ-contr P'
    s : (z : Σ A B) → P' (a , b) → P' z
    s z pab = proj₁ si pab z
    sh : (λ (h : (x : A) → (y : B x) → P x y) → h a b) ∘
         (λ pab x y → s (x , y) pab) ∼ id
    sh = proj₂ si

-- iii → i
id-sys-to-fam-equiv : {A : Set} → {a : A} → {B : A → Set} → (b : B a) → (f : (x : A) → (a ≡ x) → B x) → (p : f a refl ≡ b) → is-id-sys B a b → (x : A) → is-equiv (f x)
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
is-dep-id-sys : {A : Set} → (B C : A → Set) → (a : A) → (b : B a) → (c : C a)
  → is-id-sys C a c
  → (D : (x : A) → B x → C x → Set) → (d : D a b c) → Set₁
is-dep-id-sys B C a b c _ D d = is-id-sys (λ y → D a y c) b d

-- Theorem 11.6.2 (Structure identity principle)

-- The key total-space equivalence: swap order of (B,C) Σ's
SIP-Σ-equiv : {A : Set} → (B C : A → Set)
  → (D : (x : A) → B x → C x → Set)
  → Σ (Σ A B) (λ z → Σ (C (proj₁ z)) (λ w → D (proj₁ z) (proj₂ z) w))
  ≃ Σ (Σ A C) (λ z → Σ (B (proj₁ z)) (λ y → D (proj₁ z) y (proj₂ z)))
SIP-Σ-equiv B C D = (λ { ((a , b) , (c , d)) → (a , c) , (b , d)}) , (((λ {((a , c) ,  (b , d)) → (a , b) , (c , d)}) , λ { ((a , c) , (b , d)) → refl}) , (((λ {((a , c) ,  (b , d)) → (a , b) , (c , d)}) , λ { ((a , c) , (b , d)) → refl})))

-- (ii) ⇒ (v): contractibility of inner total space implies contractibility of outer
inner-contr-to-outer-contr : {A : Set} → (B C : A → Set) → (a : A) → (b : B a) → (c : C a)
  → is-id-sys C a c
  → (D : (x : A) → B x → C x → Set)
  → is-contractible (Σ (B a) (λ y → D a y c))
  → is-contractible (Σ (Σ A B) (λ z → Σ (C (proj₁ z)) (λ w → D (proj₁ z) (proj₂ z) w)))
inner-contr-to-outer-contr {A} B C a b c C-id-sys D inner-contr = equiv-contr-to-contr (collapse ∘ swap) inner-contr (equiv-comp swap collapse swap-equiv collapse-equiv)
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
outer-contr-to-inner-contr : {A : Set} → (B C : A → Set) → (a : A) → (b : B a) → (c : C a)
  → is-id-sys C a c
  → (D : (x : A) → B x → C x → Set)
  → is-contractible (Σ (Σ A B) (λ z → Σ (C (proj₁ z)) (λ w → D (proj₁ z) (proj₂ z) w)))
  → is-contractible (Σ (B a) (λ y → D a y c))
outer-contr-to-inner-contr {A} B C a b c C-id-sys D outer-contr =
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
dep-id-sys-to-Σ-id-sys : {A : Set} → (B C : A → Set) → (a : A) → (b : B a) → (c : C a)
  → (C-id-sys : is-id-sys C a c)
  → (D : (x : A) → B x → C x → Set) → (d : D a b c)
  → is-dep-id-sys B C a b c C-id-sys D d
  → is-id-sys (λ z → Σ (C (proj₁ z)) (λ w → D (proj₁ z) (proj₂ z) w)) (a , b) (c , d)
dep-id-sys-to-Σ-id-sys {A} B C a b c C-id-sys D d D-dep-id-sys =
  total-contr-to-id-sys (c , d) f-outer refl outer-contr
  where
    f-inner : (y : B a) → (b ≡ y) → D a y c
    f-inner .b refl = d

    inner-contr : is-contractible (Σ (B a) (λ y → D a y c))
    inner-contr = fam-equiv-to-total-contr d f-inner refl (id-sys-to-fam-equiv d f-inner refl D-dep-id-sys)

    outer-contr : is-contractible (Σ (Σ A B) (λ z → Σ (C (proj₁ z)) (λ w → D (proj₁ z) (proj₂ z) w)))
    outer-contr = inner-contr-to-outer-contr B C a b c C-id-sys D inner-contr

    f-outer : (z : Σ A B) → ((a , b) ≡ z) → Σ (C (proj₁ z)) (λ w → D (proj₁ z) (proj₂ z) w)
    f-outer .(a , b) refl = c , d

-- and the converse
Σ-id-sys-to-dep-id-sys : {A : Set} → (B C : A → Set) → (a : A) → (b : B a) → (c : C a)
  → (C-id-sys : is-id-sys C a c)
  → (D : (x : A) → B x → C x → Set) → (d : D a b c)
  → is-id-sys (λ z → Σ (C (proj₁ z)) (λ w → D (proj₁ z) (proj₂ z) w)) (a , b) (c , d)
  → is-dep-id-sys B C a b c C-id-sys D d
Σ-id-sys-to-dep-id-sys {A} B C a b c C-id-sys D d Σ-id-sys =
  total-contr-to-id-sys d f-inner refl inner-contr
  where
    f-outer : (z : Σ A B) → ((a , b) ≡ z) → Σ (C (proj₁ z)) (λ w → D (proj₁ z) (proj₂ z) w)
    f-outer .(a , b) refl = c , d

    outer-contr : is-contractible (Σ (Σ A B) (λ z → Σ (C (proj₁ z)) (λ w → D (proj₁ z) (proj₂ z) w)))
    outer-contr = fam-equiv-to-total-contr (c , d) f-outer refl (id-sys-to-fam-equiv (c , d) f-outer refl Σ-id-sys)

    inner-contr : is-contractible (Σ (B a) (λ y → D a y c))
    inner-contr = outer-contr-to-inner-contr B C a b c C-id-sys D outer-contr

    f-inner : (y : B a) → (b ≡ y) → D a y c
    f-inner .b refl = d

-- Example 11.6.3: characterization of the identity type of fib

-- The identity-system structure on path types
path-id-sys : {A : Set} → (x : A) → is-id-sys (λ y → x ≡ y) x refl
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
  → is-dep-id-sys (λ y → f y ≡ b) (λ y → x ≡ y) x p refl
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

  Σ-id-sys : is-id-sys (λ z → Σ (x ≡ proj₁ z) (λ α → ap f α ≡ concat p (inv (proj₂ z))))
               (x , p) (refl , fib-d f b x p)
  Σ-id-sys = dep-id-sys-to-Σ-id-sys (λ y' → f y' ≡ b) (λ y' → x ≡ y')
               x p refl (path-id-sys x)
               (fib-D f b x p) (fib-d f b x p)
               (fib-D-dep-id-sys f b x p)


-- Exercises
-- Ex 11.1
-- a
empty-embeds : {A : Set} → (f : 𝟘 → A) → is-emb f
empty-embeds f () ()

-- b
inl-emb : (A B : Set) → is-emb (inl {A} {B}) 
inl-emb A B x y = ((λ { refl → refl}) , λ {refl → refl}) , ((λ { refl → refl}) , λ {refl → refl})

inr-emb : (A B : Set) → is-emb (inr {A} {B})
inr-emb A B x y = ((λ { refl → refl}) , λ {refl → refl}) , ((λ { refl → refl}) , λ {refl → refl})

-- c
inl-equiv-to-B-empty : (A B : Set) → is-equiv (inl {A} {B}) → is-empty B
inl-equiv-to-B-empty A B ((f , inf) , (g , gin)) x = ≡-to-Eq-copr (inl (f (inr x))) (inr x) (inf (inr x)) 

B-empty-to-inl-equiv : (A B : Set) → is-empty B → is-equiv (inl {A} {B})
B-empty-to-inl-equiv A B Bempty = (⊎-elim-left Bempty , λ { (inl x) → refl ; (inr x) → ex-falso (Bempty x)}) , ((⊎-elim-left Bempty , λ { x → refl }))

inr-equiv-to-A-empty : (A B : Set) → is-equiv (inr {A} {B}) → is-empty A
inr-equiv-to-A-empty A B ((f , inf) , (g , gin)) x = ≡-to-Eq-copr (inr (f (inl x))) (inl x) (inf (inl x)) 

A-empty-to-inr-equiv : (A B : Set) → is-empty A → is-equiv (inr {A} {B})
A-empty-to-inr-equiv A B Aempty = (⊎-elim-right Aempty , λ { (inr x) → refl ; (inl x) → ex-falso (Aempty x)}) , ((⊎-elim-right Aempty , λ { x → refl }))

-- Ex 11.2
-- a
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

-- b
adj-G : {A B : Set} → (e : A ≃ B) → (y : B) → (proj₁ e) (proj₁ (proj₁ (proj₂ e)) y) ≡ y
adj-G (e' , ((f , ef) , (g , ge))) =
  proj₁ (proj₂ (inv-to-coh-inv e' (equiv-to-inverse e' ((f , ef) , (g , ge)))))

adj-equiv-triangle : {A B : Set} → (e : A ≃ B) → (x : A) → (y : B) → (p : (proj₁ e) x ≡ y) →
                     concat (ap (proj₁ e) (proj₁ (adj-equiv e x y) p)) (adj-G e y) ≡ p
adj-equiv-triangle {A} {B} (e' , ((f , ef) , (g , ge))) x .(e' x) refl =
  concat
    (ap (λ q → concat q (G (e' x)))
        (concat (ap (ap e') (right-unit (inv (fe x)))) (ap-inv e' (fe x))))
    (concat
      (ap (concat (inv (ap e' (fe x)))) (K x))
      (left-inv (ap e' (fe x))))
  where
    coh : is-coh-inv e'
    coh = inv-to-coh-inv e' (equiv-to-inverse e' ((f , ef) , (g , ge)))
    fe : (a : A) → f (e' a) ≡ a
    fe = proj₁ (proj₂ (proj₂ coh))
    G : (b : B) → e' (f b) ≡ b
    G = proj₁ (proj₂ coh)
    K : (a : A) → G (e' a) ≡ ap e' (fe a)
    K = proj₂ (proj₂ (proj₂ coh))

-- 11.3
-- a
htpy-of-emb-is-emb : {A B : Set} → (f g : A → B) → (f ∼ g) → is-emb f → is-emb g
htpy-of-emb-is-emb {A} {B} f g H femb x y = htpy-of-equiv-is-equiv (composite) (ap g) (λ { refl → concat (ap (concat (inv (H x))) (left-unit (H x))) (left-inv (H x))}) (equiv-comp (ap f) (λ {p → concat (inv (H x)) (concat p (H y))}) (femb x y) (equiv-comp (λ q → concat q (H y)) (concat (inv (H x))) (is-equiv-concat' (H y)) (is-equiv-concat (inv (H x)))))
  where
  composite : (x ≡ y) → (g x ≡ g y)
  composite p = concat (inv (H x)) (concat (ap f p) (H y))

emb-comp : {A B C : Set} → (f : A → B) → (g : B → C) → is-emb f → is-emb g → is-emb (g ∘ f)
emb-comp f g femb gemb x y = htpy-of-equiv-is-equiv (ap g ∘ ap f) (ap (g ∘ f)) (λ p → ap-comp f g p) (equiv-comp (ap f) (ap g) (femb x y) (gemb (f x) (f y)))

emb-cancel : {A B C : Set} → (f : A → B) → (g : B → C) → is-emb g → is-emb (g ∘ f) → is-emb f
emb-cancel f g gemb gfemb x y = 3-for-2-f-g-to-h (ap (g ∘ f)) (ap g) (ap f) (λ p → inv (ap-comp f g p)) (gfemb x y) (gemb (f x) (f y))

-- 11.4
-- a
comm-tri-emb-g-to-emb-f-iff-emb-h : {A B X : Set} → (f : A → X) → (g : B → X) → (h : A → B)
  → triangle-commutes f h g → is-emb g → (is-emb f ↔ is-emb h)
comm-tri-emb-g-to-emb-f-iff-emb-h f g h H gemb = (to , from)
  where
  to : is-emb f → is-emb h
  to femb = emb-cancel h g gemb (htpy-of-emb-is-emb f (g ∘ h) H femb)
  from : is-emb h → is-emb f
  from hemb = htpy-of-emb-is-emb (g ∘ h) f (inv-htpy H) (emb-comp h g hemb gemb)
-- b
comm-tri-equiv-h-to-emb-f-iff-emb-g : {A B X : Set} → (f : A → X) → (g : B → X) → (h : A → B)
  → triangle-commutes f h g → is-equiv h → (is-emb f ↔ is-emb g)
comm-tri-equiv-h-to-emb-f-iff-emb-g f g h H hequiv = (to , from)
  where
  to : is-emb f → is-emb g
  to femb = htpy-of-emb-is-emb (f ∘ k) g (λ x → concat (H (k x)) (ap g (kh x)))
      (emb-comp k f (equiv-to-emb k (3-for-2-f-g-to-h id h k (inv-htpy kh) (is-equiv-id _) hequiv)) femb)
    where
    k = proj₁ (proj₁ hequiv)
    kh = proj₂ (proj₁ hequiv)
  from : is-emb g → is-emb f
  from gemb = htpy-of-emb-is-emb (g ∘ h) f (inv-htpy H) (emb-comp h g (equiv-to-emb h hequiv) gemb)

-- 11.5
-- composition of equivalences is an equivalence by equiv-comp, so we only prove the reverse direction

emb-comp-equiv-to-f-equiv : {A B C : Set} → (f : A → B) → (g : B → C) → is-emb f → is-emb g → is-equiv (g ∘ f) → is-equiv f × is-equiv g
emb-comp-equiv-to-f-equiv {A} {B} {C} f g femb gemb gfequiv = fequiv , gequiv
  where
  fequiv : is-equiv f
  fequiv = contr-map-to-equiv f (λ b →
    equiv-contr-to-contr
      (tot (λ a (p : f a ≡ b) → ap g p))
      (equiv-to-contr-map (g ∘ f) gfequiv (g b))
      (fam-equiv-to-tot-equiv (λ a (p : f a ≡ b) → ap g p) (λ a → gemb (f a) b)))
  gequiv : is-equiv g
  gequiv = contr-map-to-equiv g (λ c →
    contr-equiv-to-contr
      (base-change f (λ b → g b ≡ c))
      (equiv-to-contr-map (g ∘ f) gfequiv c)
      (f-equiv-to-base-change-equiv f (λ b → g b ≡ c) fequiv))

-- 11.6
-- a
⊎-elim-emb-to-emb-f-and-emb-g-and-ne : {A B C : Set} → (f : A → C) → (g : B → C) → is-emb (ind⊎ f g) → is-emb f × is-emb g × ((a : A) → (b : B) → ¬ (f a ≡ g b))
⊎-elim-emb-to-emb-f-and-emb-g-and-ne {A} {B} {C} f g fgemb = fequiv , (gequiv , ne)
  where
  fequiv = proj₂ (comm-tri-emb-g-to-emb-f-iff-emb-h f (ind⊎ {P = λ _ → C} f g) (inl {A} {B}) (λ x → refl) fgemb) (inl-emb A B)
  gequiv = proj₂ (comm-tri-emb-g-to-emb-f-iff-emb-h g (ind⊎ {P = λ _ → C} f g) (inr {A} {B}) (λ x → refl) fgemb) (inr-emb A B)
  ne : (a : A) → (b : B) → ¬ (f a ≡ g b)
  ne a b fagb = proj₁ (inl-≡-inr-equiv a b) (proj₁ (proj₁ (fgemb (inl a) (inr b))) fagb)

empty-equiv : (f : 𝟘 → 𝟘) → is-equiv f
empty-equiv f = ((λ ()) , (λ ())) , ((λ ()) , λ ())

-- b
emb-f-and-emb-g-and-ne-to-⊎-elim-emb : {A B C : Set} → (f : A → C) → (g : B → C)  → is-emb f → is-emb g → ((a : A) → (b : B) → ¬ (f a ≡ g b)) → is-emb (ind⊎ f g)
emb-f-and-emb-g-and-ne-to-⊎-elim-emb {A} {B} {C} f g femb gemb p (inl x) (inl y) = 
  3-for-2-f-h-to-g (ap f) (ap (ind⊎ f g)) (ap inl) (λ q → inv (ap-comp inl (ind⊎ f g) q)) (femb x y) (inl-emb A B x y)
emb-f-and-emb-g-and-ne-to-⊎-elim-emb {A} {B} {C} f g femb gemb p (inl x) (inr y) = 
  ((λ q → ex-falso (p x y q)) , λ {q → ex-falso (p x y q)}) , ((λ q → ex-falso ((p x y q))) , λ ())
emb-f-and-emb-g-and-ne-to-⊎-elim-emb {A} {B} {C} f g femb gemb p (inr x) (inl y) = 
  ((λ q → ex-falso (p y x (inv q))) , (λ q → ex-falso (p y x (inv q)))) , (((λ q → ex-falso (p y x (inv q)))) , (λ ()))
emb-f-and-emb-g-and-ne-to-⊎-elim-emb {A} {B} {C} f g femb gemb p (inr x) (inr y) = 
  3-for-2-f-h-to-g (ap g) (ap (ind⊎ f g)) (ap inr) (λ q → inv (ap-comp inr (ind⊎ f g) q)) (gemb x y) (inr-emb A B x y)

-- 11.7
-- a
coprod-map-equiv-to-maps-equiv : {A B A' B' : Set} → (f : A → A') → (g : B → B') → is-equiv (f ⊎' g) → (is-equiv f × is-equiv g)
coprod-map-equiv-to-maps-equiv {A} {B} {A'} {B'} f g fgequiv = fequiv , gequiv 
  where
  fequiv : is-equiv f
  fequiv = contr-map-to-equiv f λ a' → equiv-contr-to-contr (λ {(a , p) → (inl a , ap inl p)}) (equiv-to-contr-map (f ⊎' g) fgequiv (inl a')) 
    (((λ {(inl x , p) → x , ≡-to-Eq-copr (inl (f x)) (inl a') p }) , λ {(inl x , refl) → refl}) , ((λ {(inl x , p) → (x , ≡-to-Eq-copr (inl (f x)) (inl a') p)}) , λ {(a , refl) → refl}))

  gequiv : is-equiv g
  gequiv = contr-map-to-equiv g λ a' → equiv-contr-to-contr (λ {(a , p) → (inr a , ap inr p)}) (equiv-to-contr-map (f ⊎' g) fgequiv (inr a'))
    ((((λ {(inr x , p) → x , ≡-to-Eq-copr (inr (g x)) (inr a') p }) , λ {(inr x , refl) → refl}) , ((λ {(inr x , p) → (x , ≡-to-Eq-copr (inr (g x)) (inr a') p)}) , λ {(a , refl) → refl})))

-- 11.7b
⊎'-emb-iff-emb-f-and-emb-g : {A B A' B' : Set} → (f : A → A') → (g : B → B')
  → is-emb (f ⊎' g) ↔ (is-emb f × is-emb g)
⊎'-emb-iff-emb-f-and-emb-g {A} {B} {A'} {B'} f g = (to , from)
  where
  to : is-emb (f ⊎' g) → is-emb f × is-emb g
  to fgemb =
    emb-cancel f (inl {A'} {B'}) (inl-emb A' B')
      (htpy-of-emb-is-emb (inl {A'} {B'} ∘ f) ((f ⊎' g) ∘ inl {A} {B}) (λ _ → refl)
        (emb-comp (inl {A} {B}) (f ⊎' g) (inl-emb A B) fgemb)) ,
    emb-cancel g (inr {A'} {B'}) (inr-emb A' B')
      (htpy-of-emb-is-emb (inr {A'} {B'} ∘ g) ((f ⊎' g) ∘ inr {A} {B}) (λ _ → refl)
        (emb-comp (inr {A} {B}) (f ⊎' g) (inr-emb A B) fgemb))
  from : is-emb f × is-emb g → is-emb (f ⊎' g)
  from (femb , gemb) (inl x) (inl y) =
    3-for-2-f-h-to-g (ap (inl {A'} {B'}) ∘ ap f) (ap (f ⊎' g)) (ap (inl {A} {B}))
      (λ p → concat (ap-comp f (inl {A'} {B'}) p) (inv (ap-comp (inl {A} {B}) (f ⊎' g) p)))
      (equiv-comp (ap f) (ap (inl {A'} {B'})) (femb x y) (inl-emb A' B' (f x) (f y)))
      (inl-emb A B x y)
  from (femb , gemb) (inl x) (inr y) =
    ((λ q → ex-falso (≡-to-Eq-copr (inl (f x)) (inr (g y)) q)) ,
     λ q → ex-falso (≡-to-Eq-copr (inl (f x)) (inr (g y)) q)) ,
    ((λ q → ex-falso (≡-to-Eq-copr (inl (f x)) (inr (g y)) q)) , λ ())
  from (femb , gemb) (inr x) (inl y) =
    ((λ q → ex-falso (≡-to-Eq-copr (inr (g x)) (inl (f y)) q)) ,
     λ q → ex-falso (≡-to-Eq-copr (inr (g x)) (inl (f y)) q)) ,
    ((λ q → ex-falso (≡-to-Eq-copr (inr (g x)) (inl (f y)) q)) , λ ())
  from (femb , gemb) (inr x) (inr y) =
    3-for-2-f-h-to-g (ap (inr {A'} {B'}) ∘ ap g) (ap (f ⊎' g)) (ap (inr {A} {B}))
      (λ p → concat (ap-comp g (inr {A'} {B'}) p) (inv (ap-comp (inr {A} {B}) (f ⊎' g) p)))
      (equiv-comp (ap g) (ap (inr {A'} {B'})) (gemb x y) (inr-emb A' B' (g x) (g y)))
      (inr-emb A B x y)

-- 11.8
-- a
htpy-to-tot-htpy : {A : Set} → {B C : A → Set} → (f g : (x : A) → B x → C x) → ((x : A) → f x ∼ g x) → tot f ∼ tot g
htpy-to-tot-htpy f g H (a , b) = eq-pair (tot f (a , b)) (tot g (a , b)) (refl , H a b)

-- b
tot-comp-htpy : {A : Set} → {B C D : A → Set} → (f : (x : A) → B x → C x) → (g : (x : A) → C x → D x) → tot (λ x → (g x) ∘ (f x)) ∼ tot g ∘ tot f
tot-comp-htpy f g (a , b) = eq-pair (tot (λ x → g x ∘ f x) (a , b)) ((tot g ∘ tot f) (a , b)) (refl , refl)

-- c
tot-id : {A : Set} → {B : A → Set} → tot (λ x → id {B x}) ∼ id 
tot-id (a , b) = eq-pair (tot (λ x → id) (a , b)) (a , b) (refl , refl)

-- d
fam-retr-≡-to-fam-equiv-≡ : {A : Set} → {a : A} → {B : A → Set} → (f : (x : A) → B x → (a ≡ x)) → ((x : A) → retr (f x)) → (x : A) → B x ≃ (a ≡ x)
fam-retr-≡-to-fam-equiv-≡ {A} {a} {B} f r x = f x , 3-for-2-f-g-to-h id (proj₁ (r x)) (f x) (λ a → inv (proj₂ (r x) a)) (is-equiv-id (B x)) 
  (total-contr-to-fam-equiv (proj₁ (r a) refl) (λ a p → proj₁ (r a) p) refl 
    (retr-to-contr-to-contr (tot f) (tot (λ y → proj₁ (r y)) , λ {(a' , b') → eq-pair _ _ (refl , proj₂ (r a') b')}) (Σ-≡-contractible a)) 
  x)

-- 11.8e
fam-sec-≡-to-fam-equiv-≡ : {A : Set} → {a : A} → (B : A → Set)
  → (f : (x : A) → (a ≡ x) → B x)
  → ((x : A) → sec (f x))
  → is-equiv-fam f
fam-sec-≡-to-fam-equiv-≡ {A} {a} B f s = 
  total-contr-to-fam-equiv (f a refl) f refl 
    (retr-to-contr-to-contr (tot (λ x → proj₁ (s x))) 
      ((tot f) , λ {(x , b) → eq-pair ((tot f ∘ tot (λ x₁ → proj₁ (s x₁))) (x , b)) ((x , b)) ((refl , (proj₂ (s x) b)))}) 
      (Σ-≡-contractible a))

-- 11.9
ap-sec-to-emb : {A B : Set} → (f : A → B) → ((x y : A) → sec (ap f {x} {y}))  → is-emb f
ap-sec-to-emb {A} {B} f s x y = fam-sec-≡-to-fam-equiv-≡ (λ y → f x ≡ f y) (λ y p → ap f p) (s x) y

-- 11.10
is-path-split : {A B : Set} → (f : A → B) → Set
is-path-split {A} {B} f = sec f × ((x y : A) → sec (ap f {x} {y}))

path-split-to-equiv : {A B : Set} → (f : A → B) → is-path-split f → is-equiv f
path-split-to-equiv f ((s , fs) , aps) = (s , fs) , (s , λ x → proj₁ (aps (s (f x)) x) (fs (f x)))

equiv-to-path-split : {A B : Set} → (f : A → B) → is-equiv f → is-path-split f
equiv-to-path-split f ((s , fs) , (r , rf)) = (s , fs) , λ x y → proj₁ (equiv-to-emb f ((s , fs) , (r , rf)) x y)

-- 11.11a
fib-triangle : {A B X : Set} → (f : A → X) → (g : B → X) → (h : A → B)
  → triangle-commutes f h g → (x : X) → fib f x → fib g x
fib-triangle f g h H x (a , p) = h a , concat (inv (H a)) p

fib-triangle-htpy : {B X : Set} → (g : B → X) → (b : B) → (x : X) → (p : x ≡ g b)
  → _≡_ {A = Σ X (fib g)} (g b , (b , refl)) (x , (b , concat (inv p) refl))
fib-triangle-htpy g b _ refl = refl

-- 11.11b
comm-tri-equiv-h-iff-fam-equiv-fib-tri : {A B X : Set} → (f : A → X) → (g : B → X) → (h : A → B)
  → (H : triangle-commutes f h g)
  → is-equiv h ↔ is-equiv-fam (fib-triangle f g h H)
comm-tri-equiv-h-iff-fam-equiv-fib-tri {A} {B} {X} f g h H = (λ hequiv x → 
  htpy-of-equiv-is-equiv (tot-fam h λ a → concat (inv (H a))) (fib-triangle f g h H x) (λ {(a , refl) → refl}) 
  (g-equiv-to-tot-fam-equiv h (λ a p → concat (inv (H a)) p) hequiv λ a' → is-equiv-concat (inv (H a')))) , 
  
  λ eqfam →
    htpy-of-equiv-is-equiv
      (sec-g ∘ tot (fib-triangle f g h H) ∘ fwd-f)
      h
      (λ a → ap sec-g (inv (htpy a)))
      (equiv-comp fwd-f (sec-g ∘ tot (fib-triangle f g h H)) fwd-f-equiv
        (equiv-comp (tot (fib-triangle f g h H)) sec-g
          (fam-equiv-to-tot-equiv (fib-triangle f g h H) eqfam)
          sec-g-equiv))
    where
      fwd-f       = proj₁ (proj₁ (fib-repl f))
      fwd-f-equiv = proj₂ (proj₁ (fib-repl f))
      sec-g       = proj₁ (inv-≃ (proj₁ (fib-repl g)))
      sec-g-equiv = proj₂ (inv-≃ (proj₁ (fib-repl g)))
      htpy : (a : A) → (g (h a) , (h a , refl)) ≡ (f a , (h a , concat (inv (H a)) refl))
      htpy a = fib-triangle-htpy g (h a) (f a) ((H a))

