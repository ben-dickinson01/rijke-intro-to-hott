module ch11 where

open import ch10 public

tot : {A : Set} → {B C : A → Set} → (f : (x : A) → (B x → C x)) → Σ A B → Σ A C

tot f (a , b) = a , f a b

fib-tot-equiv-fib : {A : Set} → {B C : A → Set} → (f : (x : A) → B x → C x) → (t : Σ A C) → fib (tot f) t ≃ fib (f (proj₁ t)) (proj₂ t)
fib-tot-equiv-fib {A} {B} {C} f (a , c) = (λ { ((a , b) , refl) → b , refl}) , (((λ { (bta , p) → (a , bta) , eq-pair (a , f a bta) (a , c) (refl , p)}) , λ { (bta , refl) → refl}) , ((λ { (ba , refl) → (a , ba) , refl}) , λ { ((a , b) , refl) → refl}))

fam-equiv-to-tot-equiv : {A : Set} → {B C : A → Set} → (f : (x : A) → B x → C x) → ((x : A) → is-equiv (f x)) → is-equiv (tot f)
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

tot-equiv-to-fam-equiv : {A : Set} → {B C : A → Set} → (f : (x : A) → B x → C x) → is-equiv (tot f) → (x : A) → is-equiv (f x)
tot-equiv-to-fam-equiv {A} {B} {C} f e a = contr-map-to-equiv (f a) (λ c →
    ex-10-3ii (proj₁ (fib-tot-equiv-fib f (a , c)))
              (equiv-to-contr-map (tot f) e (a , c))
              (proj₂ (fib-tot-equiv-fib f (a , c))))

base-change : {A B : Set} → (f : A → B) → (C : B → Set) → Σ A (λ x → C (f x)) → Σ B C
base-change f C (x , z) = f x , z

fib-base-change-equiv-fib : {A B : Set} → (f : A → B) → (C : B → Set) → (t : Σ B C) → fib (base-change f C) t ≃ fib f (proj₁ t)
fib-base-change-equiv-fib f C (b , c) =
  (λ { ((x , z) , refl) → x , refl}) ,
  (((λ { (x , refl) → (x , c) , refl}) , (λ { (x , refl) → refl})) ,
   ((λ { (x , refl) → (x , c) , refl}) , (λ { ((x , z) , refl) → refl})))

f-equiv-to-base-change-equiv : {A B : Set} → (f : A → B) → (C : B → Set) → is-equiv f → is-equiv (base-change f C)
f-equiv-to-base-change-equiv f C e = contr-map-to-equiv (base-change f C) (λ { (b , c) →
  ex-10-3iii (proj₁ (fib-base-change-equiv-fib f C (b , c)))
             (equiv-to-contr-map f e b)
             (proj₂ (fib-base-change-equiv-fib f C (b , c)))})

tot-fam : {A B : Set}  → {C : A → Set} → {D : B → Set}
  → (f : A → B) → (g : (x : A) → C x → D (f x)) → Σ A C → Σ B D
tot-fam f g (a , c) = f a , g a c

g-equiv-to-tot-fam-equiv : {A B : Set} → {C : A → Set} → {D : B → Set}
  → (f : A → B) → (g : (x : A) → C x → D (f x))
  → is-equiv f → ((x : A) → is-equiv (g x))
  → is-equiv (tot-fam {A} {B} {C} {D} f g)
g-equiv-to-tot-fam-equiv f g fe gx-equiv = {!!}

tot-fam-equiv-to-g-equiv : {A B : Set} → {C : A → Set} → {D : B → Set}
  → (f : A → B) → (g : (x : A) → C x → D (f x))
  → is-equiv f → is-equiv (tot-fam {A} {B} {C} {D} f g)
  → (x : A) → is-equiv (g x)
tot-fam-equiv-to-g-equiv f g fe te x = {!!}

is-id-sys : (A : Set) → (B : A → Set) → (a : A) → (b : B a) → Set₁
is-id-sys A B a b = (P : (x : A) → B x → Set) → sec (λ (h : (x : A) → (y : B x) → P x y) → h a b)
