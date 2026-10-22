{-# OPTIONS --without-K #-}
module ch10 where

open import ch09 public

is-contr : (A : Set) → Set
is-contr A = Σ A (λ a → (x : A) → x ≡ a)

const-centre-equiv-id : {A : Set} → (con : is-contr A) → (const {A} {A} {proj₁ con}) ∼ id {A}
const-centre-equiv-id (c , f) = λ {x → inv (concat (f x) refl)}

𝟙-contractible : is-contr 𝟙
𝟙-contractible = * , λ {* → refl}

Σ-≡-contractible : {A : Set} → (a : A) → is-contr (Σ A (λ x → a ≡ x))
Σ-≡-contractible a = ((a , refl)) , λ { (x , refl) → refl}

ev-pt : {A : Set} → {B : A → Set} → (a : A) → ((x : A) → B x) → B a
ev-pt a f = f a

has-sing-ind : {A : Set} → (a : A) → Set₁
has-sing-ind {A} a = (B : A → Set) → sec (ev-pt {A} {B} a)

ind-sing : {A : Set} → {B : A → Set} → (a : A) → has-sing-ind a → B a → (x : A) → B x
ind-sing {A} {B} a sing ba x = proj₁ (sing B) ba x

comp-sing : {A : Set} → {B : A → Set} → (a : A) → (si : has-sing-ind a) → (ev-pt a) ∘ (proj₁ (si B)) ∼ id
comp-sing {A} {B} a si x = proj₂ (si B) x

𝟙-sing-ind : has-sing-ind *
𝟙-sing-ind = λ B → (λ {b * → b}) , λ { b → refl}

contr-to-sing-ind : {A : Set} → (a : A) → is-contr A → has-sing-ind a
contr-to-sing-ind a (x , f) = λ B → (λ ba y → tr B (concat (f a) (inv (f y))) ba) , (λ z → ap (λ p → tr B p z) (right-inv (f a)))

sing-ind-to-contr : {A : Set} → (a : A) → has-sing-ind a → is-contr A
sing-ind-to-contr a si = a , ind-sing a si refl

fib : {A B : Set} → (f : A → B) → (b : B) → Set
fib {A} {B} f b = Σ A (λ a → f a ≡ b)

Eq-fib : {A B : Set} → (f : A → B) → {y : B} → fib f y → fib f y → Set
Eq-fib f (x , p) (x' , p') = Σ (x ≡ x') (λ α → p ≡ concat (ap f α) p')

rfl-Eq-fib : {A B : Set} → (f : A → B) → {y : B} → (s : fib f y) → Eq-fib f s s
rfl-Eq-fib f (x , p) = refl , inv (left-unit p)

≡-to-Eq-fib : {A B : Set} → (f : A → B) → {y : B} → (s t : fib f y) → s ≡ t → Eq-fib f s t
≡-to-Eq-fib f (x , refl) (y , refl) refl = refl , refl

is-contr-map : {A B : Set} → (f : A → B) → Set
is-contr-map {A} {B} f = (b : B) → is-contr (fib f b)

contr-map-to-equiv : {A B : Set} → (f : A → B) → is-contr-map f → is-equiv f
contr-map-to-equiv {A} {B} f contr = ((λ x → proj₁ (proj₁ (contr x))) , λ x → proj₂ (proj₁ (contr x))) , ((λ x → (proj₁ (proj₁ (contr x)))) , λ x → ap proj₁ (inv (proj₂ (contr (f x)) (x , refl))))

is-coh-inv : {A B : Set} → (f : A → B) → Set
is-coh-inv {A} {B} f = Σ (B → A) (λ g → Σ (f ∘ g ∼ id) (λ G → Σ (g ∘ f ∼ id) (λ H → (x : A) → G (f x) ≡ ap f (H x))))

eq-pair : {A : Set} → {B : A → Set} → (s t : Σ A B) → Eq-Σ s t → s ≡ t
eq-pair (s1 , s2) (t1 , t2) (refl , refl) = refl

eq-pair× : {A B : Set} → {p p' : A} → {q q' : B} → p ≡ p' → q ≡ q' → (p , q) ≡ (p' , q')
eq-pair× refl refl = refl

inv-inv : {A : Set} → {x y : A} → (p : x ≡ y) → inv (inv p) ≡ p
inv-inv refl = refl

tr-fib : {A B : Set} → (f : A → B) → {b : B} → {x y : A} → (p : x ≡ y) → (q : f x ≡ b) → tr (λ z → f z ≡ b) p q ≡ concat (inv (ap f p)) q
tr-fib f refl q = inv (left-unit q)

tr-× : {A : Set} → (P Q : A → Set) → {u v : A} → (α : u ≡ v) → (w : P u × Q u)
     → tr (λ a → P a × Q a) α w ≡ (tr P α (proj₁ w) , tr Q α (proj₂ w))
tr-× P Q refl (p , q) = refl

coh-inv-to-contr-fib : {A B : Set} → (f : A → B) → is-coh-inv f → is-contr-map f
coh-inv-to-contr-fib f (g , (G , (H , K))) b =
  (g b , G b) , λ { (a , refl) →
    eq-pair (a , refl) (g (f a) , G (f a)) (inv (H a) ,
      concat (tr-fib f (inv (H a)) refl)
        (concat (right-unit (inv (ap f (inv (H a)))))
          (concat (ap inv (ap-inv f (H a)))
            (concat (inv-inv (ap f (H a)))
              (inv (K a))))))}

nat-htpy : {A B : Set} → {f g : A → B} → {x y : A} → (H : f ∼ g) → (p : x ≡ y) → concat (ap f p) (H y) ≡ concat (H x) (ap g p)
nat-htpy {A} {B} {f} {g} {x} {y} H refl = concat (left-unit (H x)) (inv (right-unit (H y)))


nat-htpy-id : {A : Set} → (f : A → A) → {x : A} → (H : f ∼ id) → (H (f x)) ≡ (ap f (H x))
nat-htpy-id {A} f {x} H = inv (
  concat (con-inv (ap f (H x)) (H x) (concat (H (f x)) (H x))
    (concat (nat-htpy H (H x)) (ap (concat (H (f x))) (ap-id (H x)))))
  (concat (assoc (H (f x)) (H x) (inv (H x)))
    (concat (ap (concat (H (f x))) (right-inv (H x)))
      (right-unit (H (f x))))))

inv-to-coh-inv : {A B : Set} → (f : A → B) → has-inverse f → is-coh-inv f
inv-to-coh-inv f (g , (fg , gf)) = g , (G' , (gf , K))
  where
    G' : f ∘ g ∼ id
    G' y = concat (inv (fg (f (g y)))) (concat (ap f (gf (g y))) (fg y))
    K : (a : _) → G' (f a) ≡ ap f (gf a)
    K a = concat
      (ap (concat (inv (fg (f (g (f a))))))
        (concat
          (ap (λ t → concat t (fg (f a)))
            (concat (ap (ap f) (nat-htpy-id (λ x → g (f x)) {a} gf))
              (ap-comp (λ x → g (f x)) f (gf a))))
          (nat-htpy (λ x → fg (f x)) (gf a))))
      (concat
        (inv (assoc (inv (fg (f (g (f a))))) (fg (f (g (f a)))) (ap f (gf a))))
        (concat
          (ap (λ t → concat t (ap f (gf a))) (left-inv (fg (f (g (f a))))))
          (left-unit (ap f (gf a)))))

equiv-to-contr-map : {A B : Set} → (f : A → B) → is-equiv f → is-contr-map f
equiv-to-contr-map f e = coh-inv-to-contr-fib f (inv-to-coh-inv f (equiv-to-inverse f e))

identity-contr : {A : Set} → (a : A) → is-contr (Σ A (λ x → x ≡ a))
identity-contr a = (a , refl) , λ { (x , refl) → refl}

contr-to-eq-contr : {A : Set} → is-contr A → (x y : A) → is-contr (x ≡ y)
contr-to-eq-contr (a , f) x y = concat (f x) (inv (f y)) , λ {refl → inv (right-inv (f x))}

retr-to-contr-to-contr : {A B : Set} → (f : A → B) → retr f → is-contr B → is-contr A
retr-to-contr-to-contr f (g , gf) (b , p) = g b , λ {a → concat (inv (gf a)) (ap g (p (f a)))}

const𝟙-equiv-to-A-contr : {A : Set} → is-equiv (const {A} {𝟙} {*}) → is-contr A
const𝟙-equiv-to-A-contr ((f , cf) , (g , gc)) = g * , λ a → concat (inv (gc a)) (ap g refl)

A-contr-to-const𝟙-equiv : {A : Set} → is-contr A → is-equiv (const {A} {𝟙} {*})
A-contr-to-const𝟙-equiv {A} (a , p) = (const {𝟙} {A} {a} , λ { * → refl}) , ((const {𝟙} {A} {a} , λ {x →  concat (p ((const ∘ const {A} {𝟙} {*}) x)) (inv (p x))}))

contr-contr-to-equiv : {A B : Set} → (f : A → B) → is-contr A → is-contr B → is-equiv f
contr-contr-to-equiv f (a , pA) (b , pB) = ((λ x → a) , λ x → concat (pB (f a)) (inv (pB x))) , ((λ x → a) , λ x → concat (pA a) (inv (pA x)))

is-contr-codomain-equiv : {A B : Set} → (f : A → B) → is-contr A → is-equiv f → is-contr B
is-contr-codomain-equiv f (a , pA) ((g , fg) , (h , hf)) = f a , λ b → concat (inv (fg b)) (ap f (pA (g b)))

is-contr-domain-equiv : {A B : Set} → (f : A → B) → is-contr B → is-equiv f → is-contr A
is-contr-domain-equiv f (b , pB) ((g , fg) , (h , hf)) = h b , λ a → concat (inv (hf a)) (ap h (pB (f a)))

-- Fin k is not contr for k ≠ 1
inl-ne-inr : {A B : Set} → (a : A) → (b : B) → ¬ (inl a ≡ inr b)
inl-ne-inr a b p = tr (λ { (inl _) → 𝟙 ; (inr _) → 𝟘 }) p *

Fin-0-not-contr : ¬ (is-contr (Fin 0ℕ))
Fin-0-not-contr (c , _) = c

Fin-2+-not-contr : (k : ℕ) → ¬ (is-contr (Fin (succℕ (succℕ k))))
Fin-2+-not-contr k (_ , f) = inl-ne-inr (inr *) * (concat (f (inl (inr *))) (inv (f (inr *))))

contr-to-prod-contr : {A B : Set} → is-contr A → is-contr B → is-contr (A × B)
contr-to-prod-contr (a , pA) (b , pB) = (a , b) , λ {(x , y) → eq-pair (x , y) (a , b) (pA x , pB (tr (λ v → _) (pA x) y))}

prod-contr-to-contr : {A B : Set} → is-contr (A × B) → (is-contr A) × (is-contr B)
prod-contr-to-contr {A} {B} ((a , b) , pAB) =
  (a , λ x → (ap proj₁ (pAB (x , b)))) ,
  (b , λ x → (ap proj₂ (pAB (a , x))))

tr-inv-tr : {A : Set} → {B : A → Set} → {x y : A} → (p : x ≡ y) → (bx : B x) → tr B (inv p) (tr B p bx) ≡ bx
tr-inv-tr refl bx = refl

contr-loop-refl : {A : Set} → (a : A) → (pA : (x : A) → x ≡ a) → pA a ≡ refl
contr-loop-refl a pA = concat (proj₂ c (pA a)) (inv (proj₂ c refl))
  where
  c = contr-to-eq-contr (a , pA) a a

is-equiv-pair-contr-base : {A : Set} (Ac : is-contr A) (B : A → Set) → let a = proj₁ Ac in is-equiv {A = B a} {B = Σ A B} (λ y → (a , y))
is-equiv-pair-contr-base (a , pA) B = ((λ { (x , b) → tr B (pA x) b}) , λ {(x , b) → eq-pair ((a , tr B (pA x) b)) ((x , b)) (inv (pA x) , tr-inv-tr (pA x) b)}) , ((λ {(x , b) → tr B (pA x) b}) , λ {b → ap (λ p → tr B p b) (contr-loop-refl a pA)})

is-equiv-fib-proj₁ : {A : Set} → {B : A → Set} → (a : A) → is-equiv {fib (proj₁ {A = A} {B = B}) a} {B a} (λ { ((x , y) , p) → tr B p y})
is-equiv-fib-proj₁ a = ((λ {ba → (a , ba) , refl}) , λ x → refl) , ((λ x → (a , x) , refl) , λ { ((x , bx) , refl) → refl})

proj₁-equiv-to-fib-contr : {A : Set} → {B : A → Set} → is-equiv (proj₁ {A = A} {B = B}) → (x : A) → is-contr (B x)
proj₁-equiv-to-fib-contr {A} {B} ((f , pf) , (g , gp)) a = tr B (proj₂ centre-fib) (proj₂ (proj₁ centre-fib)) , λ ba → ap (λ s → tr B (proj₂ s) (proj₂ (proj₁ s))) (proj₂ fib-contr ((a , ba) , refl))
  where
    fib-contr : is-contr (fib (proj₁ {A = A} {B = B}) a)
    fib-contr = equiv-to-contr-map (proj₁ {A = A} {B = B}) ((f , pf) , (g , gp)) a
    centre-fib : fib (proj₁ {A = A} {B = B}) a
    centre-fib = proj₁ fib-contr

fib-contr-to-proj₁-equiv : {A : Set} → {B : A → Set} → ((x : A) → is-contr (B x)) → is-equiv (proj₁ {A = A} {B = B})
fib-contr-to-proj₁-equiv {A} {B} a→contrBa = ((λ a → a , proj₁ (a→contrBa a)) , λ x → refl) , ((λ a → a , proj₁ (a→contrBa a)) , λ { (x , y) → eq-pair (x , proj₁ (a→contrBa x)) (x , y) (refl , inv (proj₂ (a→contrBa x) y))})

sec-pair-equiv-to-fib-contr : {A : Set} → {B : A → Set} → (b : (x : A) → B x) → is-equiv {A} {Σ A B} (λ x → x , b x) → (x : A) → is-contr (B x)
sec-pair-equiv-to-fib-contr {A} {B} b ((f , pf) , (g , gp)) x = b x , λ y →
  let pe = pair-eq (f (x , y) , b (f (x , y))) (x , y) (pf (x , y))
  in concat (inv (proj₂ pe)) (apd b (proj₁ pe))

fib-contr-to-sec-pair-equiv : {A : Set} → {B : A → Set} → (b : (x : A) → B x) → ((x : A) → is-contr (B x)) → is-equiv {A} {Σ A B} (λ x → x , b x)
fib-contr-to-sec-pair-equiv {A} {B} b c = (proj₁ , λ { (x , y) → eq-pair (x , b x) (x , y) (refl , concat (proj₂ (c x) (b x)) (inv (proj₂ (c x) y)))}) , (proj₁ , λ {a → refl})

fib-repl : {A B : Set} → (f : A → B) → Σ (A ≃ Σ B (λ y → fib f y)) (λ e → (f ∼ proj₁ ∘ (proj₁ e)))
fib-repl f = ((λ x → f x , (x , refl)) , (((λ { (b , (a , refl)) → a}) , λ { (b , (a , refl)) → refl}) , ((λ { (b , (a , refl)) → a}) , λ a → refl))) , λ a → refl

