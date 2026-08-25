{-# OPTIONS --without-K #-}
module ch13 where

open import ch12 public

htpy-eq : {A : Set} → {B : A → Set} → (f g : (x : A) → B x) → f ≡ g → f ∼ g
htpy-eq f g refl = λ x → refl

postulate
    fun-ext : {A : Set} → {B : A → Set} → (f g : (x : A) → B x) → is-equiv (htpy-eq f g)

eq-htpy : {A : Set} → {B : A → Set} → (f g : (x : A) → B x) → f ∼ g → f ≡ g
eq-htpy f g = proj₁ (proj₁ (fun-ext f g))

htpy-eq-eq-htpy : {A : Set} → {B : A → Set} → (f g : (x : A) → B x) → (H : f ∼ g) → htpy-eq f g (eq-htpy f g H) ≡ H
htpy-eq-eq-htpy f g = proj₂ (proj₁ (fun-ext f g))

eq-htpy-htpy-eq : {A : Set} → {B : A → Set} → (f g : (x : A) → B x) → (p : f ≡ g) → eq-htpy f g (htpy-eq f g p) ≡ p
eq-htpy-htpy-eq f g p =
  concat
    (sec-equiv-retr (htpy-eq f g) (proj₁ (fun-ext f g)) (proj₂ (fun-ext f g)) (htpy-eq f g p))
    (proj₂ (proj₂ (fun-ext f g)) p)

-- Proposition 13.1.1
-- (i) function extensionality holds at f
funext-at : {A : Set} → {B : A → Set} → (f : (x : A) → B x) → Set
funext-at {A} {B} f = (g : (x : A) → B x) → is-equiv (htpy-eq f g)

-- (ii) the total space of homotopies out of f is contractible
is-contr-total-htpy : {A : Set} → {B : A → Set} → (f : (x : A) → B x) → Set
is-contr-total-htpy {A} {B} f = is-contr (Σ ((x : A) → B x) (λ g → f ∼ g))

-- (iii) homotopy induction: evaluation at (f , rfl-htpy f) has a section
ev-htpy : {A : Set} → {B : A → Set} → (f : (x : A) → B x)
  → (P : (g : (x : A) → B x) → f ∼ g → Set)
  → ((g : (x : A) → B x) → (H : f ∼ g) → P g H) → P f (rfl-htpy f)
ev-htpy f P s = s f (rfl-htpy f)

has-htpy-ind : {A : Set} → {B : A → Set} → (f : (x : A) → B x) → Set₁
has-htpy-ind {A} {B} f = (P : (g : (x : A) → B x) → f ∼ g → Set) → sec (ev-htpy f P)

funext-at-to-is-contr-total-htpy : {A : Set} → {B : A → Set} → (f : (x : A) → B x)
  → funext-at f → is-contr-total-htpy f
funext-at-to-is-contr-total-htpy {A} {B} f fext = contr-equiv-to-contr (tot (htpy-eq f)) (Σ-≡-contractible f) (fam-equiv-to-tot-equiv (htpy-eq f) fext)

is-contr-total-htpy-to-has-htpy-ind : {A : Set} → {B : A → Set} → (f : (x : A) → B x)
  → is-contr-total-htpy f → has-htpy-ind f
is-contr-total-htpy-to-has-htpy-ind f contr P =
  (λ p₀ g H → proj₁ sing p₀ (g , H)) , proj₂ sing
  where
    sing = contr-to-sing-ind (f , rfl-htpy f) contr (λ s → P (proj₁ s) (proj₂ s))

has-htpy-ind-to-funext-at : {A : Set} → {B : A → Set} → (f : (x : A) → B x)
  → has-htpy-ind f → funext-at f
has-htpy-ind-to-funext-at f hind =
  total-contr-to-fam-equiv (rfl-htpy f) (htpy-eq f) refl (sing-ind-to-contr (f , rfl-htpy f) bridge)
  where
    bridge : has-sing-ind (f , rfl-htpy f)
    bridge B' = (λ b₀ → λ { (g , H) → proj₁ (hind (λ g' H' → B' (g' , H'))) b₀ g H })
              , proj₂ (hind (λ g' H' → B' (g' , H')))

-- Theorem 13.1.2
-- (i) the function extensionality principle
funext-principle : Set₁
funext-principle = (A : Set) → (B : A → Set) → (f : (x : A) → B x) → funext-at f

-- (ii) the weak function extensionality principle
weak-funext : Set₁
weak-funext = (A : Set) → (B : A → Set) → ((x : A) → is-contr (B x)) → is-contr ((x : A) → B x)

funext-principle-to-weak-funext : funext-principle → weak-funext
funext-principle-to-weak-funext fext A B xcontrBx = (λ a → proj₁ (xcontrBx a)) , λ aBa → proj₁ (proj₁ (fext A B aBa λ a → proj₁ (xcontrBx a))) λ a → proj₂ (xcontrBx a) (aBa a)

weak-funext-to-funext-principle : weak-funext → funext-principle
weak-funext-to-funext-principle wfext A B f g = total-contr-to-fam-equiv (rfl-htpy f) (htpy-eq f) refl
  (retr-to-contr-to-contr (λ {(h , fh) → (λ x → (h x , fh x)) })
    ((λ p → (λ x → proj₁ (p x)) , (λ x → proj₂ (p x))) , λ {(h , fh) → refl})
    (wfext A (λ x → Σ (B x) λ b → f x ≡ b) λ a → Σ-≡-contractible (f a)))
  g

fam-trunc-to-Π-trunc : {A : Set} → {B : A → Set} → {k : 𝕋} → ((x : A) → is-trunc k (B x)) → is-trunc k ((x : A) → B x)
fam-trunc-to-Π-trunc {A} {B} { -2𝕋} xcontrBx = (λ a → xcentre a) , λ aBa → eq-htpy aBa xcentre λ a → eqcentre a (aBa a)
  where
    xcentre : (a : A) → B a
    xcentre a = proj₁ (xcontrBx a)
    eqcentre : (a : A) → (x : B a) → x ≡ (xcentre a)
    eqcentre a x = proj₂ (xcontrBx a) x
fam-trunc-to-Π-trunc {A} {B} {succ𝕋 k} xtruncBx f g = equiv-to-same-k-type ((htpy-eq f g , fun-ext f g)) (fam-trunc-to-Π-trunc {k = k} λ a → xtruncBx a (f a) (g a))

codom-trunc-to-→-trunc : {A B : Set} → {k : 𝕋} → is-trunc k B → is-trunc k (A → B)
codom-trunc-to-→-trunc Btrunc = fam-trunc-to-Π-trunc λ a → Btrunc

¬-prop : (A : Set) → is-prop (¬ A)
¬-prop A = codom-trunc-to-→-trunc λ ()

-- Π over 𝟙 is evaluation at *  (needs funext, so it lives here rather than next to Σ-𝟙 in ch09)
Π-𝟙 : (B : 𝟙 → Set) → ((x : 𝟙) → B x) ≃ B *
Π-𝟙 B = ev , ((cnst , λ b → refl) , (cnst , λ h → eq-htpy _ _ (indUnit {P = λ x → cnst (ev h) x ≡ h x} refl)))
  where
  ev : ((x : 𝟙) → B x) → B *
  ev h = h *

  cnst : B * → (x : 𝟙) → B x
  cnst b = indUnit b

choice : {A : Set} → {B : A → Set} → {C : (x : A) → B x → Set} → ((x : A) → Σ (B x) (C x)) → (Σ ((x : A) → B x) (λ f → (x : A) → C x (f x)))
choice h = (λ x → proj₁ (h x)) , λ x → proj₂ (h x)

choice-inv : {A : Set} → {B : A → Set} → {C : (x : A) → B x → Set} → (Σ ((x : A) → B x) (λ f → (x : A) → C x (f x))) → ((x : A) → Σ (B x) (C x))
choice-inv (f , g) x = f x , g x

choice-equiv : {A : Set} → {B : A → Set} → {C : (x : A) → B x → Set} → is-equiv (choice {A} {B} {C})
choice-equiv {A} {B} {C} = (choice-inv , λ {(f , g) → refl}) , (choice-inv , λ {h → eq-htpy ((choice-inv ∘ choice) h) (id h) λ x → eq-pair _ _ (refl , refl)})

Π-distrib-Σ : {A : Set} → {B : A → Set} → {C : (x : A) → B x → Set} → ((x : A) → Σ (B x) (C x)) ≃ (Σ ((x : A) → B x) (λ f → (x : A) → C x (f x)))
Π-distrib-Σ {A} {B} {C} = choice , choice-equiv

Π-distrib-× : {I : Set} → (P Q : I → Set)
  → ((i : I) → P i × Q i) ≃ (((i : I) → P i) × ((i : I) → Q i))
Π-distrib-× {I} P Q = fwd , ((bwd , sec-htpy) , (bwd , retr-htpy))
  where
  fwd : ((i : I) → P i × Q i) → ((i : I) → P i) × ((i : I) → Q i)
  fwd iPQ = (λ i → proj₁ (iPQ i)) , λ i → proj₂ (iPQ i)

  bwd : ((i : I) → P i) × ((i : I) → Q i) → ((i : I) → P i × Q i)
  bwd (iP , iQ) i = (iP i , iQ i)

  sec-htpy : fwd ∘ bwd ∼ id
  sec-htpy (iP , iQ) = eq-pair× refl refl

  retr-htpy : bwd ∘ fwd ∼ id
  retr-htpy iPQ = eq-htpy _ _ λ i → η-pair (iPQ i)

Π-fib-equiv-sec : {A B : Set} → (f : A → B) → ((b : B) → fib f b) ≃ sec f
Π-fib-equiv-sec {A} {B} f = choice , choice-equiv

total-htpy-is-contr : (A : Set) → is-contractible (Σ (A → A) (λ f → f ∼ id))
total-htpy-is-contr A = contr-equiv-to-contr (tot (λ f → htpy-eq f id)) (identity-contr id) (fam-equiv-to-tot-equiv (λ x → htpy-eq x id) λ f → fun-ext f id)

sec-proj₁-equiv-Π : {A : Set} → {B : A → Set} → sec (proj₁ {A = A} {B = B}) ≃ ((x : A) → B x)
sec-proj₁-equiv-Π {A} {B} = concat-≃ distrib (concat-≃ reassoc collapse)
  where
    distrib : sec (proj₁ {A = A} {B = B})
          ≃ Σ (Σ (A → A) (λ f → (x : A) → B (f x))) (λ y → proj₁ y ∼ id)
    distrib = base-change (choice {A} {λ _ → A} {λ _ → B}) (λ y → proj₁ y ∼ id)
          , f-equiv-to-base-change-equiv (choice {A} {λ _ → A} {λ _ → B})
              (λ y → proj₁ y ∼ id) (choice-equiv {A} {λ _ → A} {λ _ → B})

    reassoc : Σ (Σ (A → A) (λ f → (x : A) → B (f x))) (λ y → proj₁ y ∼ id)
          ≃ Σ (Σ (A → A) (λ f → f ∼ id)) (λ w → (x : A) → B (proj₁ w x))
    reassoc = (λ {((f , g) , H) → (f , H) , g}) , (((λ {((x , x₂) , x₁) → (x , x₁) , x₂}) , λ {((x , x₂) , x₁) → refl}) , ((λ {((x , x₂) , x₁) → (x , x₁) , x₂}) , λ {((x , x₂) , x₁) → refl}))

    collapse : Σ (Σ (A → A) (λ f → f ∼ id)) (λ w → (x : A) → B (proj₁ w x))
          ≃ ((x : A) → B x)
    collapse = inv-≃ ((λ y → proj₁ (total-htpy-is-contr A) , y) , is-equiv-pair-contr-base (total-htpy-is-contr A) λ v → (x : A) → B (proj₁ v x))

Π-id-sys : {A : Set} → {B : A → Set} → (E : (a : A) → B a → B a → Set)
  → (e : (a : A) → (b : B a) → E a b b)
  → ((a : A) → (b : B a) → is-id-sys (E a b) b (e a b))
  → (f : (x : A) → B x)
  → is-id-sys (λ g → (x : A) → E x (f x) (g x)) f (λ x → e x (f x))
Π-id-sys {A} {B} E e hyp f P = total-contr-to-id-sys (λ x → e x (f x)) (λ x₁ x₂ x₃ → tr (E x₃ (f x₃)) (htpy-eq f x₁ x₂ x₃) (e x₃ (f x₃))) refl
  (contr-equiv-to-contr (proj₁ Π-distrib-Σ) (fam-trunc-to-Π-trunc fiber-contr) (proj₂ Π-distrib-Σ)) P
  where
    canonical-map : (a : A) → (y : B a) → (f a ≡ y) → E a (f a) y
    canonical-map a y p = tr (E a (f a)) p (e a (f a))

    fiber-contr : (a : A) → is-contractible (Σ (B a) (E a (f a)))
    fiber-contr a = fam-equiv-to-total-contr (e a (f a)) (canonical-map a) refl
      (id-sys-to-fam-equiv (e a (f a)) (canonical-map a) refl (hyp a (f a)))

ev-pair-dep : {A : Set} → {B : A → Set} → {C : Σ A B → Set} → ((z : Σ A B) → C z) → ((x : A) → (y : B x) → C (x , y))
ev-pair-dep f x y = f (x , y)

dep-univ-prop-Σ : {A : Set} → {B : A → Set} → {C : Σ A B → Set} → is-equiv (ev-pair-dep {A} {B} {C})
dep-univ-prop-Σ = (indΣ , λ x → rfl-htpy (λ x₁ → x₁) x) , (indΣ , λ x → eq-htpy _ _ (indΣ λ x₁ y → refl))

ev-pair-× : {A B X : Set} → (A × B → X) → (A → B → X)
ev-pair-× f a b = f (a , b)

univ-prop-× : {A B X : Set} → is-equiv (ev-pair-× {A} {B} {X})
univ-prop-× {A} {B} {X} = dep-univ-prop-Σ {A} {λ _ → B} {λ _ → X}

univ-prop-Σ-map : {A : Set} → {B : A → Set} → {X : Set} → (Σ A B → X) → (a : A) → B a → X
univ-prop-Σ-map f a b = f (a , b)

univ-prop-Σ : {A : Set} → {B : A → Set} → {X : Set} → is-equiv (univ-prop-Σ-map {A} {B} {X})
univ-prop-Σ {A} {B} {X} = dep-univ-prop-Σ {A} {B} {λ _ → X}

ev-refl-dep : {A : Set} → {a : A} → {B : (x : A) → a ≡ x → Set} → ((x : A) → (p : a ≡ x) → B x p) → B a refl
ev-refl-dep f = f _ refl

dep-univ-prop-id : {A : Set} → {a : A} → {B : (x : A) → a ≡ x → Set} → is-equiv (ev-refl-dep {A} {a} {B})
dep-univ-prop-id {A} {a} {B} = (ind≡ , (λ x → refl)) , (ind≡ , λ f → eq-htpy _ _ λ y → eq-htpy _ _ (ind≡ {A} {a} {λ x p → ind≡ (ev-refl-dep f) x p ≡ f x p} refl y))

univ-prop-id-map : {A : Set} → {a : A} → {B : A → Set} → ((x : A) → (a ≡ x) → B x) → B a
univ-prop-id-map f = f _ refl

univ-prop-id : {A : Set} → {a : A} → {B : A → Set} → is-equiv (univ-prop-id-map)
univ-prop-id {A} {a} {B} = dep-univ-prop-id {A} {a} {λ x _ → B x}

-- Theorem 13.4.1 — composing with equivalences

-- the precomposition map  (– ∘ f)  on dependent functions
precomp-Π : {A B : Set} → (f : A → B) → (P : B → Set)
  → ((y : B) → P y) → ((x : A) → P (f x))
precomp-Π f P h x = h (f x)

-- the precomposition map  (– ∘ f)  on ordinary functions
precomp : {A B : Set} → (f : A → B) → (X : Set)
  → (B → X) → (A → X)
precomp f X g x = g (f x)

-- (ii) precomposition is an equivalence for every family P over B
precomp-Π-is-equiv : {A B : Set} → (f : A → B) → Set₁
precomp-Π-is-equiv {A} {B} f = (P : B → Set) → is-equiv (precomp-Π f P)

-- (iii) precomposition is an equivalence for every type X
precomp-is-equiv : {A B : Set} → (f : A → B) → Set₁
precomp-is-equiv {A} {B} f = (X : Set) → is-equiv (precomp f X)

tr-ap : {A B : Set} → (P : B → Set) → (f : A → B) → {x y : A} → (p : x ≡ y) → (u : P (f x)) → tr P (ap f p) u ≡ tr (λ x → P (f x)) p u
tr-ap P f refl u = refl

-- the theorem: (i) ⇒ (ii) ⇒ (iii) ⇒ (i)
is-equiv-to-precomp-Π-is-equiv : {A B : Set} → (f : A → B)
  → is-equiv f → precomp-Π-is-equiv f
is-equiv-to-precomp-Π-is-equiv f fequiv P with inv-to-coh-inv f (equiv-to-inverse f fequiv)
... | (g , (G , (H , K))) =
    ((λ aPfa b → tr P (G b) (aPfa (g b))) ,
     λ aPfa → eq-htpy _ _ λ y →
       concat (ap (λ q → tr P q (aPfa (g (f y)))) (K y))
              (concat (tr-ap P f (H y) (aPfa (g (f y)))) (apd aPfa (H y)))) ,
    ((λ aPfa b → tr P (G b) (aPfa (g b))) ,
     λ h → eq-htpy _ _ (λ y → apd h (G y)))

precomp-Π-is-equiv-to-precomp-is-equiv : {A B : Set} → (f : A → B)
  → precomp-Π-is-equiv f → precomp-is-equiv f
precomp-Π-is-equiv-to-precomp-is-equiv f pre = λ X → pre (λ v → X)

is-equiv-to-injective : {A B : Set} → (f : A → B) → is-equiv f → {x y : A} → f x ≡ f y → x ≡ y
is-equiv-to-injective f e {x} {y} p with equiv-to-inverse f e
... | (g , (fg , gf)) = concat (inv (gf x)) (concat (ap g p) (gf y))

precomp-is-equiv-to-is-equiv : {A B : Set} → (f : A → B)
  → precomp-is-equiv f → is-equiv f
precomp-is-equiv-to-is-equiv {A} {B} f pre = (g , sec-eq) , (g , retr-eq)
  where
    invA : (A → A) → (B → A)
    invA = proj₁ (equiv-to-inverse (precomp f A) (pre A))

    g : B → A
    g = invA id

    gf-eq : g ∘ f ≡ id
    gf-eq = proj₁ (proj₂ (equiv-to-inverse (precomp f A) (pre A))) id

    retr-eq : g ∘ f ∼ id
    retr-eq = htpy-eq (g ∘ f) id gf-eq

    fg-eq : f ∘ g ≡ id
    fg-eq = is-equiv-to-injective (precomp f B) (pre B) (ap (λ h → f ∘ h) gf-eq)

    sec-eq : f ∘ g ∼ id
    sec-eq = htpy-eq (f ∘ g) id fg-eq

-- 13.5 Strong induction on ℕ
strong-indℕ : {P : ℕ → Set} → P 0ℕ → ((n : ℕ) → ((m : ℕ) → m ≤ℕ n → P m) → P (succℕ n)) → (n : ℕ) → P n
strong-indℕ {P} p0 f n = indℕ {P = P̃} p̃0 p̃S n n (≤-rflℕ n)
  where
    P̃ : ℕ → Set
    P̃ k = (m : ℕ) → m ≤ℕ k → P m

    p̃0 : P̃ 0ℕ
    p̃0 0ℕ p = p0
    p̃0 (succℕ m) ()

    p̃S : (k : ℕ) → P̃ k → P̃ (succℕ k)
    p̃S k prev m p with <-or-≤ℕ m (succℕ k)
    ... | inl m<sk = prev m (<-to-succ-≤ℕ m (succℕ k) m<sk)
    ... | inr sk≤m = tr P (≤-antisymℕ (succℕ k) m sk≤m p) (f k prev)

-- Exercises
-- 13.1
inv-htpy-equiv : {A : Set} → {B : A → Set} → {f g : (x : A) → B x} → is-equiv (inv-htpy {A} {B} {f} {g})
inv-htpy-equiv = (inv-htpy , λ H → eq-htpy ((inv-htpy ∘ inv-htpy) H) (id H) λ x → inv-inv (H x)) , (inv-htpy , λ H → eq-htpy _ _ λ x → inv-inv (H x))

concat-htpy-equiv : {A : Set} → {B : A → Set} → {f g h : (x : A) → B x} → (H : f ∼ g) → is-equiv (concat-htpy {A} {B} {f} {g} {h} H)
concat-htpy-equiv H =
  ((λ K a → concat (inv (H a)) (K a)) ,
   λ K → eq-htpy _ _ λ x →
     concat (inv (assoc (H x) (inv (H x)) (K x)))
            (concat (ap (λ q → concat q (K x)) (right-inv (H x))) (left-unit (K x)))) ,
  ((λ L a → concat (inv (H a)) (L a)) ,
   λ L → eq-htpy _ _ λ x →
     concat (inv (assoc (inv (H x)) (H x) (L x)))
            (concat (ap (λ q → concat q (L x)) (left-inv (H x))) (left-unit (L x))))

concat-htpy' : {A : Set} → {B : A → Set} → {f g h : (x : A) → B x} → g ∼ h → f ∼ g → f ∼ h
concat-htpy' K H = concat-htpy H K

concat-htpy'-equiv : {A : Set} → {B : A → Set} → {f g h : (x : A) → B x} → (K : g ∼ h) → is-equiv (concat-htpy' {A} {B} {f} {g} {h} K)
concat-htpy'-equiv K =
  ((λ L a → concat (L a) (inv (K a))) ,
   λ L → eq-htpy _ _ λ x →
     concat (assoc (L x) (inv (K x)) (K x))
            (concat (ap (λ q → concat (L x) q) (left-inv (K x))) (right-unit (L x)))) ,
  ((λ M a → concat (M a) (inv (K a))) ,
   λ H → eq-htpy _ _ λ x →
     concat (assoc (H x) (K x) (inv (K x)))
            (concat (ap (λ q → concat (H x) q) (right-inv (K x))) (right-unit (H x))))

-- 13.2
-- (a) pointed maps: Σ (h : A → B) (h a ≡ b)
pointed-map : {A B : Set} → (a : A) → (b : B) → Set
pointed-map {A} {B} a b = Σ (A → B) (λ h → h a ≡ b)

Eq-pointed-map : {A B : Set} → (a : A) → (b : B) → (s t : pointed-map a b) → Set
Eq-pointed-map a b (h , p) (h' , p') = Σ (h ∼ h') (λ H → concat (inv (H a)) p ≡ p')

pointed-map-eq : {A B : Set} → (a : A) → (b : B) → (s t : pointed-map a b) → s ≡ t → Eq-pointed-map a b s t
pointed-map-eq {A} {B} a b (f , fab) (g , gab) refl = rfl-htpy f , left-unit fab

ap-ev : {A : Set} → {B : A → Set} → (f g : (x : A) → B x) → (p : f ≡ g) → (x : A) → ap (λ h → h x) p ≡ htpy-eq f g p x
ap-ev f g refl x = refl

ap-ev-eq-htpy : {A : Set} → {B : A → Set} → (f g : (x : A) → B x) → (H : f ∼ g) → (x : A) → ap (λ h → h x) (eq-htpy f g H) ≡ H x
ap-ev-eq-htpy f g H x = concat (ap-ev f g (eq-htpy f g H) x) (htpy-eq _ _ (htpy-eq-eq-htpy f g H) x)

pointed-map-eq-is-equiv : {A B : Set} → (a : A) → (b : B) → (s t : pointed-map a b) → is-equiv (pointed-map-eq a b s t)
pointed-map-eq-is-equiv {A} {B} a b (f , fab) (g , gab) =
  total-contr-to-fam-equiv (rfl-htpy f , left-unit fab) (pointed-map-eq a b (f , fab)) refl pointed-total-contr (g , gab)
  where
    Fib : Σ (A → B) (λ h → f ∼ h) → Set
    Fib hH = Σ (proj₁ hH a ≡ b) (λ hab → concat (inv (proj₂ hH a)) fab ≡ hab)

    fib-swap : (h : A → B)
      → Σ (h a ≡ b) (λ hab → Σ (f ∼ h) (λ H → concat (inv (H a)) fab ≡ hab))
      ≃ Σ (f ∼ h) (λ H → Σ (h a ≡ b) (λ hab → concat (inv (H a)) fab ≡ hab))
    fib-swap h = Σ-swap (λ hab H → concat (inv (H a)) fab ≡ hab)

    assoc-fwd : Σ (pointed-map a b) (Eq-pointed-map a b (f , fab))
          ≃ Σ (A → B) (λ h → Σ (h a ≡ b) (λ hab → Σ (f ∼ h) (λ H → concat (inv (H a)) fab ≡ hab)))
    assoc-fwd = Σ-assoc (λ h → h a ≡ b) (λ z → Eq-pointed-map a b (f , fab) z)

    swap-fib : Σ (A → B) (λ h → Σ (h a ≡ b) (λ hab → Σ (f ∼ h) (λ H → concat (inv (H a)) fab ≡ hab)))
          ≃ Σ (A → B) (λ h → Σ (f ∼ h) (λ H → Σ (h a ≡ b) (λ hab → concat (inv (H a)) fab ≡ hab)))
    swap-fib = tot (λ h → proj₁ (fib-swap h)) , fam-equiv-to-tot-equiv (λ h → proj₁ (fib-swap h)) (λ h → proj₂ (fib-swap h))

    assoc-bwd : Σ (A → B) (λ h → Σ (f ∼ h) (λ H → Σ (h a ≡ b) (λ hab → concat (inv (H a)) fab ≡ hab)))
          ≃ Σ (Σ (A → B) (λ h → f ∼ h)) Fib
    assoc-bwd = inv-≃ (Σ-assoc (λ h → f ∼ h) Fib)

    fib-contr : (hH : Σ (A → B) (λ h → f ∼ h)) → is-contractible (Fib hH)
    fib-contr hH = Σ-≡-contractible (concat (inv (proj₂ hH a)) fab)

    drop-fib : Σ (Σ (A → B) (λ h → f ∼ h)) Fib ≃ Σ (A → B) (λ h → f ∼ h)
    drop-fib = proj₁ , fib-contr-to-proj₁-equiv fib-contr

    htpy-total-equiv : Σ (pointed-map a b) (Eq-pointed-map a b (f , fab)) ≃ Σ (A → B) (λ h → f ∼ h)
    htpy-total-equiv = concat-≃ assoc-fwd (concat-≃ swap-fib (concat-≃ assoc-bwd drop-fib))

    pointed-total-contr : is-contractible (Σ (pointed-map a b) (Eq-pointed-map a b (f , fab)))
    pointed-total-contr =
      contr-equiv-to-contr (proj₁ (inv-≃ htpy-total-equiv))
        (funext-at-to-is-contr-total-htpy {A} {λ _ → B} f (fun-ext f))
        (proj₂ (inv-≃ htpy-total-equiv))

-- (b) commuting triangles: Σ (h : A → B) (f ∼ g ∘ h)
comm-tri-post : {A B X : Set} → (f : A → X) → (g : B → X) → Set
comm-tri-post {A} {B} f g = Σ (A → B) (λ h → triangle-commutes f h g)

Eq-comm-tri-post : {A B X : Set} → (f : A → X) → (g : B → X) → (s t : comm-tri-post f g) → Set
Eq-comm-tri-post {A} {B} {X} f g (h , H) (h' , H') = Σ (h ∼ h') (λ K → (x : A) → concat (H x) (ap g (K x)) ≡ H' x)

comm-tri-post-eq : {A B X : Set} → (f : A → X) → (g : B → X) → (s t : comm-tri-post f g) → s ≡ t → Eq-comm-tri-post f g s t
comm-tri-post-eq {A} {B} {X} f g (h , H) (h' , H') refl = rfl-htpy h , λ x → right-unit (H x)

comm-tri-post-eq-is-equiv : {A B X : Set} → (f : A → X) → (g : B → X) → (s t : comm-tri-post f g) → is-equiv (comm-tri-post-eq f g s t)
comm-tri-post-eq-is-equiv {A} {B} {X} f g (h , H) (h' , H') =
  total-contr-to-fam-equiv
    (rfl-htpy h , λ x → right-unit (H x))
    (comm-tri-post-eq f g (h , H))
    refl
    (contr-equiv-to-contr (proj₁ (inv-≃ (comm-tri-post-total-equiv))) (funext-at-to-is-contr-total-htpy h (fun-ext h)) (proj₂ (inv-≃ (comm-tri-post-total-equiv))))
    (h' , H')

  where
    swap-fib : (h' : A → B)
      → Σ (f ∼ g ∘ h') (λ H' → Σ (h ∼ h') (λ K → (x : A) → concat (H x) (ap g (K x)) ≡ H' x))
      ≃ Σ (h ∼ h') (λ K → Σ (f ∼ g ∘ h') (λ H' → (x : A) → concat (H x) (ap g (K x)) ≡ H' x))
    swap-fib h' = Σ-swap (λ H' K → (x : A) → concat (H x) (ap g (K x)) ≡ H' x)

    swap-total : Σ (A → B) (λ h' → Σ (f ∼ g ∘ h') (λ H' → Σ (h ∼ h') (λ K → (x : A) → concat (H x) (ap g (K x)) ≡ H' x)))
               ≃ Σ (A → B) (λ h' → Σ (h ∼ h') (λ K → Σ (f ∼ g ∘ h') (λ H' → (x : A) → concat (H x) (ap g (K x)) ≡ H' x)))
    swap-total = tot (λ h' → proj₁ (swap-fib h')) , fam-equiv-to-tot-equiv (λ h' → proj₁ (swap-fib h')) (λ h' → proj₂ (swap-fib h'))

    Fib : Σ (A → B) (λ h' → h ∼ h') → Set
    Fib (h' , K) = Σ (f ∼ g ∘ h') (λ H' → (x : A) → concat (H x) (ap g (K x)) ≡ H' x)

    fib-contr : (w : Σ (A → B) (λ h' → h ∼ h')) → is-contractible (Fib w)
    fib-contr (h' , K) = funext-at-to-is-contr-total-htpy (λ x → concat (H x) (ap g (K x))) (fun-ext λ x → concat (H x) (ap g (K x)))

    drop-fib : Σ (Σ (A → B) (λ h' → h ∼ h')) Fib ≃ Σ (A → B) (λ h' → h ∼ h')
    drop-fib = proj₁ , fib-contr-to-proj₁-equiv fib-contr

    comm-tri-post-total-equiv : Σ (comm-tri-post f g) (Eq-comm-tri-post f g (h , H)) ≃ Σ (A → B) (λ h' → (h ∼ h'))
    comm-tri-post-total-equiv =
      concat-≃ (Σ-assoc (λ h₁ → triangle-commutes f h₁ g) (Eq-comm-tri-post f g (h , H)))
        (concat-≃ swap-total
          (concat-≃ (inv-≃ (Σ-assoc (λ h' → h ∼ h') Fib)) drop-fib))

-- (c)
comm-tri-pre : {A X Y : Set} → (f : A → X) → (g : A → Y) → Set
comm-tri-pre {A} {X} {Y} f g = Σ (X → Y) (λ h → triangle-commutes g f h)

Eq-comm-tri-pre : {A X Y : Set} → (f : A → X) → (g : A → Y) → (s t : comm-tri-pre f g) → Set
Eq-comm-tri-pre {A} {X} {Y} f g (h , H) (h' , H') = Σ (h ∼ h') (λ K → (x : A) → concat (H x) (K (f x)) ≡ H' x)

comm-tri-pre-eq : {A X Y : Set} → (f : A → X) → (g : A → Y) → (s t : comm-tri-pre f g) → s ≡ t → Eq-comm-tri-pre f g s t
comm-tri-pre-eq {A} {X} {Y} f g (h , H) (h' , H') refl = (λ x → refl) , λ x → right-unit (H x)

comm-tri-pre-eq-is-equiv : {A X Y : Set} → (f : A → X) → (g : A → Y) → (s t : comm-tri-pre f g) → is-equiv (comm-tri-pre-eq f g s t)
comm-tri-pre-eq-is-equiv {A} {X} {Y} f g (h , H) (h' , H') =
  total-contr-to-fam-equiv
    (rfl-htpy h , λ x → right-unit (H x))
    (comm-tri-pre-eq f g (h , H))
    refl
    (contr-equiv-to-contr
      (proj₁ (inv-≃ comm-tri-pre-total-equiv))
      (funext-at-to-is-contr-total-htpy h (fun-ext h))
      (proj₂ (inv-≃ comm-tri-pre-total-equiv)))
    (h' , H')

  where
    swap-fib : (h' : X → Y)
      → Σ (g ∼ h' ∘ f) (λ H' → Σ (h ∼ h') (λ K → (x : A) → concat (H x) (K (f x)) ≡ H' x))
      ≃ Σ (h ∼ h') (λ K → Σ (g ∼ h' ∘ f) (λ H' → (x : A) → concat (H x) (K (f x)) ≡ H' x))
    swap-fib h' = Σ-swap λ z K → (x : A) → concat (H x) (K (f x)) ≡ z x

    swap-total : Σ (X → Y) (λ h' → Σ (g ∼ h' ∘ f) (λ H' → Σ (h ∼ h') (λ K → (x : A) → concat (H x) (K (f x)) ≡ H' x)))
               ≃ Σ (X → Y) (λ h' → Σ (h ∼ h') (λ K → Σ (g ∼ h' ∘ f) (λ H' → (x : A) → concat (H x) (K (f x)) ≡ H' x)))
    swap-total = tot (λ k → proj₁ (swap-fib k)) , fam-equiv-to-tot-equiv (λ k → proj₁ (swap-fib k)) λ k → proj₂ (swap-fib k)

    Fib : Σ (X → Y) (λ h' → h ∼ h') → Set
    Fib (h' , K) = Σ (g ∼ h' ∘ f) (λ H' → (x : A) → concat (H x) (K (f x)) ≡ H' x)

    fib-contr : (w : Σ (X → Y) (λ h' → h ∼ h')) → is-contractible (Fib w)
    fib-contr (h' , K) = funext-at-to-is-contr-total-htpy (λ x → concat (H x) (K (f x))) (fun-ext λ x → concat (H x) (K (f x)))

    drop-fib : Σ (Σ (X → Y) (λ h' → h ∼ h')) Fib ≃ Σ (X → Y) (λ h' → h ∼ h')
    drop-fib = proj₁ , fib-contr-to-proj₁-equiv fib-contr

    comm-tri-pre-total-equiv : Σ (comm-tri-pre f g) (Eq-comm-tri-pre f g (h , H)) ≃ Σ (X → Y) (λ h' → (h ∼ h'))
    comm-tri-pre-total-equiv =
      concat-≃ (Σ-assoc (λ h₁ → triangle-commutes g f h₁) (Eq-comm-tri-pre f g (h , H)))
        (concat-≃ swap-total
          (concat-≃ (inv-≃ (Σ-assoc (λ h' → h ∼ h') Fib)) drop-fib))

-- (d)
comm-sq : {A X B Y : Set} → (f : A → B) → (g : X → Y) → Set
comm-sq {A} {X} {B} {Y} f g = Σ (A → X) (λ i → (Σ (B → Y) (λ j → (square-commutes f i g j))))

Eq-comm-sq : {A X B Y : Set} → (f : A → B) → (g : X → Y) → (s t : comm-sq f g) → Set
Eq-comm-sq {A} {X} {B} {Y} f g (i , (j , H)) (i' , (j' , H')) = Σ (i ∼ i') (λ Ki → (Σ (j ∼ j') (λ Kj → (a : A) → concat (H a) (ap g (Ki a)) ≡ concat (Kj (f a)) (H' a))))

comm-sq-eq : {A X B Y : Set} → (f : A → B) → (g : X → Y) → (s t : comm-sq f g) → s ≡ t → Eq-comm-sq f g s t
comm-sq-eq {A} {X} {B} {Y} f g (i , (j , H)) (i' , (j' , H')) refl = (rfl-htpy i) , ((rfl-htpy j) , λ a → concat (right-unit (H a)) (inv (left-unit (H a))))

comm-sq-eq-is-equiv : {A X B Y : Set} → (f : A → B) → (g : X → Y) → (s t : comm-sq f g) → is-equiv (comm-sq-eq f g s t)
comm-sq-eq-is-equiv {A} {X} {B} {Y} f g (i , (j , H)) (i' , (j' , H')) =
  total-contr-to-fam-equiv
  ((rfl-htpy i) , ((rfl-htpy j) , λ a → concat (right-unit (H a)) (inv (left-unit (H a)))))
  (comm-sq-eq f g (i , (j , H)))
  refl
  (contr-equiv-to-contr
    (proj₁ (inv-≃ comm-sq-total-equiv))
    (funext-at-to-is-contr-total-htpy i (fun-ext i))
    (proj₂ (inv-≃ comm-sq-total-equiv)))
  (i' , (j' , H'))

  where
    assoc-j-fib : (i' : A → X)
      → Σ (Σ (B → Y) (λ j' → square-commutes f i' g j')) (λ w → Eq-comm-sq f g (i , (j , H)) (i' , w))
      ≃ Σ (B → Y) (λ j' → Σ (square-commutes f i' g j') (λ H' → Eq-comm-sq f g (i , (j , H)) (i' , (j' , H'))))
    assoc-j-fib i' = Σ-assoc (square-commutes f i' g) λ w → Eq-comm-sq f g (i , (j , H)) (i' , w)

    assoc-j-total : Σ (A → X) (λ i' → Σ (Σ (B → Y) (λ j' → square-commutes f i' g j')) (λ w → Eq-comm-sq f g (i , (j , H)) (i' , w)))
                  ≃ Σ (A → X) (λ i' → Σ (B → Y) (λ j' → Σ (square-commutes f i' g j') (λ H' → Eq-comm-sq f g (i , (j , H)) (i' , (j' , H')))))
    assoc-j-total = tot (λ k → proj₁ (assoc-j-fib k)) , fam-equiv-to-tot-equiv (λ k → proj₁ (assoc-j-fib k)) λ k → proj₂ (assoc-j-fib k)

    swap-H-fib : (i' : A → X) → (j' : B → Y)
      → Σ (square-commutes f i' g j') (λ H' →
          Σ (i ∼ i') (λ Ki → Σ (j ∼ j') (λ Kj →
            (a : A) → concat (H a) (ap g (Ki a)) ≡ concat (Kj (f a)) (H' a))))
      ≃ Σ (i ∼ i') (λ _ → (j ∼ j'))
    swap-H-fib i' j' = concat-≃ swapA (concat-≃ swapB-total (concat-≃ (inv-≃ (Σ-assoc (λ _ → j ∼ j') FibH')) dropH))
      where
        swapA : Σ (square-commutes f i' g j') (λ H' → Σ (i ∼ i') (λ Ki → Σ (j ∼ j') (λ Kj →
                  (a : A) → concat (H a) (ap g (Ki a)) ≡ concat (Kj (f a)) (H' a))))
              ≃ Σ (i ∼ i') (λ Ki → Σ (square-commutes f i' g j') (λ H' → Σ (j ∼ j') (λ Kj →
                  (a : A) → concat (H a) (ap g (Ki a)) ≡ concat (Kj (f a)) (H' a))))
        swapA = Σ-swap (λ H' Ki → Σ (j ∼ j') (λ Kj → (a : A) → concat (H a) (ap g (Ki a)) ≡ concat (Kj (f a)) (H' a)))

        swapB : (Ki : i ∼ i') → Σ (square-commutes f i' g j') (λ H' → Σ (j ∼ j') (λ Kj →
                  (a : A) → concat (H a) (ap g (Ki a)) ≡ concat (Kj (f a)) (H' a)))
              ≃ Σ (j ∼ j') (λ Kj → Σ (square-commutes f i' g j') (λ H' →
                  (a : A) → concat (H a) (ap g (Ki a)) ≡ concat (Kj (f a)) (H' a)))
        swapB Ki = Σ-swap (λ H' Kj → (a : A) → concat (H a) (ap g (Ki a)) ≡ concat (Kj (f a)) (H' a))

        swapB-total : Σ (i ∼ i') (λ Ki → Σ (square-commutes f i' g j') (λ H' → Σ (j ∼ j') (λ Kj →
                        (a : A) → concat (H a) (ap g (Ki a)) ≡ concat (Kj (f a)) (H' a))))
                    ≃ Σ (i ∼ i') (λ Ki → Σ (j ∼ j') (λ Kj → Σ (square-commutes f i' g j') (λ H' →
                        (a : A) → concat (H a) (ap g (Ki a)) ≡ concat (Kj (f a)) (H' a))))
        swapB-total = tot (λ Ki → proj₁ (swapB Ki)) , fam-equiv-to-tot-equiv (λ Ki → proj₁ (swapB Ki)) (λ Ki → proj₂ (swapB Ki))

        FibH' : Σ (i ∼ i') (λ _ → j ∼ j') → Set
        FibH' (Ki , Kj) = Σ (square-commutes f i' g j') (λ H' →
          (a : A) → concat (H a) (ap g (Ki a)) ≡ concat (Kj (f a)) (H' a))

        fib-contr-H' : (w : Σ (i ∼ i') (λ _ → j ∼ j')) → is-contractible (FibH' w)
        fib-contr-H' (Ki , Kj) =
          contr-equiv-to-contr
            (proj₁ Π-distrib-Σ)
            (fam-trunc-to-Π-trunc (λ a →
              contr-equiv-to-contr
                (tot (λ y → inv))
                (equiv-to-contr-map (concat (Kj (f a))) (is-equiv-concat (Kj (f a))) (concat (H a) (ap g (Ki a))))
                (fam-equiv-to-tot-equiv (λ y → inv) (λ y → is-equiv-inv (concat (Kj (f a)) y) (concat (H a) (ap g (Ki a)))))))
            (proj₂ Π-distrib-Σ)

        dropH : Σ (Σ (i ∼ i') (λ _ → j ∼ j')) FibH' ≃ Σ (i ∼ i') (λ _ → j ∼ j')
        dropH = proj₁ , fib-contr-to-proj₁-equiv fib-contr-H'

    swap-H-total : Σ (A → X) (λ i' → Σ (B → Y) (λ j' → Σ (square-commutes f i' g j') (λ H' →
                     Σ (i ∼ i') (λ Ki → Σ (j ∼ j') (λ Kj →
                       (a : A) → concat (H a) (ap g (Ki a)) ≡ concat (Kj (f a)) (H' a))))))
                 ≃ Σ (A → X) (λ i' → Σ (B → Y) (λ j' → Σ (i ∼ i') (λ _ → (j ∼ j'))))
    swap-H-total = tot (λ i' → proj₁ (lift-j i')) , fam-equiv-to-tot-equiv (λ i' → proj₁ (lift-j i')) (λ i' → proj₂ (lift-j i'))
      where
        lift-j : (i' : A → X) → Σ (B → Y) (λ j' → Σ (square-commutes f i' g j') (λ H' →
                   Σ (i ∼ i') (λ Ki → Σ (j ∼ j') (λ Kj →
                     (a : A) → concat (H a) (ap g (Ki a)) ≡ concat (Kj (f a)) (H' a)))))
                ≃ Σ (B → Y) (λ j' → Σ (i ∼ i') (λ _ → (j ∼ j')))
        lift-j i' = tot (λ j' → proj₁ (swap-H-fib i' j')) , fam-equiv-to-tot-equiv (λ j' → proj₁ (swap-H-fib i' j')) (λ j' → proj₂ (swap-H-fib i' j'))

    swap-j-fib : (i' : A → X)
      → Σ (B → Y) (λ j' → Σ (i ∼ i') (λ _ → j ∼ j'))
      ≃ Σ (i ∼ i') (λ _ → Σ (B → Y) (λ j' → j ∼ j'))
    swap-j-fib i' = Σ-swap (λ j' _ → j ∼ j')

    swap-j-total : Σ (A → X) (λ i' → Σ (B → Y) (λ j' → Σ (i ∼ i') (λ _ → j ∼ j')))
                 ≃ Σ (A → X) (λ i' → Σ (i ∼ i') (λ _ → Σ (B → Y) (λ j' → j ∼ j')))
    swap-j-total = tot (λ i' → proj₁ (swap-j-fib i')) , fam-equiv-to-tot-equiv (λ i' → proj₁ (swap-j-fib i')) (λ i' → proj₂ (swap-j-fib i'))

    FibJ : Σ (A → X) (λ i' → i ∼ i') → Set
    FibJ (i' , Ki) = Σ (B → Y) (λ j' → j ∼ j')

    fib-contr-J : (w : Σ (A → X) (λ i' → i ∼ i')) → is-contractible (FibJ w)
    fib-contr-J (i' , Ki) = funext-at-to-is-contr-total-htpy j (fun-ext j)

    drop-J : Σ (Σ (A → X) (λ i' → i ∼ i')) FibJ ≃ Σ (A → X) (λ i' → i ∼ i')
    drop-J = proj₁ , fib-contr-to-proj₁-equiv fib-contr-J

    comm-sq-total-equiv : Σ (comm-sq f g) (Eq-comm-sq f g (i , (j , H))) ≃ Σ (A → X) (λ i' → i ∼ i')
    comm-sq-total-equiv =
      concat-≃ (Σ-assoc (λ i' → Σ (B → Y) (λ j' → square-commutes f i' g j')) (Eq-comm-sq f g (i , (j , H))))
        (concat-≃ assoc-j-total
          (concat-≃ swap-H-total
            (concat-≃ swap-j-total
              (concat-≃ (inv-≃ (Σ-assoc (λ i' → i ∼ i') FibJ)) drop-J))))

-- 13.3
-- (a)
contr-is-prop : (A : Set) → is-prop (is-contr A)
contr-is-prop A c c' = fam-trunc-to-Σ-trunc (type-is-succ-type c) (λ x → fam-trunc-to-Π-trunc λ a → type-is-succ-type (type-is-succ-type c a x)) c c'

-- (b)
trunc-is-prop : (A : Set) → {k : 𝕋} → is-prop (is-trunc k A)
trunc-is-prop A { -2𝕋} = contr-is-prop A
trunc-is-prop A {succ𝕋 k} p q =
  equiv-to-same-k-type
    (htpy-eq p q , fun-ext p q)
    (fam-trunc-to-Π-trunc {k = -2𝕋} (λ x →
      equiv-to-same-k-type
        (htpy-eq (p x) (q x) , fun-ext (p x) (q x))
        (fam-trunc-to-Π-trunc {k = -2𝕋} (λ y →
          trunc-is-prop (x ≡ y) {k} (p x y) (q x y)))))

-- 13.4
-- (a)
equiv-to-contr-sec : {A B : Set} → (f : A → B) → is-equiv f → is-contr (sec f)
equiv-to-contr-sec f e =
  contr-equiv-to-contr
    (proj₁ (Π-fib-equiv-sec f))
    (fam-trunc-to-Π-trunc (equiv-to-contr-map f e))
    (proj₂ (Π-fib-equiv-sec f))

-- (b)
equiv-to-contr-retr : {A B : Set} → (f : A → B) → is-equiv f → is-contr (retr f)
equiv-to-contr-retr {A} {B} f e =
  contr-equiv-to-contr
    (tot (λ h → htpy-eq (h ∘ f) id))
    (equiv-to-contr-map (precomp f A) pfA-equiv id)
    (fam-equiv-to-tot-equiv (λ h → htpy-eq (h ∘ f) id) (λ h → fun-ext (h ∘ f) id))
  where
    pfA-equiv : is-equiv (precomp f A)
    pfA-equiv = precomp-Π-is-equiv-to-precomp-is-equiv f (is-equiv-to-precomp-Π-is-equiv f e) A

-- (c)
equiv-is-prop : {A B : Set} → (f : A → B) → is-prop (is-equiv f)
equiv-is-prop f fequiv fequiv' = type-is-succ-type (contr-to-prod-contr (equiv-to-contr-sec f fequiv) (equiv-to-contr-retr f fequiv)) fequiv fequiv'

-- (d)
≃-htpy-eq : {A B : Set} → (e e' : A ≃ B) → e ≡ e' → proj₁ e ∼ proj₁ e'
≃-htpy-eq (e , eequiv) (e' , eequiv') refl = rfl-htpy e

≃-htpy-eq-is-equiv : {A B : Set} → (e e' : A ≃ B) → is-equiv (≃-htpy-eq e e')
≃-htpy-eq-is-equiv {A} {B} e e' =
  htpy-of-equiv-is-equiv
    (htpy-eq (proj₁ e) (proj₁ e') ∘ ap proj₁)
    (≃-htpy-eq e e')
    (homotopy e e')
    (equiv-comp (ap proj₁) (htpy-eq (proj₁ e) (proj₁ e')) (embproj₁ e e') (fun-ext (proj₁ e) (proj₁ e')))
  where
    embproj₁ : is-emb (proj₁ {A = A → B} {B = is-equiv})
    embproj₁ = proj₁-of-subtype-is-emb is-equiv equiv-is-prop

    homotopy : (w w' : A ≃ B) → (p : w ≡ w') → htpy-eq (proj₁ w) (proj₁ w') (ap proj₁ p) ≡ ≃-htpy-eq w w' p
    homotopy (f , fe) .(f , fe) refl = refl

-- (e)
type-to-≃-type : {A B : Set} → {k : 𝕋} → is-trunc k A → is-trunc k B → is-trunc k (A ≃ B)
type-to-≃-type {A} {B} { -2𝕋} Atrunc Btrunc =
  fam-trunc-to-Σ-trunc ABcontr (λ h → tr (λ z → is-contr (is-equiv z)) (inv (proj₂ ABcontr h)) f0contr)
  where
    ABcontr : is-contractible (A → B)
    ABcontr = codom-trunc-to-→-trunc Btrunc

    f0contr : is-contr (is-equiv (proj₁ ABcontr))
    f0contr = is-prop'-to-inhab-contr (is-prop-to-is-prop' (equiv-is-prop (proj₁ ABcontr))) (contr-contr-to-equiv (proj₁ ABcontr) Atrunc Btrunc)
type-to-≃-type {A} {B} {succ𝕋 k} Atrunc Btrunc e e' =
  equiv-to-same-k-type
    (≃-htpy-eq e e' , ≃-htpy-eq-is-equiv e e')
    (fam-trunc-to-Π-trunc (λ x → Btrunc (proj₁ e x) (proj₁ e' x)))

-- 13.5
path-split-is-prop : {A B : Set} → (f : A → B) → is-prop (is-path-split f)
path-split-is-prop {A} f x y =
  type-is-succ-type (contr-to-prod-contr sec-f-contr sec-ap-f-contr) x y
  where
    f-equiv : is-equiv f
    f-equiv = path-split-to-equiv f x

    sec-f-contr : is-contr (sec f)
    sec-f-contr = equiv-to-contr-sec f f-equiv

    sec-ap-f-contr : is-contr ((a b : A) → sec (ap f {a} {b}))
    sec-ap-f-contr =
      fam-trunc-to-Π-trunc (λ a →
        fam-trunc-to-Π-trunc (λ b →
          equiv-to-contr-sec (ap f {a} {b}) (equiv-to-emb f f-equiv a b)))

coh-inv-is-prop : {A B : Set} → (f : A → B) → is-prop (is-coh-inv f)
coh-inv-is-prop {A} {B} f c₁ c₂ =
  type-is-succ-type coh-inv-contr c₁ c₂
  where
    f-equiv : is-equiv f
    f-equiv = contr-map-to-equiv f (coh-inv-to-contr-fib f c₁)

    -- The coherence data attached to a fixed section (g , G) of f
    inner : sec f → Set
    inner (g , G) = Σ (g ∘ f ∼ id) (λ H → (a : A) → G (f a) ≡ ap f (H a))

    inner-contr : (w : sec f) → is-contr (inner w)
    inner-contr (g , G) =
      contr-equiv-to-contr
        (choice {A} {λ a → g (f a) ≡ a} {λ a p → G (f a) ≡ ap f p})
        ΠΣ-contr
        (choice-equiv {A} {λ a → g (f a) ≡ a} {λ a p → G (f a) ≡ ap f p})
      where
        -- For each a, the fibre Σ (p : g(f a) ≡ a) (G(f a) ≡ ap f p) is
        -- contractible, since it is (up to inv) a fibre of the equivalence ap f
        fibre-contr : (a : A) → is-contr (Σ (g (f a) ≡ a) (λ p → G (f a) ≡ ap f p))
        fibre-contr a =
          contr-equiv-to-contr
            (tot (λ p → inv))
            (equiv-to-contr-map (ap f {g (f a)} {a}) (equiv-to-emb f f-equiv (g (f a)) a) (G (f a)))
            (fam-equiv-to-tot-equiv (λ p → inv) (λ p → is-equiv-inv (ap f {g (f a)} {a} p) (G (f a))))

        ΠΣ-contr : is-contr ((a : A) → Σ (g (f a) ≡ a) (λ p → G (f a) ≡ ap f p))
        ΠΣ-contr = fam-trunc-to-Π-trunc fibre-contr

    -- is-coh-inv f ≃ Σ (sec f) inner, with contractible base and fibres
    coh-assoc : Σ (sec f) inner ≃ is-coh-inv f
    coh-assoc = Σ-assoc (λ g → f ∘ g ∼ id) inner

    coh-inv-contr : is-contr (is-coh-inv f)
    coh-inv-contr =
      contr-equiv-to-contr
        (proj₁ coh-assoc)
        (fam-trunc-to-Σ-trunc {k = -2𝕋} (equiv-to-contr-sec f f-equiv) inner-contr)
        (proj₂ coh-assoc)

-- 13.5 (a) conclusion: the three notions of invertibility agree as propositions
coh-inv-to-equiv : {A B : Set} → (f : A → B) → is-coh-inv f → is-equiv f
coh-inv-to-equiv f c = contr-map-to-equiv f (coh-inv-to-contr-fib f c)

equiv-to-coh-inv : {A B : Set} → (f : A → B) → is-equiv f → is-coh-inv f
equiv-to-coh-inv f e = inv-to-coh-inv f (equiv-to-inverse f e)

equiv-iff-path-split : {A B : Set} → (f : A → B) → is-equiv f ↔ is-path-split f
equiv-iff-path-split f = equiv-to-path-split f , path-split-to-equiv f

equiv-iff-coh-inv : {A B : Set} → (f : A → B) → is-equiv f ↔ is-coh-inv f
equiv-iff-coh-inv f = equiv-to-coh-inv f , coh-inv-to-equiv f

equiv-≃-path-split : {A B : Set} → (f : A → B) → is-equiv f ≃ is-path-split f
equiv-≃-path-split f = iff-to-≃ (equiv-is-prop f) (path-split-is-prop f) (equiv-iff-path-split f)

equiv-≃-coh-inv : {A B : Set} → (f : A → B) → is-equiv f ≃ is-coh-inv f
equiv-≃-coh-inv f = iff-to-≃ (equiv-is-prop f) (coh-inv-is-prop f) (equiv-iff-coh-inv f)

path-split-≃-coh-inv : {A B : Set} → (f : A → B) → is-path-split f ≃ is-coh-inv f
path-split-≃-coh-inv f =
  iff-to-≃ (path-split-is-prop f) (coh-inv-is-prop f)
    ((λ ps → equiv-to-coh-inv f (path-split-to-equiv f ps))
     , (λ c → equiv-to-path-split f (coh-inv-to-equiv f c)))

-- (b)
has-inv-id-≃-id-rfl-htpy : {A : Set} → has-inverse (id {A}) ≃ (id {A}) ∼ (id {A})
has-inv-id-≃-id-rfl-htpy {A} =
  concat-≃
    (inv-≃ (Σ-assoc {A → A} (λ g → g ∼ id) (λ w → proj₁ w ∼ id)))
    (inv-≃ pair-map)
  where
    -- Σ (A→A) (λ g → g∼id) is contractible with centre (id , rfl-htpy id),
    -- so pairing with the centre collapses it onto the fibre id ∼ id
    pair-map : ((id {A}) ∼ id) ≃ Σ (Σ (A → A) (λ g → g ∼ id)) (λ w → proj₁ w ∼ id)
    pair-map =
      (λ y → proj₁ (total-htpy-is-contr A) , y)
      , is-equiv-pair-contr-base (total-htpy-is-contr A) (λ w → proj₁ w ∼ id)

-- 13.6

-- (ii)
empty-dep-up : (A : Set) → Set₁
empty-dep-up A = (P : A → Set) → is-contr ((x : A) → P x)

-- (iii)
empty-up : (A : Set) → Set₁
empty-up A = (X : Set) → is-contr (A → X)

-- (i) → (ii)
empty-to-dep-up : {A : Set} → ¬ A → empty-dep-up A
empty-to-dep-up nA B = (λ a → ex-falso (nA a)) , λ aBa → eq-htpy _ _ λ a → ex-falso (nA a)

-- (ii) → (iii)
dep-up-to-up : {A : Set} → empty-dep-up A → empty-up A
dep-up-to-up dupA B = dupA λ a → B

-- (iii) → (i)
up-to-empty : {A : Set} → empty-up A → ¬ A
up-to-empty upA = proj₁ (upA 𝟘)

-- 13.7
-- (i) is just is-contr A

-- (ii) dependent universal property: ev at a is an equivalence Π P → P a
contr-dep-up : (A : Set) → Set₁
contr-dep-up A = Σ A (λ a → (P : A → Set) → is-equiv (λ (f : (x : A) → P x) → f a))

-- (iii) universal property: ev at a is an equivalence (A → X) → X
contr-up : (A : Set) → Set₁
contr-up A = Σ A (λ a → (X : Set) → is-equiv (λ (f : A → X) → f a))

-- (iv)
contr-up-endo : (A : Set) → Set
contr-up-endo A = Σ A (λ a → is-equiv (λ (f : A → A) → f a))

-- (v) const is an equivalence X → (A → X)
const-up : (A : Set) → Set₁
const-up A = (X : Set) → is-equiv (λ (x : X) → λ (y : A) → x)

-- (vi)
const-up-endo : (A : Set) → Set
const-up-endo A = is-equiv (λ (x : A) → λ (y : A) → x)

-- (i) → (ii)
contr-to-dep-up : {A : Set} → is-contr A → contr-dep-up A
contr-to-dep-up (a , xeqa) = a , λ P → ((λ pa x → tr P (concat (xeqa a) (inv (xeqa x))) pa) , λ pa → ap (λ p → tr P p pa) (right-inv (xeqa a))) ,
  ((λ pa x → tr P (concat (xeqa a) (inv (xeqa x))) pa) , λ pa → eq-htpy _ _ λ x → apd pa (concat (xeqa a) (inv (xeqa x))))

-- (ii) → (iii)
contr-dep-up-to-up : {A : Set} → contr-dep-up A → contr-up A
contr-dep-up-to-up dupA = proj₁ dupA , λ X → proj₂ dupA (λ _ → X)

-- (iii) → (v)
contr-up-to-const-up : {A : Set} → contr-up A → const-up A
contr-up-to-const-up Acontrup X = 3-for-2-f-g-to-h (λ z → z) (λ f → f (proj₁ Acontrup)) (λ v v₁ → v) (λ x → refl) (((λ z → z) , (λ x → refl)) , ((λ z → z) , (λ x → refl))) (proj₂ Acontrup X)

-- (v) → (vi)
const-up-to-const-up-endo : {A : Set} → const-up A → const-up-endo A
const-up-to-const-up-endo {A} Aconstup = Aconstup A

-- (vi) → (iv)
const-up-endo-to-up-endo : {A : Set} → const-up-endo A → contr-up-endo A
const-up-endo-to-up-endo Aconstupendo = proj₁ (proj₁ Aconstupendo) id , 3-for-2-f-h-to-g id (λ z → z (proj₁ (proj₁ Aconstupendo) id)) (λ z z₁ → z) (λ x → refl) (((λ z → z) , (λ x → refl)) , ((λ z → z) , (λ x → refl))) Aconstupendo

-- (iv) → (i)
up-endo-to-contr : {A : Set} → contr-up-endo A → is-contr A
up-endo-to-contr (x , ((g , fg) , (h , fh))) = x , λ a → ap (λ f → f a) (concat (inv (fh id)) (fh (λ _ → x)))

-- 13.8

-- the map f ↦ (f ∘ inl , f ∘ inr) on dependent functions
dep-ev-⊎ : {A B : Set} → (P : A ⊎ B → Set) →
           ((z : A ⊎ B) → P z) → (((x : A) → P (inl x)) × ((y : B) → P (inr y)))
dep-ev-⊎ P f = (λ x → f (inl x)) , (λ y → f (inr y))

-- dependent universal property of the coproduct
⊎-dep-up : {A B : Set} → (P : A ⊎ B → Set) → is-equiv (dep-ev-⊎ P)
⊎-dep-up P = ((λ {(x , y) (inl z) → x z
                ; (x , y) (inr z) → y z}) , λ {(x , y) → refl}) , ((λ {(x , y) (inl z) → x z
                                                                     ; (x , y) (inr z) → y z}) , λ {f → eq-htpy _ _ λ {(inl x) → refl
                                                                                                                     ; (inr x) → refl}})

-- the non-dependent evaluation map
ev-⊎ : (A B X : Set) → (A ⊎ B → X) → ((A → X) × (B → X))
ev-⊎ A B X f = (f ∘ inl) , (f ∘ inr)

-- universal property of the coproduct
⊎-up : (A B X : Set) → is-equiv (ev-⊎ A B X)
⊎-up A B X = ⊎-dep-up λ _ → X

-- 13.9

-- evaluation of a dependent function at the base point (a , b)
ev-pt-fam : {A : Set} → (B : A → Set) → (a : A) → (b : B a) → (C : A → Set)
  → ((x : A) → B x → C x) → C a
ev-pt-fam B a b C h = h a b

-- (i) ev at b is an equivalence for every family C over A
pt-fam-up : {A : Set} → (B : A → Set) → (a : A) → (b : B a) → Set₁
pt-fam-up {A} B a b = (C : A → Set) → is-equiv (ev-pt-fam B a b C)

-- the canonical map out of the identity type, sending refl to b
≡-to-fam : {A : Set} → (B : A → Set) → (a : A) → (b : B a) → (x : A) → (a ≡ x) → B x
≡-to-fam B a b .a refl = b

-- (ii) that canonical map is a family of equivalences
pt-fam-fam-equiv : {A : Set} → (B : A → Set) → (a : A) → (b : B a) → Set
pt-fam-fam-equiv {A} B a b = (x : A) → is-equiv (≡-to-fam B a b x)

-- (i) → (ii)
pt-fam-up-to-fam-equiv : {A : Set} → (B : A → Set) → (a : A) → (b : B a)
  → pt-fam-up B a b → pt-fam-fam-equiv B a b
pt-fam-up-to-fam-equiv {A} B a b up x = (f x , sect x) , (f x , ret x)
  where
    f : (z : A) → B z → a ≡ z
    f = proj₁ (proj₁ (up (_≡_ a))) refl

    -- f sends b to refl
    fab : f a b ≡ refl
    fab = proj₂ (proj₁ (up (_≡_ a))) refl

    -- the round-trip ≡-to-fam ∘ f as a fibrewise map B → B; it agrees with the
    -- identity at b, hence with it everywhere, since ev at C := B is injective
    k : (z : A) → B z → B z
    k z y = ≡-to-fam B a b z (f z y)

    k≡id : k ≡ (λ z y → y)
    k≡id = concat (inv (proj₂ (proj₂ (up B)) k))
      (concat (ap (proj₁ (proj₂ (up B))) (ap (≡-to-fam B a b a) fab))
        (proj₂ (proj₂ (up B)) (λ z y → y)))

    sect : (z : A) → (y : B z) → ≡-to-fam B a b z (f z y) ≡ y
    sect z y = htpy-eq _ _ (htpy-eq _ _ k≡id z) y

    ret : (z : A) → (p : a ≡ z) → f z (≡-to-fam B a b z p) ≡ p
    ret .a refl = fab
-- (ii) → (i)
fam-equiv-to-pt-fam-up : {A : Set} → (B : A → Set) → (a : A) → (b : B a)
  → pt-fam-fam-equiv B a b → pt-fam-up B a b
fam-equiv-to-pt-fam-up {A} B a b fequiv C = (ext , ext-htpy) , (ext , λ h → eq-htpy _ _ λ z → eq-htpy _ _ (ext-unique h z))
  where
    -- a fibrewise equivalence out of the identity type has contractible total
    -- space, and a contractible total space is an identity system
    ΣAB-contr : is-contractible (Σ A B)
    ΣAB-contr = fam-equiv-to-total-contr b (≡-to-fam B a b) refl fequiv

    id-sys : is-id-sys B a b
    id-sys P = total-contr-to-id-sys b (≡-to-fam B a b) refl ΣAB-contr P

    -- singleton induction for B at (a , b), instantiated at the family λ z _ → C z:
    -- elimination, computation, and uniqueness for fibrewise maps out of B
    ext : C a → (z : A) → B z → C z
    ext = proj₁ (id-sys (λ z _ → C z))

    ext-htpy : (c : C a) → ext c a b ≡ c
    ext-htpy = proj₂ (id-sys (λ z _ → C z))

    ext-unique : (h : (z : A) → B z → C z) → (z : A) → (y : B z) → ext (h a b) z y ≡ h z y
    ext-unique h = proj₁ (id-sys (λ z y → ext (h a b) z y ≡ h z y)) (ext-htpy (h a b))

-- transport in a family of functions with constant domain acts pointwise
tr-Π : {A I : Set} → (D : A → I → Set) → {u v : A} → (p : u ≡ v) → (g : (i : I) → D u i) → (i : I)
  → tr (λ z → (j : I) → D z j) p g i ≡ tr (λ z → D z i) p (g i)
tr-Π D refl g i = refl

-- transport in a family of identifications whose two sides both vary
tr-≡-fun : {A B : Set} → (u v : A → B) → {g g' : A} → (p : g ≡ g') → (q : u g ≡ v g)
  → tr (λ z → u z ≡ v z) p q ≡ concat (inv (ap u p)) (concat q (ap v p))
tr-≡-fun u v refl q = inv (concat (left-unit (concat q refl)) (right-unit q))

-- 13.10
ℕ-up : {X : Set} → (x : X) → (f : X → X) → is-contr (Σ (ℕ → X) (λ h → (h 0ℕ ≡ x) × (h ∘ succℕ ∼ f ∘ h)))
ℕ-up {X} x f = ((indℕ x λ _ → f) , (refl , λ n → refl)) , contraction
  where
  contraction : (x₁ : Σ (ℕ → X) (λ h → h 0ℕ ≡ x × (h ∘ succℕ ∼ f ∘ h))) → x₁ ≡ (indℕ x (λ _ → f) , (refl , (λ n → refl)))
  contraction (h , (h0 , hsfh)) =
    eq-pair _ _ (P , concat (tr-× base step P (h0 , hsfh)) (eq-pair× (concat (tr-fib (λ z → z 0ℕ) P h0) (concat (ap (λ w → concat (inv w) h0) (K≡ 0ℕ)) (left-inv _))) (eq-htpy _ _ λ n →
        concat (tr-Π (λ k m → k (succℕ m) ≡ f (k m)) P hsfh n)
          (concat (tr-≡-fun (λ k → k (succℕ n)) (λ k → f (k n)) P (hsfh n))
            (concat (ap (λ w → concat (inv w) (concat (hsfh n) (ap (λ k → f (k n)) P))) (K≡ (succℕ n)))
              (concat (ap (λ w → concat (inv (K (succℕ n))) (concat (hsfh n) w))
                          (concat (inv (ap-comp (λ j → j n) f P)) (ap (ap f) (K≡ n))))
                (left-inv (K (succℕ n)))))))))
    where
    K : (m : ℕ) → h m ≡ indℕ x (λ _ → f) m
    K 0ℕ = h0
    K (succℕ m) = concat (hsfh m) (ap f (K m))

    base : (ℕ → X) → Set
    base k = k 0ℕ ≡ x

    step : (ℕ → X) → Set
    step k = k ∘ succℕ ∼ f ∘ k

    P : h ≡ indℕ x (λ _ → f)
    P = eq-htpy _ _ K

    -- ap-at-a-point and htpy-eq agree, so K is recoverable from P by funext's round trip
    ap-eval : {g g' : ℕ → X} → (Q : g ≡ g') → (n : ℕ) → ap (λ j → j n) Q ≡ htpy-eq g g' Q n
    ap-eval refl n = refl

    K≡ : (n : ℕ) → ap (λ j → j n) P ≡ K n
    K≡ n = concat (ap-eval P n) (htpy-eq _ _ (htpy-eq-eq-htpy h (indℕ x (λ _ → f)) K) n)

-- 13.11
-- for ordinal induction on ℕ
belowℕ : (P : ℕ → Set) → ℕ → Set
belowℕ P n = (m : ℕ) → m <ℕ n → P m

below-zeroℕ : (P : ℕ → Set) → belowℕ P 0ℕ
below-zeroℕ P 0ℕ m<0 = ex-falso m<0
below-zeroℕ P (succℕ m) m<0 = ex-falso m<0

below-succℕ : (P : ℕ → Set) → (h : (k : ℕ) → belowℕ P k → P k)
  → (k : ℕ) → belowℕ P k → belowℕ P (succℕ k)
below-succℕ P h k q m m<sk with <-succ-to-<-or-≡ℕ m k m<sk
... | inl m<k = q m m<k
... | inr refl = h k q

below-allℕ : (P : ℕ → Set) → (h : (k : ℕ) → belowℕ P k → P k) → (n : ℕ) → belowℕ P n
below-allℕ P h = indℕ {belowℕ P} (below-zeroℕ P) (below-succℕ P h)

ord-indℕ : {P : ℕ → Set} → (((k : ℕ) → ((m : ℕ) → (m <ℕ k) → P m) → P k) → ((n : ℕ) → P n))
ord-indℕ {P} f n = f n (below-allℕ P f n)

-- below-allℕ agrees pointwise with the values ord-indℕ assigns
below-all-compℕ : (P : ℕ → Set) → (h : (k : ℕ) → belowℕ P k → P k)
  → (n m : ℕ) → (m<n : m <ℕ n) → below-allℕ P h n m m<n ≡ h m (below-allℕ P h m)
below-all-compℕ P h 0ℕ m m<n = ex-falso (<-zeroℕ m m<n)
below-all-compℕ P h (succℕ k) m m<sk with <-succ-to-<-or-≡ℕ m k m<sk
... | inl m<k = below-all-compℕ P h k m m<k
... | inr refl = refl

ord-ind-compℕ : {P : ℕ → Set}
  → (h : (k : ℕ) → ((m : ℕ) → (m <ℕ k) → P m) → P k) → (n : ℕ)
  → ord-indℕ h n ≡ h n (λ m _ → ord-indℕ h m)
ord-ind-compℕ h n = ap (h n) (eq-htpy _ _ λ m → eq-htpy _ _ λ m<n → below-all-compℕ _ h n m m<n)

-- 13.12
map-Π : {I : Set} → (A B : I → Set) → (f : (i : I) → A i → B i) → ((i : I) → A i) → ((i : I) → B i)
map-Π A B f fa i = f i (fa i)

-- the fibres of map-Π are the Π of the fibres
fib-map-Π-equiv-Π-fib : {I : Set} → (A B : I → Set) → (f : (i : I) → A i → B i) → (b : (i : I) → B i)
  → fib (map-Π A B f) b ≃ ((i : I) → fib (f i) (b i))
fib-map-Π-equiv-Π-fib {I} A B f b =
  concat-≃ (tot htpy , fam-equiv-to-tot-equiv htpy (λ g → fun-ext _ _)) (inv-≃ Π-distrib-Σ)
  where
  htpy : (g : (i : I) → A i) → (map-Π A B f g ≡ b) → ((i : I) → f i (g i) ≡ b i)
  htpy g p = htpy-eq _ _ p

trunc-map-Π : {I : Set} → {k : 𝕋} → (A B : I → Set) → (f : (i : I) → A i → B i) → ((i : I) → is-trunc-map k (f i)) → is-trunc-map k (map-Π A B f)
trunc-map-Π A B f ftrunc iBi = equiv-to-same-k-type (fib-map-Π-equiv-Π-fib A B f iBi) (fam-trunc-to-Π-trunc λ i → ftrunc i (iBi i))

-- a fibrewise equivalence induces an equivalence on Π-types
fam-equiv-to-Π-equiv : {I : Set} → (A B : I → Set) → (f : (i : I) → A i → B i)
  → is-equiv-fam f → is-equiv (map-Π A B f)
fam-equiv-to-Π-equiv {I} A B f fequiv = contr-map-to-equiv (map-Π A B f) (trunc-map-Π A B f λ i → equiv-to-contr-map (f i) (fequiv i))


-- (b) transporting a fibrewise equivalence along an equivalence of index types
map-Π-≃ : {I J : Set} → (e : I ≃ J) → (A : I → Set) → (B : J → Set)
  → ((i : I) → A i → B (proj₁ e i))
  → ((i : I) → A i) → ((j : J) → B j)
map-Π-≃ e A B f =
  proj₁ (proj₁ (is-equiv-to-precomp-Π-is-equiv (proj₁ e) (proj₂ e) B))
    ∘ map-Π A (λ i → B (proj₁ e i)) f

equiv-map-Π-≃ : {I J : Set} → (e : I ≃ J) → (A : I → Set) → (B : J → Set)
  → (f : (i : I) → A i → B (proj₁ e i)) → is-equiv-fam f
  → is-equiv (map-Π-≃ e A B f)
equiv-map-Π-≃ e A B f fequiv = equiv-comp (map-Π A (λ i → B (proj₁ e i)) f) (proj₁ (proj₁ pre))
  (contr-map-to-equiv (map-Π A (λ i → B (proj₁ e i)) f)
    (trunc-map-Π {k = -2𝕋} A (λ i → B (proj₁ e i)) f (λ i → equiv-to-contr-map (f i) (fequiv i))))
  (sec-map-is-equiv (precomp-Π (proj₁ e) B) pre)
  where
  pre : is-equiv (precomp-Π (proj₁ e) B)
  pre = is-equiv-to-precomp-Π-is-equiv (proj₁ e) (proj₂ e) B

-- (c) each f i is k-truncated  iff  every reindexing of map-Π along α : X → I is k-truncated
-- (stated as two implications: quantifying over (X : Set) puts these in Set₁, so ↔ does not fit)
fam-trunc-map-to-trunc-map-Π : {I : Set} → {k : 𝕋} → (A B : I → Set) → (f : (i : I) → A i → B i)
  → ((i : I) → is-trunc-map k (f i))
  → (X : Set) → (α : X → I)
  → is-trunc-map k (map-Π (λ x → A (α x)) (λ x → B (α x)) (λ x → f (α x)))
fam-trunc-map-to-trunc-map-Π A B f ftrunc X α = trunc-map-Π (λ z → A (α z)) (λ z → B (α z)) (λ i → f (α i)) λ i → ftrunc (α i)

trunc-map-Π-to-fam-trunc-map : {I : Set} → {k : 𝕋} → (A B : I → Set) → (f : (i : I) → A i → B i)
  → ((X : Set) → (α : X → I)
     → is-trunc-map k (map-Π (λ x → A (α x)) (λ x → B (α x)) (λ x → f (α x))))
  → (i : I) → is-trunc-map k (f i)
trunc-map-Π-to-fam-trunc-map A B f H i b = equiv-to-same-k-type (concat-≃ (inv-≃ (Π-𝟙 λ _ → fib (f i) b)) (inv-≃ (fib-map-Π-equiv-Π-fib (λ _ → A i) (λ _ → B i) (λ i₁ → f i) λ i₁ → b))) (H 𝟙 (λ _ → i) (λ _ → b))

-- (d) f is k-truncated  iff  postcomposition by f is k-truncated for every type X
-- postcomposition is map-Π at constant families, so (a) and Π-𝟙 do the work again
postcomp : {A B : Set} → (f : A → B) → (X : Set) → (X → A) → (X → B)
postcomp f X g = f ∘ g

trunc-map-to-postcomp-trunc-map : {A B : Set} → {k : 𝕋} → (f : A → B)
  → is-trunc-map k f → (X : Set) → is-trunc-map k (postcomp f X)
trunc-map-to-postcomp-trunc-map {A} {B} {k} f ftrunc X = trunc-map-Π (λ _ → A) (λ _ → B) (λ i → f) λ i → ftrunc

postcomp-trunc-map-to-trunc-map : {A B : Set} → {k : 𝕋} → (f : A → B)
  → ((X : Set) → is-trunc-map k (postcomp f X)) → is-trunc-map k f
postcomp-trunc-map-to-trunc-map {A} {B} {k} f H b = equiv-to-same-k-type (concat-≃ (inv-≃ (Π-𝟙 (λ _ → fib f b))) (inv-≃ (fib-map-Π-equiv-Π-fib (λ _ → A) (λ _ → B) (λ i → f) λ i → b))) (H 𝟙 (λ i → b))

-- corollaries of (d): k := -2𝕋 reads as "equivalence", k := succ𝕋 -2𝕋 as "embedding"
equiv-to-postcomp-equiv : {A B : Set} → (f : A → B)
  → is-equiv f → (X : Set) → is-equiv (postcomp f X)
equiv-to-postcomp-equiv f fequiv X = contr-map-to-equiv (postcomp f X)
  (trunc-map-to-postcomp-trunc-map {k = -2𝕋} f (equiv-to-contr-map f fequiv) X)

postcomp-equiv-to-equiv : {A B : Set} → (f : A → B)
  → ((X : Set) → is-equiv (postcomp f X)) → is-equiv f
postcomp-equiv-to-equiv f H = contr-map-to-equiv f
  (postcomp-trunc-map-to-trunc-map {k = -2𝕋} f (λ X → equiv-to-contr-map (postcomp f X) (H X)))

emb-to-postcomp-emb : {A B : Set} → (f : A → B)
  → is-emb f → (X : Set) → is-emb (postcomp f X)
emb-to-postcomp-emb f femb X = fib-prop-to-emb (postcomp f X)
  (trunc-map-to-postcomp-trunc-map {k = succ𝕋 -2𝕋} f (emb-to-fib-prop f femb) X)

postcomp-emb-to-emb : {A B : Set} → (f : A → B)
  → ((X : Set) → is-emb (postcomp f X)) → is-emb f
postcomp-emb-to-emb f H = fib-prop-to-emb f
  (postcomp-trunc-map-to-trunc-map {k = succ𝕋 -2𝕋} f (λ X → emb-to-fib-prop (postcomp f X) (H X)))

-- 13.13, proved first over 𝟚: the two-element type with constructors is easier to
-- compute with than Fin 2ℕ = (𝟘 ⊎ 𝟙) ⊎ 𝟙.  Π-distrib-⊎ below recodes this into the
-- form the book states.
𝟚-≃-Fin2 : 𝟚 ≃ Fin 2ℕ
𝟚-≃-Fin2 = fwd , ((bwd , λ {(inl (inr *)) → refl
                           ; (inr *) → refl}) , (bwd , λ {true → refl
                                                        ; false → refl}))
  where
  fwd : 𝟚 → Fin 2ℕ
  fwd true = inr *
  fwd false = inl (inr *)

  bwd : Fin 2ℕ → 𝟚
  bwd (inl (inr *)) = false
  bwd (inr *) = true

Π-distrib-⊎-𝟚 : {X : Set} → (A B : X → Set) →
  ((x : X) → ((A x) ⊎ (B x)))
  ≃ (Σ (X → 𝟚) (λ g → ((x : X) → ((g x ≡ false → A x))) × ((x : X) → ((g x ≡ true) → B x))))
Π-distrib-⊎-𝟚 {X} A B = concat-≃ E1 (concat-≃ E2 E3)
  where
  -- the pointwise fibre: which summand was chosen, plus the payload
  Dec : (x : X) → 𝟚 → Set
  Dec x b = (b ≡ false → A x) × (b ≡ true → B x)

  step1 : (x : X) → (A x ⊎ B x) → Σ 𝟚 (Dec x)
  step1 x (inl a) = false , ((λ z → a) , (λ ()))
  step1 x (inr b) = true , ((λ ()) , λ z → b)

  step1-inv : (x : X) → Σ 𝟚 (Dec x) → (A x ⊎ B x)
  step1-inv x (true , d) = inr ((proj₂ d) refl)
  step1-inv x (false , d) = inl ((proj₁ d) refl)

  step1-equiv : is-equiv-fam step1
  step1-equiv x = (step1-inv x , sec-htpy) , (step1-inv x , retr-htpy)
    where
    sec-htpy : step1 x ∘ step1-inv x ∼ id
    sec-htpy (true , (df , dt)) = eq-pair _ _ (refl , eq-pair× (eq-htpy _ _ (λ ())) (eq-htpy _ _ λ {refl → refl}))
    sec-htpy (false , (df , dt)) = eq-pair _ _ (refl , eq-pair× (eq-htpy _ _ (λ {refl → refl})) (eq-htpy _ _ λ ()))

    retr-htpy : step1-inv x ∘ step1 x ∼ id
    retr-htpy (inl a) = refl
    retr-htpy (inr b) = refl

  -- lift the pointwise equivalence to Π
  E1 : ((x : X) → (A x ⊎ B x)) ≃ ((x : X) → Σ 𝟚 (Dec x))
  E1 = map-Π (λ x → A x ⊎ B x) (λ x → Σ 𝟚 (Dec x)) step1
     , fam-equiv-to-Π-equiv (λ x → A x ⊎ B x) (λ x → Σ 𝟚 (Dec x)) step1 step1-equiv

  -- Π distributes over Σ (type-theoretic choice, Theorem 13.2.1)
  E2 : ((x : X) → Σ 𝟚 (Dec x)) ≃ (Σ (X → 𝟚) (λ g → (x : X) → Dec x (g x)))
  E2 = Π-distrib-Σ {X} {λ _ → 𝟚} {Dec}

  -- Π distributes over × in each fibre
  E3 : (Σ (X → 𝟚) (λ g → (x : X) → Dec x (g x)))
     ≃ (Σ (X → 𝟚) (λ g → ((x : X) → ((g x ≡ false → A x))) × ((x : X) → ((g x ≡ true) → B x))))
  E3 = tot fibrewise , fam-equiv-to-tot-equiv fibrewise fibrewise-equiv
    where
    fibrewise : (g : X → 𝟚) → ((x : X) → Dec x (g x))
      → ((x : X) → ((g x ≡ false → A x))) × ((x : X) → ((g x ≡ true) → B x))
    fibrewise g = proj₁ (Π-distrib-× (λ x → g x ≡ false → A x) (λ x → g x ≡ true → B x))

    fibrewise-equiv : is-equiv-fam fibrewise
    fibrewise-equiv g = proj₂ (Π-distrib-× (λ x → g x ≡ false → A x) (λ x → g x ≡ true → B x))

-- 13.13 as the book states it: recode Π-distrib-⊎-𝟚 along e : 𝟚 ≃ Fin 2ℕ, the base by
-- postcomposition with e and each fibre by precomposition with ap e (e false and e true
-- reduce to inl (inr *) and inr *, so the component types match on the nose)
Π-distrib-⊎ : {X : Set} → (A B : X → Set)
  → ((x : X) → ((A x) ⊎ (B x)))
  ≃ (Σ (X → Fin 2ℕ) (λ g → ((x : X) → ((g x ≡ inl (inr *) → A x)))
                         × ((x : X) → ((g x ≡ inr *) → B x))))
Π-distrib-⊎ {X} A B = concat-≃ (Π-distrib-⊎-𝟚 A B) recode
  where
  e : 𝟚 → Fin 2ℕ
  e = proj₁ 𝟚-≃-Fin2

  e-emb : is-emb e
  e-emb = equiv-to-emb e (proj₂ 𝟚-≃-Fin2)

  post-e : (X → 𝟚) → (X → Fin 2ℕ)
  post-e = postcomp e X

  C : (X → 𝟚) → Set
  C g = ((x : X) → ((g x ≡ false → A x))) × ((x : X) → ((g x ≡ true) → B x))

  D : (X → Fin 2ℕ) → Set
  D h = ((x : X) → ((h x ≡ inl (inr *) → A x))) × ((x : X) → ((h x ≡ inr *) → B x))

  -- fibrewise: precomposing with ap e reindexes a component from Fin 2ℕ to 𝟚
  recodeA : (g : X → 𝟚) → (x : X) → (e (g x) ≡ e false → A x) → (g x ≡ false → A x)
  recodeA g x = precomp-Π (ap e) (λ _ → A x)

  recodeB : (g : X → 𝟚) → (x : X) → (e (g x) ≡ e true → B x) → (g x ≡ true → B x)
  recodeB g x = precomp-Π (ap e) (λ _ → B x)

  recodeA-equiv : (g : X → 𝟚) → is-equiv-fam (recodeA g)
  recodeA-equiv g x = is-equiv-to-precomp-Π-is-equiv (ap e) (e-emb (g x) false) (λ _ → A x)

  recodeB-equiv : (g : X → 𝟚) → is-equiv-fam (recodeB g)
  recodeB-equiv g x = is-equiv-to-precomp-Π-is-equiv (ap e) (e-emb (g x) true) (λ _ → B x)

  fib-map : (g : X → 𝟚) → D (post-e g) → C g
  fib-map g = map-Π (λ x → e (g x) ≡ e false → A x) (λ x → g x ≡ false → A x) (recodeA g)
           ×' map-Π (λ x → e (g x) ≡ e true → B x) (λ x → g x ≡ true → B x) (recodeB g)

  fib-map-equiv : is-equiv-fam fib-map
  fib-map-equiv g = equiv×equiv-to-equiv _ _
    (fam-equiv-to-Π-equiv _ _ (recodeA g) (recodeA-equiv g))
    (fam-equiv-to-Π-equiv _ _ (recodeB g) (recodeB-equiv g))

  recode : (Σ (X → 𝟚) C) ≃ (Σ (X → Fin 2ℕ) D)
  recode = concat-≃
    (inv-≃ (tot fib-map , fam-equiv-to-tot-equiv fib-map fib-map-equiv))
    (base-change post-e D , f-equiv-to-base-change-equiv post-e D
      (equiv-to-postcomp-equiv e (proj₂ 𝟚-≃-Fin2) X))
