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
funext-at-to-is-contr-total-htpy {A} {B} f fext = is-contr-codomain-equiv (tot (htpy-eq f)) (Σ-≡-contractible f) (fam-equiv-to-tot-equiv (htpy-eq f) fext)

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

total-htpy-is-contr : (A : Set) → is-contr (Σ (A → A) (λ f → f ∼ id))
total-htpy-is-contr A = is-contr-codomain-equiv (tot (λ f → htpy-eq f id)) (identity-contr id) (fam-equiv-to-tot-equiv (λ x → htpy-eq x id) λ f → fun-ext f id)

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
  (is-contr-codomain-equiv (proj₁ Π-distrib-Σ) (fam-trunc-to-Π-trunc fiber-contr) (proj₂ Π-distrib-Σ)) P
  where
    canonical-map : (a : A) → (y : B a) → (f a ≡ y) → E a (f a) y
    canonical-map a y p = tr (E a (f a)) p (e a (f a))

    fiber-contr : (a : A) → is-contr (Σ (B a) (E a (f a)))
    fiber-contr a = fam-equiv-to-total-contr (e a (f a)) (canonical-map a) refl
      (id-sys-to-fam-equiv (e a (f a)) (canonical-map a) refl (hyp a (f a)))

ev-pair-dep : {A : Set} → {B : A → Set} → {C : Σ A B → Set} → ((z : Σ A B) → C z) → ((x : A) → (y : B x) → C (x , y))
ev-pair-dep f x y = f (x , y)

dep-univ-prop-Σ : {A : Set} → {B : A → Set} → {C : Σ A B → Set} → is-equiv (ev-pair-dep {A} {B} {C})
dep-univ-prop-Σ = (indΣ , λ x → rfl-htpy (λ x₁ → x₁) x) , (indΣ , λ x → eq-htpy _ _ (indΣ λ x₁ y → refl))

univ-prop-× : {A B X : Set} → is-equiv (ev-pair-dep {A} {λ _ → B} {λ _ → X})
univ-prop-× {A} {B} {X} = dep-univ-prop-Σ {A} {λ _ → B} {λ _ → X}

univ-prop-Σ : {A : Set} → {B : A → Set} → {X : Set} → is-equiv (ev-pair-dep {A} {B} {λ _ → X})
univ-prop-Σ {A} {B} {X} = dep-univ-prop-Σ {A} {B} {λ _ → X}

ev-refl-dep : {A : Set} → {a : A} → {B : (x : A) → a ≡ x → Set} → ((x : A) → (p : a ≡ x) → B x p) → B a refl
ev-refl-dep f = f _ refl

dep-univ-prop-id : {A : Set} → {a : A} → {B : (x : A) → a ≡ x → Set} → is-equiv (ev-refl-dep {A} {a} {B})
dep-univ-prop-id {A} {a} {B} = (ind≡ , (λ x → refl)) , (ind≡ , λ f → eq-htpy _ _ λ y → eq-htpy _ _ (ind≡ {A} {a} {λ x p → ind≡ (ev-refl-dep f) x p ≡ f x p} refl y))

univ-prop-id : {A : Set} → {a : A} → {B : A → Set} → is-equiv (ev-refl-dep {A} {a} {λ x _ → B x})
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

-- Shared steps for 13.2: each identity-type characterisation reassociates, swaps the
-- structure component past the homotopy component, and projects away a contractible fibre.
tot-≃ : {A : Set} → {B C : A → Set} → ((x : A) → B x ≃ C x) → Σ A B ≃ Σ A C
tot-≃ e = tot (λ x → proj₁ (e x)) , fam-equiv-to-tot-equiv (λ x → proj₁ (e x)) (λ x → proj₂ (e x))

Σ-swap-drop-contr : {P Q : Set} → (R : P → Q → Set) → ((q : Q) → is-contr (Σ P (λ p → R p q)))
  → Σ P (λ p → Σ Q (R p)) ≃ Q
Σ-swap-drop-contr R c = concat-≃ (Σ-swap R) (proj₁ , fib-contr-to-proj₁-equiv c)

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
    htpy-total-equiv : Σ (pointed-map a b) (Eq-pointed-map a b (f , fab)) ≃ Σ (A → B) (λ h → f ∼ h)
    htpy-total-equiv =
      concat-≃ (Σ-assoc (λ h → h a ≡ b) (Eq-pointed-map a b (f , fab)))
        (tot-≃ (λ h → Σ-swap-drop-contr (λ hab H → concat (inv (H a)) fab ≡ hab)
          (λ H → Σ-≡-contractible (concat (inv (H a)) fab))))

    pointed-total-contr : is-contr (Σ (pointed-map a b) (Eq-pointed-map a b (f , fab)))
    pointed-total-contr =
      is-contr-codomain-equiv (proj₁ (inv-≃ htpy-total-equiv))
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
    (is-contr-codomain-equiv (proj₁ (inv-≃ (comm-tri-post-total-equiv))) (funext-at-to-is-contr-total-htpy h (fun-ext h)) (proj₂ (inv-≃ (comm-tri-post-total-equiv))))
    (h' , H')

  where
    comm-tri-post-total-equiv : Σ (comm-tri-post f g) (Eq-comm-tri-post f g (h , H)) ≃ Σ (A → B) (λ h' → (h ∼ h'))
    comm-tri-post-total-equiv =
      concat-≃ (Σ-assoc (λ h₁ → triangle-commutes f h₁ g) (Eq-comm-tri-post f g (h , H)))
        (tot-≃ (λ h' → Σ-swap-drop-contr (λ H' K → (x : A) → concat (H x) (ap g (K x)) ≡ H' x)
          (λ K → funext-at-to-is-contr-total-htpy (λ x → concat (H x) (ap g (K x))) (fun-ext λ x → concat (H x) (ap g (K x))))))

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
    (is-contr-codomain-equiv
      (proj₁ (inv-≃ comm-tri-pre-total-equiv))
      (funext-at-to-is-contr-total-htpy h (fun-ext h))
      (proj₂ (inv-≃ comm-tri-pre-total-equiv)))
    (h' , H')

  where
    comm-tri-pre-total-equiv : Σ (comm-tri-pre f g) (Eq-comm-tri-pre f g (h , H)) ≃ Σ (X → Y) (λ h' → (h ∼ h'))
    comm-tri-pre-total-equiv =
      concat-≃ (Σ-assoc (λ h₁ → triangle-commutes g f h₁) (Eq-comm-tri-pre f g (h , H)))
        (tot-≃ (λ h' → Σ-swap-drop-contr (λ H' K → (x : A) → concat (H x) (K (f x)) ≡ H' x)
          (λ K → funext-at-to-is-contr-total-htpy (λ x → concat (H x) (K (f x))) (fun-ext λ x → concat (H x) (K (f x))))))

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
  (is-contr-codomain-equiv
    (proj₁ (inv-≃ comm-sq-total-equiv))
    (funext-at-to-is-contr-total-htpy i (fun-ext i))
    (proj₂ (inv-≃ comm-sq-total-equiv)))
  (i' , (j' , H'))

  where
    Coh : {i' : A → X} → {j' : B → Y} → i ∼ i' → j ∼ j' → square-commutes f i' g j' → Set
    Coh Ki Kj H' = (a : A) → concat (H a) (ap g (Ki a)) ≡ concat (Kj (f a)) (H' a)

    coh-contr : (i' : A → X) → (j' : B → Y) → (Ki : i ∼ i') → (Kj : j ∼ j')
      → is-contr (Σ (square-commutes f i' g j') (Coh Ki Kj))
    coh-contr i' j' Ki Kj =
      is-contr-codomain-equiv
        (proj₁ Π-distrib-Σ)
        (fam-trunc-to-Π-trunc (λ a →
          is-contr-codomain-equiv
            (tot (λ y → inv))
            (equiv-to-contr-map (concat (Kj (f a))) (is-equiv-concat (Kj (f a))) (concat (H a) (ap g (Ki a))))
            (fam-equiv-to-tot-equiv (λ y → inv) (λ y → is-equiv-inv (concat (Kj (f a)) y) (concat (H a) (ap g (Ki a)))))))
        (proj₂ Π-distrib-Σ)

    -- for fixed Ki, the (j', H', Kj) part is equivalent to the total space of homotopies from j
    j-total-equiv : (i' : A → X) → (Ki : i ∼ i')
      → Σ (B → Y) (λ j' → Σ (square-commutes f i' g j') (λ H' → Σ (j ∼ j') (λ Kj → Coh Ki Kj H')))
      ≃ Σ (B → Y) (λ j' → j ∼ j')
    j-total-equiv i' Ki = tot-≃ (λ j' → Σ-swap-drop-contr (λ H' Kj → Coh Ki Kj H') (coh-contr i' j' Ki))

    comm-sq-total-equiv : Σ (comm-sq f g) (Eq-comm-sq f g (i , (j , H))) ≃ Σ (A → X) (λ i' → i ∼ i')
    comm-sq-total-equiv =
      concat-≃ (Σ-assoc (λ i' → Σ (B → Y) (λ j' → square-commutes f i' g j')) (Eq-comm-sq f g (i , (j , H))))
        (tot-≃ (λ i' →
          concat-≃ (Σ-assoc (square-commutes f i' g) (λ w → Eq-comm-sq f g (i , (j , H)) (i' , w)))
            (concat-≃ (tot-≃ (λ j' → Σ-swap (λ H' Ki → Σ (j ∼ j') (λ Kj → Coh Ki Kj H'))))
              (Σ-swap-drop-contr (λ j' Ki → Σ (square-commutes f i' g j') (λ H' → Σ (j ∼ j') (λ Kj → Coh Ki Kj H')))
                (λ Ki → is-contr-domain-equiv
                  (proj₁ (j-total-equiv i' Ki))
                  (funext-at-to-is-contr-total-htpy j (fun-ext j))
                  (proj₂ (j-total-equiv i' Ki)))))))

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
  is-contr-codomain-equiv
    (proj₁ (Π-fib-equiv-sec f))
    (fam-trunc-to-Π-trunc (equiv-to-contr-map f e))
    (proj₂ (Π-fib-equiv-sec f))

-- (b)
equiv-to-contr-retr : {A B : Set} → (f : A → B) → is-equiv f → is-contr (retr f)
equiv-to-contr-retr {A} {B} f e =
  is-contr-codomain-equiv
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
    ABcontr : is-contr (A → B)
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
      is-contr-codomain-equiv
        (choice {A} {λ a → g (f a) ≡ a} {λ a p → G (f a) ≡ ap f p})
        ΠΣ-contr
        (choice-equiv {A} {λ a → g (f a) ≡ a} {λ a p → G (f a) ≡ ap f p})
      where
        -- For each a, the fibre Σ (p : g(f a) ≡ a) (G(f a) ≡ ap f p) is
        -- contractible, since it is (up to inv) a fibre of the equivalence ap f
        fibre-contr : (a : A) → is-contr (Σ (g (f a) ≡ a) (λ p → G (f a) ≡ ap f p))
        fibre-contr a =
          is-contr-codomain-equiv
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
      is-contr-codomain-equiv
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
    ΣAB-contr : is-contr (Σ A B)
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
    K≡ : (n : ℕ) → ap (λ j → j n) P ≡ K n
    K≡ = ap-ev-eq-htpy h (indℕ x (λ _ → f)) K

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

-- transport of a section-homotopy along a path between the underlying maps
tr-sec-htpy : {B X : Set} → (g : B → X) → (k₁ k₂ : X → B) → (p : k₁ ≡ k₂)
  → (G : (g ∘ k₁) ∼ id)
  → tr (λ k → (g ∘ k) ∼ id) p G ≡ (λ x → concat (ap g (inv (htpy-eq k₁ k₂ p x))) (G x))
tr-sec-htpy g k .k refl G = eq-htpy _ _ λ x → inv (left-unit (G x))

-- 13.14
comm-tri-sec-h-to-sec-g-retr-of-sec-f : {A B X : Set} → (f : A → X) → (g : B → X) → (h : A → B) → triangle-commutes f h g → sec h → is-retract-of (sec g) (sec f)
comm-tri-sec-h-to-sec-g-retr-of-sec-f {A} {B} {X} f g h commfhg (hsec , hsec-htpy) = 
  proj₂ (comm-tri-sec-h-to-sec-f-iff-sec-g f g h commfhg (hsec , hsec-htpy)) , 
  ((proj₁ (comm-tri-sec-h-to-sec-f-iff-sec-g f g h commfhg (hsec , hsec-htpy))) , 
  λ {(gsec , gsec-htpy) → eq-pair _ _ (eq-htpy _ _ (λ x → hsec-htpy (gsec x)) , final gsec gsec-htpy)})
  where
  iff : sec f ↔ sec g
  iff = comm-tri-sec-h-to-sec-f-iff-sec-g f g h commfhg (hsec , hsec-htpy)

  -- the homotopy component r ∘ i actually produces, after inv-inv / assoc / left-inv
  comp-htpy : (k : X → B) → (gk : (g ∘ k) ∼ id)
    → proj₂ (proj₁ iff (proj₂ iff (k , gk)))
    ∼ (λ x → concat (ap g (hsec-htpy (k x))) (gk x))
  comp-htpy k gk x =
    concat (ap (λ q → concat (inv c) (concat q (gk x))) (inv-inv (concat c a)))
    (concat (inv (assoc (inv c) (concat c a) (gk x)))
            (ap (λ q → concat q (gk x))
                (concat (inv (assoc (inv c) c a))
                        (concat (ap (λ q → concat q a) (left-inv c)) (left-unit a)))))
    where
    c = commfhg (hsec (k x))
    a = ap g (hsec-htpy (k x))

  -- ap-inv / assoc / left-inv / left-unit
  cancel : (k : X → B) → (gk : (g ∘ k) ∼ id) → (x : X)
    → concat (ap g (inv (hsec-htpy (k x)))) (concat (ap g (hsec-htpy (k x))) (gk x)) ≡ gk x
  cancel k gk x =
    concat (ap (λ w → concat w (concat a (gk x))) (ap-inv g (hsec-htpy (k x))))
    (concat (inv (assoc (inv a) a (gk x)))
    (concat (ap (λ w → concat w (gk x)) (left-inv a))
            (left-unit (gk x))))
    where
    a = ap g (hsec-htpy (k x))

  -- assemble: rewrite the transport, strip the funext, then comp-htpy + cancel pointwise
  final : (k : X → B) → (gk : (g ∘ k) ∼ id)
    → tr (λ k' → (g ∘ k') ∼ id) (eq-htpy (h ∘ (hsec ∘ k)) k (λ x → hsec-htpy (k x)))
         (proj₂ (proj₁ iff (proj₂ iff (k , gk))))
    ≡ gk
  final k gk =
    concat (tr-sec-htpy g (h ∘ (hsec ∘ k)) k
              (eq-htpy (h ∘ (hsec ∘ k)) k (λ x → hsec-htpy (k x)))
              (proj₂ (proj₁ iff (proj₂ iff (k , gk)))))
    (eq-htpy _ _ (λ x →
      concat (ap (λ w → concat (ap g (inv w)) (proj₂ (proj₁ iff (proj₂ iff (k , gk))) x))
                 (htpy-eq _ _ (htpy-eq-eq-htpy (h ∘ (hsec ∘ k)) k (λ y → hsec-htpy (k y))) x))
      (concat (ap (concat (ap g (inv (hsec-htpy (k x))))) (comp-htpy k gk x))
              (cancel k gk x))))

-- (b)
tr-retr-htpy : {B X : Set} → (h : X → B) → (k₁ k₂ : B → X) → (p : k₁ ≡ k₂)
  → (G : (k₁ ∘ h) ∼ id)
  → tr (λ k → (k ∘ h) ∼ id) p G ≡ (λ x → concat (inv (htpy-eq k₁ k₂ p (
    h x))) (G x))
tr-retr-htpy h k .k refl G = eq-htpy _ _ λ x → inv (left-unit (G x))

comm-tri-retr-g-to-retr-h-retr-of-retr-f : {A B X : Set} → (f : A → X) → (g : B → X) → (h : A → B) → triangle-commutes f h g → retr g → is-retract-of (retr h) (retr f)
comm-tri-retr-g-to-retr-h-retr-of-retr-f {A} {B} {X} f g h commfhg (gret , gret-htpy) =
  proj₂ iff ,
  (proj₁ iff ,
   λ {(k , kh) → eq-pair _ _ (eq-htpy _ _ (λ x → ap k (gret-htpy x)) , final k kh)})
  where
  iff : retr f ↔ retr h
  iff = comm-tri-retr-g-to-retr-f-iff-retr-h f g h commfhg (gret , gret-htpy)

  -- the homotopy component r ∘ i actually produces, after ap-comp / inv-inv / ap-concat
  comp-htpy : (k : B → A) → (kh : (k ∘ h) ∼ id)
    → proj₂ (proj₁ iff (proj₂ iff (k , kh)))
    ∼ (λ x → concat (ap k (gret-htpy (h x))) (kh x))
  comp-htpy k kh x =
    concat (ap (λ w → concat w (concat (ap k (inv (comm' x))) (kh x)))
               (concat (ap-inv (k ∘ gret) (commfhg x))
                       (ap inv (inv (ap-comp gret k (commfhg x))))))
    (concat (ap (λ w → concat (inv α) (concat w (kh x)))
                (concat (ap (ap k) (inv-inv (concat (ap gret (commfhg x)) (gret-htpy (h x)))))
                        (ap-concat k (ap gret (commfhg x)) (gret-htpy (h x)))))
    (concat (ap (concat (inv α)) (assoc α β (kh x)))
    (concat (inv (assoc (inv α) α (concat β (kh x))))
    (concat (ap (λ w → concat w (concat β (kh x))) (left-inv α))
            (left-unit (concat β (kh x)))))))
    where
    comm' = comm-tri-retr-g-to-comm-tri f g h commfhg (gret , gret-htpy)
    α = ap k (ap gret (commfhg x))
    β = ap k (gret-htpy (h x))

  -- assoc / left-inv / left-unit
  cancel : (k : B → A) → (kh : (k ∘ h) ∼ id) → (x : A)
    → concat (inv (ap k (gret-htpy (h x)))) (concat (ap k (gret-htpy (h x))) (kh x)) ≡ kh x
  cancel k kh x =
    concat (inv (assoc (inv β) β (kh x)))
    (concat (ap (λ w → concat w (kh x)) (left-inv β))
            (left-unit (kh x)))
    where
    β = ap k (gret-htpy (h x))

  -- assemble: rewrite the transport, strip the funext, then comp-htpy + cancel pointwise
  final : (k : B → A) → (kh : (k ∘ h) ∼ id)
    → tr (λ k' → (k' ∘ h) ∼ id) (eq-htpy ((k ∘ gret) ∘ g) k (λ x → ap k (gret-htpy x)))
         (proj₂ (proj₁ iff (proj₂ iff (k , kh))))
    ≡ kh
  final k kh =
    concat (tr-retr-htpy h ((k ∘ gret) ∘ g) k
              (eq-htpy ((k ∘ gret) ∘ g) k (λ x → ap k (gret-htpy x)))
              (proj₂ (proj₁ iff (proj₂ iff (k , kh)))))
    (eq-htpy _ _ (λ x →
      concat (ap (λ w → concat (inv w) (proj₂ (proj₁ iff (proj₂ iff (k , kh))) x))
                 (htpy-eq _ _ (htpy-eq-eq-htpy ((k ∘ gret) ∘ g) k (λ y → ap k (gret-htpy y))) (h x)))
      (concat (ap (concat (inv (ap k (gret-htpy (h x))))) (comp-htpy k kh x))
              (cancel k kh x))))

-- 13.15
hom : {A B X : Set} → (f : A → X) → (g : B → X) → Set
hom f g = comm-tri-post f g

-- 13.15a
-- The chain:
--   (x : X) → fib f x → P x
--     ≃ (a : A) → (x : X) → f a ≡ x → P x      (Π-Σ-curry, Π-swap)
--     ≃ (a : A) → P (f a)                      (ev-refl-sing-is-equiv)

Π-Σ-curry : {A : Set} → (B : A → Set) → (C : Σ A B → Set)
  → ((w : Σ A B) → C w) → ((a : A) → (b : B a) → C (a , b))
Π-Σ-curry B C h a b = h (a , b)

Π-Σ-curry-is-equiv : {A : Set} → (B : A → Set) → (C : Σ A B → Set)
  → is-equiv (Π-Σ-curry B C)
Π-Σ-curry-is-equiv B C = (bwd B C , sec-htpy B C) , ((bwd B C) , retr-htpy B C)
  where
  bwd : {A : Set} → (B : A → Set) → (C : Σ A B → Set) → ((a : A) → (b : B a) → C (a , b)) → ((w : Σ A B) → C w) 
  bwd B C abC (a , b) = abC a b
  sec-htpy : {A : Set} → (B : A → Set) → (C : Σ A B → Set) → (Π-Σ-curry B C) ∘ (bwd B C) ∼ id
  sec-htpy B C abC = eq-htpy _ _ λ a → eq-htpy _ _ λ b → refl
  retr-htpy : {A : Set} → (B : A → Set) → (C : Σ A B → Set) → (bwd B C) ∘ (Π-Σ-curry B C) ∼ id
  retr-htpy B C sabC = eq-htpy _ _ λ {(a , b) → refl}

Π-swap : {A B : Set} → (C : A → B → Set)
  → ((a : A) → (b : B) → C a b) → ((b : B) → (a : A) → C a b)
Π-swap C h b a = h a b

Π-swap-is-equiv : {A B : Set} → (C : A → B → Set) → is-equiv (Π-swap C)
Π-swap-is-equiv {A} {B} C = ((Π-swap (λ z _ → (x : B) → C z x) λ a b x → b x a) , λ x → refl) , ((λ x x₁ x₂ → x x₂ x₁) , (λ x → refl))

-- evaluation at (x , refl) out of a family over the singleton x ≡ _
ev-refl-sing : {X : Set} → (x : X) → (P : X → Set) → ((y : X) → x ≡ y → P y) → P x
ev-refl-sing x P h = h x refl

ev-refl-sing-is-equiv : {X : Set} → (x : X) → (P : X → Set) → is-equiv (ev-refl-sing x P)
ev-refl-sing-is-equiv x P = (bwd x P , λ x₁ → refl) , ((bwd x P) , retr-htpy x P)
  where
  bwd : {X : Set} → (x : X) → (P : X → Set) → P x → ((y : X) → x ≡ y → P y) 
  bwd x P Px .x refl = Px
  retr-htpy : {X : Set} → (x : X) → (P : X → Set) → (bwd x P) ∘ (ev-refl-sing x P) ∼ id 
  retr-htpy x P f = eq-htpy _ _ λ y → eq-htpy _ _ λ {refl → refl}

ev-fib-refl : {A X : Set} → (f : A → X) → (P : X → Set) → ((x : X) → fib f x → P x) → ((a : A) → P (f a))
ev-fib-refl f P fibP a = fibP (f a) (a , refl)

ev-fib-refl-is-equiv : {A X : Set} → (f : A → X) → (P : X → Set) → is-equiv (ev-fib-refl f P)
ev-fib-refl-is-equiv {A} {X} f P = equiv-comp 
  (map-Π (λ x → (fib f x → P x)) (λ x → (a : A) → f a ≡ x → P x) λ x → λ faxP a fax → faxP (a , fax)) 
  (λ z a → z (f a) a refl) 
  (fam-equiv-to-Π-equiv 
    (λ x → fib f x → P x) 
    (λ x → (a : A) → f a ≡ x → P x) 
    (λ x afaxP a fax → afaxP (a , fax)) 
    λ x → Π-Σ-curry-is-equiv (λ z → f z ≡ x) λ _ → P x) 
  (equiv-comp 
    (Π-swap λ x a → f a ≡ x → P x)
    (λ z a → z a (f a) refl) 
    (Π-swap-is-equiv (λ x a → f a ≡ x → P x)) 
    (fam-equiv-to-Π-equiv (λ z → (a : X) → f z ≡ a → P a) (λ z → P (f z)) (λ i z → z (f i) refl) λ a → ev-refl-sing-is-equiv (f a) P)) 

Π-fib-map-equiv-Π-precomp : {A X : Set} → (f : A → X) → (P : X → Set) → ((x : X) → fib f x → P x) ≃ ((a : A) → P (f a))
Π-fib-map-equiv-Π-precomp f P = ev-fib-refl f P , ev-fib-refl-is-equiv f P

-- 13.15b
-- α = action-on-fibers          : hom f g → (x : X) → fib f x → fib g x
-- β = hom-to-Π-fib              : hom f g → (a : A) → fib g (f a)
-- γ = fam-fib-map-equiv-Π-fib   : ((x : X) → fib f x → fib g x) ≃ ((a : A) → fib g (f a))
--     (13.15a at P := fib g)
-- and the triangle β ∼ γ ∘ α commutes.

action-on-fibers : {A B X : Set} → (f : A → X) → (g : B → X)
  → hom f g → (x : X) → fib f x → fib g x
action-on-fibers f g (h , H) = fib-triangle f g h H

hom-to-Π-fib : {A B X : Set} → (f : A → X) → (g : B → X) → hom f g → ((a : A) → fib g (f a))
hom-to-Π-fib f g φ a = proj₁ φ a , inv (proj₂ φ a)

fam-fib-map-equiv-Π-fib : {A B X : Set} → (f : A → X) → (g : B → X)
  → ((x : X) → fib f x → fib g x) ≃ ((a : A) → fib g (f a))
fam-fib-map-equiv-Π-fib f g = Π-fib-map-equiv-Π-precomp f (fib g)

comm-tri-hom-fib : {A B X : Set} → (f : A → X) → (g : B → X)
  → triangle-commutes (hom-to-Π-fib f g) (action-on-fibers f g) (ev-fib-refl f (fib g))
comm-tri-hom-fib f g (h , commfgh) = eq-htpy _ _ λ a → eq-pair _ _ (refl , inv (right-unit _))

-- β and γ are equivalences directly; α follows by 3-for-2 on the triangle

hom-to-Π-fib-is-equiv : {A B X : Set} → (f : A → X) → (g : B → X) → is-equiv (hom-to-Π-fib f g)
hom-to-Π-fib-is-equiv f g = equiv-comp 
  (tot λ h commfgh → inv-htpy λ x → commfgh x) 
  choice-inv
  (fam-equiv-to-tot-equiv (λ k commfxg → inv-htpy commfxg) λ k → inv-htpy-equiv) 
  (sec-map-is-equiv (λ x → choice x) choice-equiv)

hom-equiv-Π-fib : {A B X : Set} → (f : A → X) → (g : B → X)
  → hom f g ≃ ((a : A) → fib g (f a))
hom-equiv-Π-fib f g = hom-to-Π-fib f g , hom-to-Π-fib-is-equiv f g

action-on-fibers-is-equiv : {A B X : Set} → (f : A → X) → (g : B → X)
  → is-equiv (action-on-fibers f g)
action-on-fibers-is-equiv f g =
  3-for-2-f-g-to-h (hom-to-Π-fib f g) (ev-fib-refl f (fib g)) (action-on-fibers f g)
    (comm-tri-hom-fib f g) (hom-to-Π-fib-is-equiv f g) (ev-fib-refl-is-equiv f (fib g))

hom-equiv-fam-fib-map : {A B X : Set} → (f : A → X) → (g : B → X)
  → hom f g ≃ ((x : X) → fib f x → fib g x)
hom-equiv-fam-fib-map f g = action-on-fibers f g , action-on-fibers-is-equiv f g

-- 13.15c
-- (i) is-equiv h   ⇔   (ii) is-equiv-fam (action-on-fibers f g (h , H))
-- is 11.11b: comm-tri-equiv-h-iff-fam-equiv-fib-tri f g h H.
-- (i) ⇔ (iii), precomposition with (h , H) is an equivalence, is below.

hom-precomp : {A B C X : Set} → (f : A → X) → (g : B → X) → (i : C → X)
  → hom f g → hom g i → hom f i
hom-precomp f g i φ ψ =
  (proj₁ ψ ∘ proj₁ φ) , concat-htpy (proj₂ φ) (λ a → proj₂ ψ (proj₁ φ a))

equiv-h-to-equiv-hom-precomp : {A B X : Set} → (f : A → X) → (g : B → X)
  → (φ : hom f g) → is-equiv (proj₁ φ)
  → {C : Set} → (i : C → X) → is-equiv (hom-precomp f g i φ)
equiv-h-to-equiv-hom-precomp {A} {B} {X} f g φ hequiv {C} i =
  g-equiv-to-tot-fam-equiv
    (precomp h C)
    (λ k K → concat-htpy H λ a → K (h a))
    (is-equiv-to-precomp-Π-is-equiv h hequiv λ v → C)
    λ k → equiv-comp
      (precomp-Π h (λ z → g z ≡ (i ∘ k) z))
      (concat-htpy H)
      (is-equiv-to-precomp-Π-is-equiv h hequiv λ z → g z ≡ (i ∘ k) z)
      (concat-htpy-equiv H)
  where
    h : A → B
    h = proj₁ φ
    H = proj₂ φ

-- a hom into the trivial projection X × Y → X is just a map into Y
hom-proj₁-to-fun : {A X : Set} → (f : A → X) → (Y : Set)
  → hom f (proj₁ {A = X} {B = λ _ → Y}) → (A → Y)
hom-proj₁-to-fun f Y ψ a = proj₂ (proj₁ ψ a)

hom-proj₁-to-fun-is-equiv : {A X : Set} → (f : A → X) → (Y : Set)
  → is-equiv (hom-proj₁-to-fun f Y)
hom-proj₁-to-fun-is-equiv {A} {X} f Y = (bwd , λ y → refl) , (bwd , retr-htpy)
  where
  bwd : (A → Y) → hom f (proj₁ {A = X} {B = λ _ → Y})
  bwd y = (λ a → f a , y a) , λ a → refl
  -- pointwise, ((x₀ , y) , refl) is the centre of the singleton at x₀
  pt : (x₀ : X) → (w : X × Y) → (p : x₀ ≡ proj₁ w) → ((x₀ , proj₂ w) , refl) ≡ (w , p)
  pt x₀ (.x₀ , y) refl = refl
  retr-htpy : bwd ∘ hom-proj₁-to-fun f Y ∼ id
  retr-htpy (k , K) = ap choice (eq-htpy _ _ λ a → pt (f a) (k a) (K a))

-- test against i := proj₁ : X × Y → X; the square
--   hom g proj₁ ──hom-precomp φ──▶ hom f proj₁
--        │                              │
--     (B → Y) ────── − ∘ h ───────▶ (A → Y)
-- commutes definitionally, so − ∘ h is an equivalence for every Y (13.4.1)
equiv-hom-precomp-to-equiv-h : {A B X : Set} → (f : A → X) → (g : B → X)
  → (φ : hom f g)
  → ({C : Set} → (i : C → X) → is-equiv (hom-precomp f g i φ))
  → is-equiv (proj₁ φ)
equiv-hom-precomp-to-equiv-h f g φ precomp-equiv =
  precomp-is-equiv-to-is-equiv (proj₁ φ) λ Y →
    3-for-2-f-h-to-g
      (hom-proj₁-to-fun f Y ∘ hom-precomp f g proj₁ φ)
      (precomp (proj₁ φ) Y)
      (hom-proj₁-to-fun g Y)
      (λ _ → refl)
      (equiv-comp _ _ (precomp-equiv proj₁) (hom-proj₁-to-fun-is-equiv f Y))
      (hom-proj₁-to-fun-is-equiv g Y)

-- 13.16
-- Defining type of isomorphisms
infix 0 _≅_
_≅_ : Set → Set → Set
A ≅ B = Σ (A → B) (λ f → Σ (B → A) (λ g → (f ∘ g ≡ id) × (g ∘ f ≡ id)))

equiv-≃-iso : {A B : Set} → is-set A → is-set B → (A ≃ B) ≃ (A ≅ B)
equiv-≃-iso {A} {B} Aset Bset =
  tot-≃
    λ f →
      iff-to-≃
        (equiv-is-prop f)
        (λ x y → contr-to-eq-contr (iso-contr f x) x y)
        ((λ {((g , fg) , (h , hf)) →
                g , (eq-htpy _ _ fg , eq-htpy _ _ (λ x → concat (sec-equiv-retr f (g , fg) (h , hf) (f x)) (hf x)))})
        , (λ {(g , (fg , gf)) → (g , htpy-eq _ _ fg) , (g , htpy-eq _ _ gf)}))
  where
    -- inhabited ⇒ f is an equivalence ⇒ the type of iso data is contractible
    iso-contr : (f : A → B) → Σ (B → A) (λ g → (f ∘ g ≡ id) × (g ∘ f ≡ id))
      → is-contr (Σ (B → A) (λ g → (f ∘ g ≡ id) × (g ∘ f ≡ id)))
    iso-contr f x =
      is-contr-codomain-equiv (proj₁ reassoc) (is-prop'-to-inhab-contr (is-prop-to-is-prop' Σ-prop) (proj₁ (proj₁ (proj₂ reassoc)) x)) (proj₂ reassoc)
      where
        e : is-equiv f
        e = (proj₁ x , htpy-eq _ _ (proj₁ (proj₂ x))) , (proj₁ x , htpy-eq _ _ (proj₂ (proj₂ x)))
        sec-≃ : Σ (B → A) (λ g → f ∘ g ≡ id) ≃ sec f
        sec-≃ = tot-≃ (λ g → htpy-eq (f ∘ g) id , fun-ext _ _)
        -- sections are unique, so the base is contractible (no sethood needed)
        base-contr : is-contr (Σ (B → A) (λ g → f ∘ g ≡ id))
        base-contr = is-contr-domain-equiv (proj₁ sec-≃) (equiv-to-contr-sec f e) (proj₂ sec-≃)
        -- A is a set, so A → A is a set and the extra homotopy is a proposition
        Σ-prop : is-prop (Σ (Σ (B → A) (λ g → f ∘ g ≡ id)) (λ w → proj₁ w ∘ f ≡ id))
        Σ-prop = fam-trunc-to-Σ-trunc {k = succ𝕋 -2𝕋} (type-is-succ-type base-contr)
          (λ w → codom-trunc-to-→-trunc {k = succ𝕋 (succ𝕋 -2𝕋)} Aset (proj₁ w ∘ f) id)
        reassoc = Σ-assoc (λ g → f ∘ g ≡ id) (λ w → proj₁ w ∘ f ≡ id)

-- 13.17
fam-contr-to-Π-contr : {I : Set} → {A : I → Set} → is-set I → has-decidable-eq I → ((i : I) → is-contr (A i)) → is-contr ((i : I) → A i)
fam-contr-to-Π-contr Iset Ideceq icontrAi = (λ i → proj₁ (icontrAi i)) , λ iAi → eq-htpy _ _ λ i → proj₂ (icontrAi i) (iAi i)

Π-contr-to-fam-contr : {I : Set} → {A : I → Set} → is-set I → has-decidable-eq I → is-contr ((i : I) → A i) → ((i : I) → is-contr (A i))
Π-contr-to-fam-contr {I} {A} Iset Ideceq (iAi , eqiAi) i = (iAi i) , (λ ai → concat (ai-ext-eq-ai ai) (htpy-eq _ _ (eqiAi (ext ai)) i))
  where
    ext : A i → (j : I) → A j
    ext ai j with Ideceq i j
    ... | inl ieqj = tr A ieqj ai
    ... | inr ineqj = iAi j

    ai-ext-eq-ai : (x : A i) → x ≡ ext x i
    ai-ext-eq-ai x with Ideceq i i
    ... | inl p = ap (λ q → tr A q x) (proj₁ (Iset i i refl p))
    ... | inr np = ex-falso (np refl)

-- 13.18 (Shulman)
seq-lim : {X : Set} → (f : X → X) → Set
seq-lim {X} f = Σ (ℕ → X) (λ x → (n : ℕ) → f (x (succℕ n)) ≡ x n)

-- Paths in seq-lim g: a homotopy K : x ∼ y on the sequences, plus a coherence filling
--   g (x (n+1)) ──p n──▶ x n
--        │                 │
--  ap g (K (n+1))         K n
--        ▼                 ▼
--   g (y (n+1)) ──q n──▶ y n
-- First for a path e : x ≡ y (so we can path-induct), then for K via eq-htpy.
eq-seq-lim-path : {X : Set} → (g : X → X) → (x y : ℕ → X)
  → (p : (n : ℕ) → g (x (succℕ n)) ≡ x n) → (q : (n : ℕ) → g (y (succℕ n)) ≡ y n)
  → (e : x ≡ y)
  → ((n : ℕ) → concat (p n) (htpy-eq x y e n) ≡ concat (ap g (htpy-eq x y e (succℕ n))) (q n))
  → _≡_ {A = seq-lim g} (x , p) (y , q)
eq-seq-lim-path g x .x p q refl c = eq-pair _ _ (refl , eq-htpy _ _ λ n → concat (inv (right-unit _)) (concat (c n) (left-unit _)))

eq-seq-lim : {X : Set} → (g : X → X) → (x y : ℕ → X)
  → (p : (n : ℕ) → g (x (succℕ n)) ≡ x n) → (q : (n : ℕ) → g (y (succℕ n)) ≡ y n)
  → (K : x ∼ y)
  → ((n : ℕ) → concat (p n) (K n) ≡ concat (ap g (K (succℕ n))) (q n))
  → _≡_ {A = seq-lim g} (x , p) (y , q)
eq-seq-lim g x y p q K c = eq-seq-lim-path g x y p q (eq-htpy x y K) λ n →
  tr (λ L → concat (p n) (L n) ≡ concat (ap g (L (succℕ n))) (q n)) (inv (htpy-eq-eq-htpy x y K)) (c n)

-- drop the first term of a compatible sequence
shift : {X : Set} → (g : X → X) → seq-lim g → seq-lim g
shift g (x , p) = (λ n → x (succℕ n)) , (λ n → p (succℕ n))

-- apply g to every term
push : {X : Set} → (g : X → X) → seq-lim g → seq-lim g
push g (x , p) = (λ n → g (x n)) , (λ n → ap g (p n))

push-shift : {X : Set} → (g : X → X) → (s : seq-lim g) → push g (shift g s) ≡ s
push-shift g (x , p) = eq-seq-lim g _ x _ p p (λ n → refl)

push-is-equiv : {X : Set} → (g : X → X) → is-equiv (push g)
push-is-equiv g = (shift g , push-shift g) , (shift g , λ {(x , p) → push-shift g (x , p)})

-- the tower A ←id─ A ←id─ A ← … collapses onto its first term
seq-lim-id-≃ : {A : Set} → seq-lim (id {A}) ≃ A
seq-lim-id-≃ {A} = ev-zero , ((const-seq , (λ a → refl)) , (const-seq , const-seq-ev-zero))
  where
    ev-zero : seq-lim (id {A}) → A
    ev-zero (x , p) = x 0ℕ

    const-seq : A → seq-lim (id {A})
    const-seq a = (λ n → a) , (λ n → refl)

    -- path from the first term to the n-th, walking along p
    K : (x : ℕ → A) → (p : (n : ℕ) → x (succℕ n) ≡ x n) → (n : ℕ) → x 0ℕ ≡ x n
    K x p 0ℕ = refl
    K x p (succℕ n) = concat (K x p n) (inv (p n))

    const-seq-ev-zero : (s : seq-lim (id {A})) → const-seq (ev-zero s) ≡ s
    const-seq-ev-zero (x , p) = eq-seq-lim id _ _ _ _ (K x p) c
      where
        c : (n : ℕ) → concat refl (K x p n) ≡ concat (ap id (K x p (succℕ n))) (p n)
        c n = concat (left-unit _) (inv (concat (ap (λ q → concat q (p n)) (ap-id _))
                (concat (assoc (K x p n) (inv (p n)) (p n)) (concat (ap (concat (K x p n)) (left-inv (p n))) (right-unit _)))))

retract-≃-seq-lim : {A X : Set} → (i : A → X) → (r : X → A) → (H : r ∘ i ∼ id) → A ≃ seq-lim (i ∘ r)
retract-≃-seq-lim {A} {X} i r H =
  inv-≃ (concat-≃ (r* , r*-is-equiv) (concat-≃ seq-lim-ri-≃-id seq-lim-id-≃))
  where
    f : X → X
    f = i ∘ r

    -- the interleaved tower  X ←i─ A ←r─ X ←i─ A ←r─ …
    -- apply r (resp. i) to every term to pass between the two subtowers
    r* : seq-lim f → seq-lim (r ∘ i)
    r* (x , p) = (λ n → r (x n)) , (λ n → ap r (p n))

    i* : seq-lim (r ∘ i) → seq-lim f
    i* (y , q) = (λ n → i (y n)) , (λ n → ap i (q n))

    i*-r* : (s : seq-lim f) → i* (r* s) ≡ push f s
    i*-r* (x , p) = eq-seq-lim f _ _ _ _ (λ n → refl)
      λ n → concat (right-unit _) (concat (ap-comp r i (p n)) (inv (left-unit _)))

    r*-i* : (t : seq-lim (r ∘ i)) → r* (i* t) ≡ push (r ∘ i) t
    r*-i* (y , q) = eq-seq-lim (r ∘ i) _ _ _ _ (λ n → refl)
      λ n → concat (right-unit _) (concat (ap-comp i r (q n)) (inv (left-unit _)))

    -- i* is an inverse only up to push, so correct it by a shift on either side
    r*-is-equiv : is-equiv r*
    r*-is-equiv =
      ((i* ∘ shift (r ∘ i)) , λ t → concat (r*-i* (shift (r ∘ i) t)) (push-shift (r ∘ i) t)) ,
      ((shift f ∘ i*) , λ s → concat (ap (shift f) (i*-r* s)) (proj₂ (proj₂ (push-is-equiv f)) s))

    -- H : r ∘ i ∼ id becomes a path r ∘ i ≡ id; transport seq-lim along it
    seq-lim-ri-≃-id : seq-lim (r ∘ i) ≃ seq-lim (id {A})
    seq-lim-ri-≃-id = tr seq-lim (eq-htpy (r ∘ i) id H) , is-equiv-tr (eq-htpy (r ∘ i) id H)