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

choice : {A : Set} → {B : A → Set} → {C : (x : A) → B x → Set} → ((x : A) → Σ (B x) (C x)) → (Σ ((x : A) → B x) (λ f → (x : A) → C x (f x)))
choice h = (λ x → proj₁ (h x)) , λ x → proj₂ (h x)

choice-inv : {A : Set} → {B : A → Set} → {C : (x : A) → B x → Set} → (Σ ((x : A) → B x) (λ f → (x : A) → C x (f x))) → ((x : A) → Σ (B x) (C x)) 
choice-inv (f , g) x = f x , g x 

choice-equiv : {A : Set} → {B : A → Set} → {C : (x : A) → B x → Set} → is-equiv (choice {A} {B} {C})
choice-equiv {A} {B} {C} = (choice-inv , λ {(f , g) → refl}) , (choice-inv , λ {h → eq-htpy ((choice-inv ∘ choice) h) (id h) λ x → eq-pair _ _ (refl , refl)})

Π-distrib-Σ : {A : Set} → {B : A → Set} → {C : (x : A) → B x → Set} → ((x : A) → Σ (B x) (C x)) ≃ (Σ ((x : A) → B x) (λ f → (x : A) → C x (f x)))
Π-distrib-Σ {A} {B} {C} = choice , choice-equiv

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