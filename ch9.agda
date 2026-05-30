module ch9 where

open import ch8 public

infix 1 _∼_
_∼_ : {A : Set} → {B : A → Set} → (f g : (x : A) → B x) → Set
f ∼ g = (x : _) → ((f x) ≡ (g x))

neg-neg𝟚 : (neg𝟚 ∘ neg𝟚) ∼ id
neg-neg𝟚 true = refl
neg-neg𝟚 false = refl


triangle-commutes : {A B X : Set} → (f : A → X) → (h : A → B) → (g : B → X) → Set
triangle-commutes f h g = f ∼ (g ∘ h)

square-commutes : {A A' B B' : Set} → (f : A → B) → (g : A → A') → (f' : A' → B') → (g' : B → B') → Set
square-commutes f g f' g' = (g' ∘ f) ∼ (f' ∘ g)

rfl-htpy : {A : Set} → {B : A → Set} → (f : (x : A) → B x) → f ∼ f
rfl-htpy f x = refl

inv-htpy : {A : Set} → {B : A → Set} → {f g : (x : A) → B x} → f ∼ g → g ∼ f
inv-htpy f∼g x = inv (f∼g x)

concat-htpy : {A : Set} → {B : A → Set} → {f g h : (x : A) → B x } → f ∼ g → g ∼ h → f ∼ h
concat-htpy f∼g g∼h x = concat (f∼g x) (g∼h x)

assoc-htpy : {A : Set} → {B : A → Set} → {f g h i : (x : A) → B x} → (H : f ∼ g) → (K : g ∼ h) → (L : h ∼ i) → concat-htpy (concat-htpy H K) L ∼ concat-htpy H (concat-htpy K L)
assoc-htpy {A} {B} {f} {g} {h} {i} H K L x = assoc (H x) (K x) (L x)

left-unit-htpy : {A : Set} → {B : A → Set} → {f g : (x : A) → B x} → (H : f ∼ g) → concat-htpy (rfl-htpy f) H ∼ H
left-unit-htpy H x = left-unit (H x)

right-unit-htpy : {A : Set} → {B : A → Set} → {f g : (x : A) → B x} → (H : f ∼ g) → concat-htpy H (rfl-htpy g) ∼ H
right-unit-htpy H x = right-unit (H x)

left-inv-htpy : {A : Set} → {B : A → Set} → {f g : (x : A) → B x} → (H : f ∼ g) → concat-htpy (inv-htpy H) H ∼ rfl-htpy g
left-inv-htpy H x = left-inv (H x)

right-inv-htpy : {A : Set} → {B : A → Set} → {f g : (x : A) → B x} → (H : f ∼ g) → concat-htpy H (inv-htpy H) ∼ rfl-htpy f
right-inv-htpy H x = right-inv (H x)

left-whisker : {A B C : Set} → (f g : A → B) → (h : B → C) → (H : f ∼ g) → h ∘ f ∼ h ∘ g
left-whisker f g h H x = ap h (H x)

right-whisker : {A B C : Set} → (h : A → B) → (f g : B → C) → (H : f ∼ g) → f ∘ h ∼ g ∘ h
right-whisker h f g H x = H (h x)

sec : {A B : Set} → (f : A → B) → Set
sec {A} {B} f = Σ (B → A) (λ g → f ∘ g ∼ id)

retr : {A B : Set} → (f : A → B) → Set
retr {A} {B} f = Σ (B → A) (λ h → h ∘ f ∼ id)

is-equiv : {A B : Set} → (f : A → B) → Set
is-equiv f = sec f × retr f

infix 0 _≃_
_≃_ : (A B : Set) → Set
A ≃ B = Σ (A → B) (λ f → is-equiv f)

is-equiv-id : (A : Set) → is-equiv (id {A})
is-equiv-id A = (((id , λ x → refl)) , ((id , λ x → refl)))

is-equiv-neg𝟚 : is-equiv (neg𝟚)
is-equiv-neg𝟚 = (((neg𝟚 , neg-neg𝟚)) , ((neg𝟚 , neg-neg𝟚)))

is-equiv-succℤ : is-equiv (succℤ)
is-equiv-succℤ = (((predℤ , λ x → succ-predℤ x)) , ((predℤ , λ x → pred-succℤ x)))

is-equiv-predℤ : is-equiv (predℤ)
is-equiv-predℤ = ((succℤ , λ x → pred-succℤ x) , (succℤ , λ x → succ-predℤ x))

is-equiv-addℤ : (k : ℤ) → is-equiv (λ x → x +ℤ k)
is-equiv-addℤ k = ((((λ z → z -ℤ k) , λ y → concat (add-assocℤ y (-ℤ k) k) (ap (λ n → y +ℤ n) (neg-addℤ k)))) , (((λ z → z -ℤ k) , λ x → concat (add-assocℤ x k (-ℤ k)) (ap (λ n → x +ℤ n) (add-negℤ k)))))

is-equiv-negℤ : is-equiv (-ℤ_)
is-equiv-negℤ = (((-ℤ_ , λ x → neg-negℤ x)) , (((-ℤ_ , λ x → neg-negℤ x))))

zero-Fin : (k : ℕ) → Fin (succℕ k)
zero-Fin 0ℕ       = inr *
zero-Fin (succℕ k) = inl (zero-Fin k)

succ-Fin-nc : (k : ℕ) → Fin (succℕ k) → Fin (succℕ k) ⊎ 𝟙
succ-Fin-nc k       (inr *) = inr *
succ-Fin-nc 0ℕ      (inl ())
succ-Fin-nc (succℕ k) (inl x) with succ-Fin-nc k x
... | inl y = inl (inl y)
... | inr * = inl (inr *)

succ-Fin : (k : ℕ) → Fin (succℕ k) → Fin (succℕ k)
succ-Fin k x with succ-Fin-nc k x
... | inl y = y
... | inr * = zero-Fin k

succ-Fin-nc-inr : (k : ℕ) → (x : Fin (succℕ k)) → succ-Fin-nc k x ≡ inr * → x ≡ inr *
succ-Fin-nc-inr k (inr *) _ = refl
succ-Fin-nc-inr 0ℕ (inl ()) _
succ-Fin-nc-inr (succℕ k) (inl x) p with succ-Fin-nc k x
succ-Fin-nc-inr (succℕ k) (inl x) () | inl _
succ-Fin-nc-inr (succℕ k) (inl x) () | inr *

pred-Fin-nc : (k : ℕ) → Fin (succℕ k) → Fin (succℕ k) ⊎ 𝟙
pred-Fin-nc 0ℕ        (inr *)  = inr *
pred-Fin-nc (succℕ k) (inr *)  = inl (inl (inr *))
pred-Fin-nc (succℕ k) (inl x) with pred-Fin-nc k x
... | inl y = inl (inl y)
... | inr * = inr *

pred-Fin : (k : ℕ) → Fin (succℕ k) → Fin (succℕ k)
pred-Fin k x with pred-Fin-nc k x
... | inl y = y
... | inr * = inr *

pred-Fin-nc-zero : (k : ℕ) → pred-Fin-nc k (zero-Fin k) ≡ inr *
pred-Fin-nc-zero 0ℕ = refl
pred-Fin-nc-zero (succℕ k) with pred-Fin-nc k (zero-Fin k) | pred-Fin-nc-zero k
... | inr * | _ = refl
... | inl _ | ()

pred-Fin-nc-inr : (k : ℕ) → (x : Fin (succℕ k)) → pred-Fin-nc k x ≡ inr * → x ≡ zero-Fin k
pred-Fin-nc-inr 0ℕ (inr *) _ = refl
pred-Fin-nc-inr (succℕ k) (inl x) p with pred-Fin-nc k x | pred-Fin-nc-inr k x
pred-Fin-nc-inr (succℕ k) (inl x) refl | inr * | ih = ap inl (ih refl)
pred-Fin-nc-inr (succℕ k) (inl x) () | inl _ | _
pred-Fin-nc-inr (succℕ k) (inr *) ()

succ-pred-nc : (k : ℕ) → (x : Fin (succℕ k)) → (y : Fin (succℕ k))
  → pred-Fin-nc k x ≡ inl y → succ-Fin-nc k y ≡ inl x
succ-pred-nc 0ℕ (inr *) y ()
succ-pred-nc (succℕ k) (inr *) .(inl (inr *)) refl = refl
succ-pred-nc (succℕ k) (inl x) y p with pred-Fin-nc k x | succ-pred-nc k x
succ-pred-nc (succℕ k) (inl x) .(inl y') refl | inl y' | ih
  with succ-Fin-nc k y' | ih y' refl
... | inl z | q = ap inl q
... | inr * | q = ex-falso (tr (λ { (inl _) → 𝟙 ; (inr _) → 𝟘 }) (inv q) *)
succ-pred-nc (succℕ k) (inl x) y () | inr * | _

pred-succ-nc : (k : ℕ) → (x : Fin (succℕ k)) → (y : Fin (succℕ k))
  → succ-Fin-nc k x ≡ inl y → pred-Fin-nc k y ≡ inl x
pred-succ-nc 0ℕ (inr *) y ()
pred-succ-nc (succℕ k) (inr *) y ()
pred-succ-nc (succℕ k) (inl x) y p with succ-Fin-nc k x | pred-succ-nc k x | succ-Fin-nc-inr k x
pred-succ-nc (succℕ k) (inl x) .(inl y') refl | inl y' | ih | _
  with pred-Fin-nc k y' | ih y' refl
... | inl z | q = ap inl q
... | inr * | q = ex-falso (tr (λ { (inl _) → 𝟙 ; (inr _) → 𝟘 }) (inv q) *)
pred-succ-nc (succℕ k) (inl x) .(inr *) refl | inr * | _ | f
  = ap inl (ap inl (inv (f refl)))

succ-pred-Fin : (k : ℕ) → (x : Fin (succℕ k)) → succ-Fin k (pred-Fin k x) ≡ x
succ-pred-Fin k x with pred-Fin-nc k x | succ-pred-nc k x | pred-Fin-nc-inr k x
succ-pred-Fin k x | inl y | ih | _ with succ-Fin-nc k y | ih y refl
succ-pred-Fin k x | inl y | _ | _ | inl z | p = ap (λ { (inl w) → w ; (inr *) → z }) p
succ-pred-Fin k x | inl y | _ | _ | inr * | p = ex-falso (tr (λ { (inl _) → 𝟙 ; (inr _) → 𝟘 }) (inv p) *)
succ-pred-Fin k x | inr * | _ | f = inv (f refl)

pred-succ-Fin : (k : ℕ) → (x : Fin (succℕ k)) → pred-Fin k (succ-Fin k x) ≡ x
pred-succ-Fin k x with succ-Fin-nc k x | pred-succ-nc k x | succ-Fin-nc-inr k x
pred-succ-Fin k x | inl y | ih | _ with pred-Fin-nc k y | ih y refl
pred-succ-Fin k x | inl y | _ | _ | inl z | p = ap (λ { (inl w) → w ; (inr *) → z }) p
pred-succ-Fin k x | inl y | _ | _ | inr * | p = ex-falso (tr (λ { (inl _) → 𝟙 ; (inr _) → 𝟘 }) (inv p) *)
pred-succ-Fin k x | inr * | _ | f
  with pred-Fin-nc k (zero-Fin k) | pred-Fin-nc-zero k
pred-succ-Fin k x | inr * | _ | f | inr * | _ = inv (f refl)
pred-succ-Fin k x | inr * | _ | f | inl _ | p =
  ex-falso (tr (λ { (inl _) → 𝟙 ; (inr _) → 𝟘 }) p *)

is-equiv-succ-Fin : (k : ℕ) → is-equiv (succ-Fin k)
is-equiv-succ-Fin k = (pred-Fin k , succ-pred-Fin k) , (pred-Fin k , pred-succ-Fin k)

add-Fin : (k : ℕ) → ℕ → Fin (succℕ k) → Fin (succℕ k)
add-Fin k n = iterate (succ-Fin k) n

is-equiv-add-Fin : (k : ℕ) → (n : ℕ) → is-equiv (add-Fin k n)
is-equiv-add-Fin k n =
  (iterate (pred-Fin k) n , add-Fin-pred-Fin n) ,
  (iterate (pred-Fin k) n , pred-Fin-add-Fin n)
  where
    shift : (m : ℕ) → (x : Fin (succℕ k))
          → iterate (pred-Fin k) m (pred-Fin k x) ≡ pred-Fin k (iterate (pred-Fin k) m x)
    shift 0ℕ       x = refl
    shift (succℕ m) x = ap (pred-Fin k) (shift m x)
    add-Fin-pred-Fin : (m : ℕ) → (x : Fin (succℕ k)) → add-Fin k m (iterate (pred-Fin k) m x) ≡ x
    add-Fin-pred-Fin 0ℕ       x = refl
    add-Fin-pred-Fin (succℕ m) x =
      concat (ap (succ-Fin k) (concat (ap (add-Fin k m) (inv (shift m x)))
                                      (add-Fin-pred-Fin m (pred-Fin k x))))
             (succ-pred-Fin k x)
    pred-Fin-add-Fin : (m : ℕ) → (x : Fin (succℕ k)) → iterate (pred-Fin k) m (add-Fin k m x) ≡ x
    pred-Fin-add-Fin 0ℕ       x = refl
    pred-Fin-add-Fin (succℕ m) x =
      concat (inv (shift m (succ-Fin k (add-Fin k m x))))
             (concat (ap (iterate (pred-Fin k) m) (pred-succ-Fin k (add-Fin k m x)))
                     (pred-Fin-add-Fin m x))

has-inverse : {A B : Set} → (f : A → B) → Set
has-inverse {A} {B} f = Σ (B → A) (λ g → ((f ∘ g ∼ id) × (g ∘ f ∼ id)))

inverse-to-equiv : {A B : Set} → (f : A → B) → has-inverse f → is-equiv f
inverse-to-equiv f (g , (fg , gf)) = (((g , fg)) , ((g , gf)))

sec-equiv-retr : {A B : Set} → (f : A → B) → (g : sec f) → (h : retr f) → proj₁ g ∼ proj₁ h
sec-equiv-retr f (g , fg) (h , hf) = λ x → concat (inv (hf (g x))) (ap h (fg x))

equiv-to-inverse : {A B : Set} → (f : A → B) → is-equiv f → has-inverse f
equiv-to-inverse f ((g , fg) , (h , hf)) = (g , ((fg , concat-htpy (right-whisker f g h (sec-equiv-retr f (g , fg) (h , hf))) hf)))

inv-equiv-is-equiv : {A B : Set} → (f : A → B) → is-equiv f → (invf : has-inverse f) → is-equiv (proj₁ invf) 
inv-equiv-is-equiv f ((g , fg) , (h , hf)) (k , (fk , kf)) = (((f , kf)) , ((f , fk)))

𝟘-⊎ : (B : Set) → 𝟘 ⊎ B ≃ B
𝟘-⊎ B = (⊎-elim-right id , ((((inr , λ x → refl)) , ((inr , λ {(inr x) → refl})))))

⊎-𝟘 : (A : Set) → A ⊎ 𝟘 ≃ A
⊎-𝟘 A = (⊎-elim-left id , ((((inl , λ x → refl)) , ((inl , λ {(inl x) → refl})))))

⊎-symm : (A B : Set) → A ⊎ B ≃ B ⊎ A
⊎-symm A B = ((λ { (inl x) → inr x ; (inr x) → inl x}) , ((((((λ { (inl x) → inr x ; (inr x) → inl x})) , λ { (inl x) → refl ; (inr x) → refl})) , (((λ { (inl x) → inr x ; (inr x) → inl x}) , λ { (inl x) → refl ; (inr x) → refl})))))

⊎-assoc : (A B C : Set) → (A ⊎ B) ⊎ C ≃ A ⊎ (B ⊎ C)
⊎-assoc A B C = ((λ { (inl (inl x)) → inl x ; (inl (inr x)) → inr (inl x) ; (inr x) → inr (inr x)}) , (((((λ { (inl x) → inl (inl x) ; (inr (inl x)) → (inl (inr x)) ; (inr (inr x)) → inr x}) , λ { (inl x) → refl ; (inr (inl x)) → refl ; (inr (inr x)) → refl})) , (((λ { (inl x) → inl (inl x) ; (inr (inl x)) → (inl (inr x)) ; (inr (inr x)) → inr x}) , λ { (inl (inl x)) → refl ; (inl (inr x)) → refl ; (inr x) → refl})))))

𝟘-× : (B : Set) → 𝟘 × B ≃ 𝟘
𝟘-× B = ((λ { (() , _)}) , (((((λ { ()}) , λ ())) , (((λ ()) , λ { (() , _)})))))

×-𝟘 : (A : Set) → A × 𝟘 ≃ 𝟘
×-𝟘 A = ((λ {(_ , ())}) , (((((λ ()) , λ ())) , (((λ ()) , λ {(_ , ())})))))

𝟙-× : (B : Set) → 𝟙 × B ≃ B
𝟙-× B = (λ { (* , b) → b}) , (((λ x → (* , x)) , (λ x → refl)) , ((λ x → * , x) , (λ { (* , b) → refl})))

×-𝟙 : (A : Set) → A × 𝟙 ≃ A
×-𝟙  A = (λ { (a , *) → a}) , (((λ z → z , *) , (λ {x → refl})) , ((λ z → z , *) , (λ { (x , *) → refl})))

×-symm : (A B : Set) → A × B ≃ B × A
×-symm A B = (λ { (a , b) → b , a}) , (((λ { (b , a) → a , b}) , λ { (b , a) → refl}) , ((λ { (b , a) → a , b}) , λ { (a , b) → refl}))

×-assoc : (A B C : Set) → (A × B) × C ≃ A × (B × C)
×-assoc A B C = (λ {((a , b) , c) → a , (b , c)}) , (((λ { (a , (b , c)) → (a , b) , c}) , λ { (a , (b , c)) → refl}) , ((λ { (a , (b , c)) → (a , b) , c}) , λ {((a , b) , c) → refl}))

×-distrib-⊎ : (A B C : Set) → A × (B ⊎ C) ≃ (A × B) ⊎ (A × C)
×-distrib-⊎ A B C = (λ { (a , inl b) → inl (a , b) ; (a , inr c) → inr (a , c)}) , (((λ { (inl (a , b)) → a , inl b ; (inr (a , c)) → a , inr c}) , λ { (inl (a , b)) → refl ; (inr (a , c)) → refl}) , ((λ { (inl (x , x₁)) → x , inl x₁ ; (inr (x , x₁)) → x , inr x₁}) , λ { (x , inl x₁) → refl ; (x , inr x₁) → refl}))

⊎-distrib-× : (A B C : Set) → (A ⊎ B) × C ≃ (A × C) ⊎ (B × C)
⊎-distrib-× A B C = (λ { (inl x , x₁) → inl (x , x₁) ; (inr x , x₁) → inr (x , x₁)}) , (((λ { (inl (x , x₁)) → inl x , x₁ ; (inr (x , x₁)) → inr x , x₁}) , λ { (inl (x , x₁)) → refl ; (inr (x , x₁)) → refl}) , ((λ { (inl (x , x₁)) → inl x , x₁ ; (inr (x , x₁)) → inr x , x₁}) , λ { (inl x , x₁) → refl ; (inr x , x₁) → refl}))

Σ-𝟘 : (B : 𝟘 → Set) → Σ 𝟘 (λ x → B x) ≃ 𝟘
Σ-𝟘 B = (λ { (() , x₁)}) , (((λ { ()}) , λ { ()}) , ((λ ()) , λ { (() , x₁)}))

Σ-A-𝟘 : (A : Set) → Σ A (λ a → 𝟘) ≃ 𝟘
Σ-A-𝟘 A = (λ {(x , ())}) , (((λ {()}) , λ {()}) , ((λ ()) , λ {(_ , ())}))

Σ-𝟙 : (B : 𝟙 → Set) → Σ 𝟙 B ≃ B *
Σ-𝟙 B = (λ {(* , b) → b}) , (((λ {x → * , x}) , λ {x → refl}) , ((λ {x → * , x}) , λ { (* , x₁) → refl}))

Σ-A-𝟙 : (A : Set) → Σ A (λ a → 𝟙) ≃ A
Σ-A-𝟙 A = (λ { (x , *) → x}) , (((λ {x → x , *}) , λ x → refl) , ((λ z → z , *) , (λ { (x , *) → refl})))

Σ-assoc : {A : Set} → (B : A → Set) → (C : Σ A B → Set) → Σ (Σ A B) C ≃ Σ A (λ a → Σ (B a) (λ b → C (a , b)))
Σ-assoc B C = (λ { ((x , x₂) , x₁) → x , (x₂ , x₁)}) , (((λ { (x , (x₁ , x₂)) → (x , x₁) , x₂}) , λ { (x , (x₁ , x₂)) → refl}) , ((λ { (x , (x₁ , x₂)) → (x , x₁) , x₂}) , λ { ((x , x₂) , x₁) → refl}))

Σ-⊎-distrib : {A B : Set} → (C : A ⊎ B → Set)  → Σ (A ⊎ B) C ≃ Σ A (λ a → C (inl a)) ⊎ Σ B (λ b → C (inr b))
Σ-⊎-distrib C = (λ { (inl x , x₁) → inl (x , x₁) ; (inr x , x₁) → inr (x , x₁)}) , (((λ { (inl (x , x₁)) → inl x , x₁ ; (inr (x , x₁)) → inr x , x₁}) , λ { (inl (x , x₁)) → refl ; (inr (x , x₁)) → refl}) , ((λ { (inl (x , x₁)) → inl x , x₁ ; (inr (x , x₁)) → inr x , x₁}) , λ { (inl x , x₁) → refl ; (inr x , x₁) → refl}))

Σ-distrib-⊎ : {A : Set} → (B C : A → Set) → Σ A (λ a → B a ⊎ C a) ≃ Σ A B ⊎ Σ A C
Σ-distrib-⊎ B C = (λ { (x , inl x₁) → inl (x , x₁) ; (x , inr x₁) → inr (x , x₁)}) , (((λ { (inl (x , x₁)) → x , inl x₁ ; (inr (x , x₁)) → x , inr x₁}) , λ { (inl (x , x₁)) → refl ; (inr (x , x₁)) → refl}) , ((λ { (inl (x , x₁)) → x , inl x₁ ; (inr (x , x₁)) → x , inr x₁}) , λ { (x , inl x₁) → refl ; (x , inr x₁) → refl}))

Eq-Σ : {A : Set} → {B : A → Set} → (x y : Σ A B) → Set
Eq-Σ {A} {B} x y = Σ (proj₁ x ≡ proj₁ y) (λ α → tr B α (proj₂ x) ≡ proj₂ y)

rfl-Eq-Σ : {A : Set} → {B : A → Set} → (x : Σ A B) → Eq-Σ x x
rfl-Eq-Σ {A} {B} (a , b) = refl , refl

pair-eq : {A : Set} → {B : A → Set} → (s t : Σ A B) → s ≡ t → Eq-Σ s t
pair-eq {A} {B} s t refl = rfl-Eq-Σ s

pair-eq-is-equiv : {A : Set} → {B : A → Set} → (s t : Σ A B) → is-equiv (pair-eq s t)
pair-eq-is-equiv (sa , sb) (ta , tb) = ((λ { (refl , refl) → refl}) , λ { (refl , refl) → refl}) , ((λ { (refl , refl) → refl}) , λ { refl → refl})

-- Exercises
-- 9.1
is-equiv-inv : {A : Set} → (s t : A) → is-equiv (inv {A} {s} {t})
is-equiv-inv {A} s t = ((λ { refl → refl}) , λ { refl → refl}) , ((λ {refl → refl}) , λ {refl → refl})

is-equiv-concat : {A : Set} → {x y z : A} → (p : x ≡ y) → is-equiv (concat {A} {x} {y} {z} p)
is-equiv-concat refl = (id , λ {refl → refl}) , (id , λ {refl → refl})

is-equiv-concat' : {A : Set} → {a b c : A} → (q : b ≡ c) → is-equiv (λ p → concat {A} {a} {b} {c} p q)
is-equiv-concat' refl = ((λ {x → x}) , λ {refl → refl}) , ((λ {x → x}) , λ {refl → refl})

is-equiv-tr : {A : Set} → {B : A → Set} → {x y : A} → (p : x ≡ y) → is-equiv (tr B p)
is-equiv-tr refl = ((λ z → z) , (λ x₁ → refl)) , ((λ z → z) , (λ x₁ → refl))

true-ne-false : ¬ (true ≡ false)
true-ne-false ()

const-is-not-equiv : (b : 𝟚) → ¬ (is-equiv {𝟚} (const {b = b}))
const-is-not-equiv true ((g , constg) , (h , hconst)) = true-ne-false (constg false)
const-is-not-equiv false ((g , constg) , (h , hconst)) = true-ne-false (inv (constg true))

𝟚-nequiv-𝟙 : ¬ (𝟚 ≃ 𝟙)
𝟚-nequiv-𝟙 (f , ((g , fg) , (h , hf))) = true-ne-false (concat (inv (hf true)) (concat (ap h (indUnit {P = λ u → u ≡ f false} (indUnit {P = λ u → * ≡ u} refl (f false)) (f true))) (hf false)))

≤-left-maxℕ : (m n : ℕ) → m ≤ℕ maxℕ m n
≤-left-maxℕ 0ℕ 0ℕ = *
≤-left-maxℕ 0ℕ (succℕ n) = *
≤-left-maxℕ (succℕ m) 0ℕ = ≤-rflℕ m
≤-left-maxℕ (succℕ m) (succℕ n) = ≤-left-maxℕ m n

≤-right-maxℕ : (m n : ℕ) → n ≤ℕ maxℕ m n
≤-right-maxℕ 0ℕ 0ℕ = *
≤-right-maxℕ 0ℕ (succℕ n) = ≤-rflℕ n
≤-right-maxℕ (succℕ m) 0ℕ = *
≤-right-maxℕ (succℕ m) (succℕ n) = ≤-right-maxℕ m n

maxFin : (k : ℕ) → (Fin (succℕ k) → ℕ) → ℕ
maxFin 0ℕ f = f (inr *)
maxFin (succℕ k) f = maxℕ (maxFin k (λ x → f (inl x))) (f (inr *))

maxFin-ub : (k : ℕ) → (f : Fin (succℕ k) → ℕ) → (x : Fin (succℕ k)) → f x ≤ℕ maxFin k f
maxFin-ub 0ℕ f (inr *) = ≤-rflℕ (f (inr *))
maxFin-ub (succℕ k) f (inl x) = ≤-transℕ {f (inl x)} {maxFin k (λ z → f (inl z))} {maxℕ (maxFin k (λ z → f (inl z))) (f (inr *))} (maxFin-ub k (λ z → f (inl z)) x) (≤-left-maxℕ (maxFin k (λ z → f (inl z))) (f (inr *)))
maxFin-ub (succℕ k) f (inr *) = ≤-right-maxℕ (maxFin k (λ z → f (inl z))) (f (inr *))

succ-≰-selfℕ : (m : ℕ) → ¬ (succℕ m ≤ℕ m)
succ-≰-selfℕ m p = <-to-≱ m (succℕ m) (<-succℕ m) p

ℕ-nequiv-Fin : (k : ℕ) → ¬ (ℕ ≃ Fin k)
ℕ-nequiv-Fin 0ℕ (f , _) = f 0ℕ
ℕ-nequiv-Fin (succℕ k) (f , ((g , fg) , (h , hf))) = succ-≰-selfℕ (maxFin k g) (tr (_≤ℕ maxFin k g) (concat (sec-equiv-retr f (g , fg) (h , hf) (f (succℕ (maxFin k g)))) (hf (succℕ (maxFin k g)))) (maxFin-ub k g (f (succℕ (maxFin k g)))))

htpy-of-equiv-is-equiv : {A B : Set} → (f g : A → B) → (H : f ∼ g) → is-equiv f → is-equiv g
htpy-of-equiv-is-equiv f g H ((h , fh) , (k , kf)) = (h , concat-htpy (right-whisker h g f (inv-htpy H)) fh) , (k , concat-htpy (left-whisker g f k (inv-htpy H)) kf)

htpy-to-inv-htpy : {A B : Set} → (f g : A → B) → (H : f ∼ g) → (finv : has-inverse f) → (ginv : has-inverse g) → proj₁ finv ∼ proj₁ ginv
htpy-to-inv-htpy f g H (h , (fh , hf)) (k , (fk , kf)) = λ x → concat (ap h (inv (fk x))) (concat (ap h (inv (H (k x)))) (hf (k x)))

comm-tri-sec-h-to-comm-tri : {A B X : Set} → (f : A → X) → (g : B → X) → (h : A → B) → triangle-commutes f h g → (sech : sec h) → triangle-commutes g (proj₁ sech) f
comm-tri-sec-h-to-comm-tri f g h comm (s , hs) = λ x → inv (concat (comm (s x)) (ap g (hs x)))

comm-tri-sec-h-to-sec-f-iff-sec-g : {A B X : Set} → (f : A → X) → (g : B → X) → (h : A → B) → triangle-commutes f h g → (sech : sec h) → (sec f ↔ sec g)
comm-tri-sec-h-to-sec-f-iff-sec-g f g h comm (s , hs) = (λ {(k , fk) → (h ∘ k) , concat-htpy (right-whisker k (g ∘ h) f (inv-htpy comm)) fk}) , λ {(k , gk) → (s ∘ k) , concat-htpy (right-whisker k (f ∘ s) g (inv-htpy (comm-tri-sec-h-to-comm-tri f g h comm (s , hs)))) gk}

comm-tri-retr-g-to-comm-tri : {A B X : Set} → (f : A → X) → (g : B → X) → (h : A → B) → triangle-commutes f h g → (retg : retr g) → triangle-commutes h f (proj₁ retg)
comm-tri-retr-g-to-comm-tri f g h comm (r , rg) = λ x → inv (concat (ap r (comm x)) (rg (h x)))

comm-tri-retr-g-to-retr-f-iff-retr-h : {A B X : Set} → (f : A → X) → (g : B → X) → (h : A → B) → triangle-commutes f h g → (retg : retr g) → (retr f ↔ retr h)
comm-tri-retr-g-to-retr-f-iff-retr-h f g h comm (r , rg) = (λ {(k , kf) → (k ∘ g) , concat-htpy (λ x → ap k (inv (comm x))) kf}) , λ {(k , kh) → (k ∘ r) , concat-htpy (λ x → ap k (inv (comm-tri-retr-g-to-comm-tri f g h comm (r , rg) x))) kh}


3-for-2-f-g-to-h : {A B X : Set} → (f : A → X) → (g : B → X) → (h : A → B) → triangle-commutes f h g → is-equiv f → is-equiv g → is-equiv h
3-for-2-f-g-to-h f g h comm ((s , fs) , (r , rf)) ((s' , gs') , (r' , r'g)) =
  ((s ∘ g) , λ b → concat (inv (r'g (h (s (g b))))) (concat (ap r' (concat (inv (comm (s (g b)))) (fs (g b)))) (r'g b))) ,
  ((r ∘ g) , λ a → concat (ap r (inv (comm a))) (rf a))

3-for-2-f-h-to-g : {A B X : Set} → (f : A → X) → (g : B → X) → (h : A → B) → triangle-commutes f h g → is-equiv f → is-equiv h → is-equiv g
3-for-2-f-h-to-g f g h comm ((s , fs) , (r , rf)) ((s' , hs') , (r' , r'h)) =
  ((h ∘ s) , λ x → concat (inv (comm (s x))) (fs x)) ,
  ((h ∘ r) , λ b → concat (inv (ap h (sec-equiv-retr h (s' , hs') ((r ∘ g) , retr-h) b))) (hs' b))
  where retr-h = λ a → concat (ap r (inv (comm a))) (rf a)

3-for-2-g-h-to-f : {A B X : Set} → (f : A → X) → (g : B → X) → (h : A → B) → triangle-commutes f h g → is-equiv g → is-equiv h → is-equiv f
3-for-2-g-h-to-f f g h comm ((s , gs) , (r , rg)) ((s' , hs') , (r' , r'h)) =
  ((s' ∘ s) , λ x → concat (comm (s' (s x))) (concat (ap g (hs' (s x))) (gs x))) ,
  ((r' ∘ r) , λ a → concat (ap r' (ap r (comm a))) (concat (ap r' (rg (h a))) (r'h a)))

Σ-swap : {A B : Set} → (C : A → B → Set) → Σ A (λ a → Σ B (λ b → C a b)) ≃ Σ B (λ b → Σ A (λ a → C a b))
Σ-swap C = (λ { (a , (b , c)) → b , (a , c)}) , (((λ {(b , (a , c)) → a , (b , c)}) , λ {(b , (a , c)) → refl}) , (((λ {(b , (a , c)) → a , (b , c)}) , λ {(b , (a , c)) → refl})))

Σ-Σ-swap : {A : Set} → (B C : A → Set) → Σ (Σ A B) (λ b → C (proj₁ b)) ≃ Σ (Σ A C) (λ c → B (proj₁ c))
Σ-Σ-swap B C = (λ { ((a , b) , c) → (a , c) , b}) , (((λ { ((a , c) , b) → (a , b) , c}) , λ {((a , c) , b) → refl}) , (((λ { ((a , c) , b) → (a , b) , c}) , λ {((a , c) , b) → refl})))

infix 1 _⊎'_
_⊎'_ : {A B A' B' : Set} → (f : A → A') → (g : B → B') → A ⊎ B → A' ⊎ B'
(f ⊎' g) (inl x) = inl (f x)
(f ⊎' g) (inr x) = inr (g x)

id⊎id-equiv-id : {A B : Set} → ((id {A}) ⊎' (id {B})) ∼ id {A ⊎ B}
id⊎id-equiv-id = λ { (inl x) → refl ; (inr x) → refl}

∘⊎∘-equiv-⊎∘⊎ : {A A' A'' B B' B'' : Set} → (f : A → A') → (f' : A' → A'') → (g : B → B') → (g' : B' → B'') → ((f' ∘ f) ⊎' (g' ∘ g)) ∼ (f' ⊎' g') ∘ (f ⊎' g)
∘⊎∘-equiv-⊎∘⊎ f f' g g' = λ { (inl x) → refl ; (inr x) → refl}

infix 1 _⊎∼_
_⊎∼_ : {A B C D : Set} → {f f' : A → C} → {g g' : B → D} → (H : f ∼ f') → (K : g ∼ g') → (f ⊎' g) ∼ (f' ⊎' g')
H ⊎∼ K = λ { (inl x) → ap inl (H x) ; (inr x) → ap inr (K x)}

equiv⊎equiv-to-equiv : {A B C D : Set} → (f : A → C) → (g : B → D) → is-equiv f → is-equiv g → is-equiv (f ⊎' g)
equiv⊎equiv-to-equiv f g ((s , fs) , (r , rf)) ((t , gt) , (q , qg)) = ((s ⊎' t) , λ { (inl x) → ap inl (fs x) ; (inr x) → ap inr (gt x)}) , ((r ⊎' q) , λ { (inl x) → ap inl (rf x) ; (inr x) → ap inr (qg x)})

infix 1 _×'_
_×'_ : {A B C D : Set} → (f : A → B) → (g : C → D) → A × C → B × D
(f ×' g) (x , y) = (f x) , (g y)

id×id-equiv-id : {A B : Set} → (id {A} ×' id {B}) ∼ id 
id×id-equiv-id = λ { (x , x₁) → refl}

∘×∘-equiv-×∘× : {A A' A'' B B' B'' : Set} → (f : A → A') → (f' : A' → A'') → (g : B → B') → (g' : B' → B'') → ((f' ∘ f) ×' (g' ∘ g)) ∼ (f' ×' g') ∘ (f ×' g)
∘×∘-equiv-×∘× f f' g g' = λ { (a , b) → refl}

infix 1 _×∼_
_×∼_ : {A B C D : Set} → {f f' : A → C} → {g g' : B → D} → (H : f ∼ f') → (K : g ∼ g') → (f ×' g) ∼ (f' ×' g')
(H ×∼ K) (a , b) = concat (ap (λ x → x , _) (H a)) (ap (λ y → _ , y) (K b))

equiv×equiv-to-equiv : {A B A' B' : Set} → (f : A → A') → (g : B → B') → is-equiv f → is-equiv g → is-equiv (f ×' g)
equiv×equiv-to-equiv f g ((s , fs) , (r , rf)) ((t , gt) , (q , qg)) = ((λ { (a' , b') → s a' , t b'}) , λ { (a , b) → (fs ×∼ gt) (a , b)}) , ((r ×' q) , λ {(a , b) → (rf ×∼ qg) (a , b)})

×'-proj₁ : {A B C D : Set} → (f : A → C) → (g : B → D) → (p : A × B) → proj₁ ((f ×' g) p) ≡ f (proj₁ p)
×'-proj₁ f g (a , b) = refl

×'-proj₂ : {A B C D : Set} → (f : A → C) → (g : B → D) → (p : A × B) → proj₂ ((f ×' g) p) ≡ g (proj₂ p)
×'-proj₂ f g (a , b) = refl

η-pair : {A : Set} → {B : A → Set} → (p : Σ A B) → (proj₁ p , proj₂ p) ≡ p
η-pair (a , b) = refl

×'-equiv-to-fiberwise-equiv : {A B A' B' : Set} → (f : A → A') → (g : B → B') → is-equiv (f ×' g) → (B → is-equiv f) × (A → is-equiv g)
×'-equiv-to-fiberwise-equiv f g ((s , fgs) , (r , rfg)) =
  (λ b → ((λ a' → proj₁ (s (a' , g b))) ,
           (λ a' → concat (inv (×'-proj₁ f g (s (a' , g b)))) (ap proj₁ (fgs (a' , g b))))) ,
          ((λ a' → proj₁ (r (a' , g b))) ,
           (λ a → ap proj₁ (rfg (a , b))))) ,
  (λ a → ((λ b' → proj₂ (s (f a , b'))) ,
           (λ b' → concat (inv (×'-proj₂ f g (s (f a , b')))) (ap proj₂ (fgs (f a , b'))))) ,
          ((λ b' → proj₂ (r (f a , b'))) ,
           (λ b → ap proj₂ (rfg (a , b)))))

fiberwise-equiv-to-×'-equiv : {A B A' B' : Set} → (f : A → A') → (g : B → B') → A → B → (B → is-equiv f) × (A → is-equiv g) → is-equiv (f ×' g)
fiberwise-equiv-to-×'-equiv f g a₀ b₀ (α , β) = equiv×equiv-to-equiv f g (α b₀) (β a₀)

inv-≃ : {A B : Set} → A ≃ B → B ≃ A
inv-≃ (f , ef) = (proj₁ invf , inv-equiv-is-equiv f ef invf)
  where invf = equiv-to-inverse f ef

concat-≃ : {A B C : Set} → A ≃ B → B ≃ C → A ≃ C
concat-≃ (f , ((sf , fsf) , (rf , rff))) (g , ((sg , gsg) , (rg , rgg))) =
  ((g ∘ f) , (((sf ∘ sg) , λ x → concat (ap g (fsf (sg x))) (gsg x)) ,
              ((rf ∘ rg) , λ x → concat (ap rf (rgg (f x))) (rff x))))

⊎-equiv-right : {A B B' : Set} → B ≃ B' → (A ⊎ B) ≃ (A ⊎ B')
⊎-equiv-right (g , eg) = ((id ⊎' g) , equiv⊎equiv-to-equiv id g (is-equiv-id _) eg)

⊎-equiv-left : {A A' B : Set} → A ≃ A' → (A ⊎ B) ≃ (A' ⊎ B)
⊎-equiv-left (f , ef) = ((f ⊎' id) , equiv⊎equiv-to-equiv f id ef (is-equiv-id _))

×-equiv-right : {A B B' : Set} → B ≃ B' → (A × B) ≃ (A × B')
×-equiv-right (g , eg) = ((id ×' g) , equiv×equiv-to-equiv id g (is-equiv-id _) eg)

×-equiv-left : {A A' B : Set} → A ≃ A' → (A × B) ≃ (A' × B)
×-equiv-left (f , ef) = ((f ×' id) , equiv×equiv-to-equiv f id ef (is-equiv-id _))

Fin-add-equiv-⊎ : (k l : ℕ) → Fin (k +ℕ l) ≃ (Fin k ⊎ Fin l)
Fin-add-equiv-⊎ k 0ℕ = (inl , (((λ { (inl x) → x }) , λ { (inl x) → refl }) , ((λ { (inl x) → x }) , λ x → refl)))
Fin-add-equiv-⊎ k (succℕ l) = concat-≃ (⊎-equiv-left (Fin-add-equiv-⊎ k l)) (⊎-assoc (Fin k) (Fin l) 𝟙)

Fin-mul-equiv-× : (k l : ℕ) → Fin (k ·ℕ l) ≃ (Fin k × Fin l)
Fin-mul-equiv-× k 0ℕ = inv-≃ (×-𝟘 (Fin k))
Fin-mul-equiv-× k (succℕ l) =
  concat-≃ (Fin-add-equiv-⊎ k (k ·ℕ l))
  (concat-≃ (⊎-equiv-right (Fin-mul-equiv-× k l))
  (concat-≃ (⊎-equiv-left (inv-≃ (×-𝟙 (Fin k))))
  (concat-≃ (inv-≃ (×-distrib-⊎ (Fin k) 𝟙 (Fin l)))
              (×-equiv-right (⊎-symm 𝟙 (Fin l))))))

{-
is-finitely-cyclic : {X : Set} → (f : X → X) → Set
is-finitely-cyclic {X} f = (x y : X) → Σ ℕ (λ k → iterate f k x ≡ y)

-- Proof idea: for each x, fincyc x x produces k with iterate f k x ≡ x — a
-- "period" of x. Define the inverse as g x := iterate f (k - 1) x, so that
--   f (g x) = iterate f k x ≡ x        (section side)
--   g (f x) = iterate f (k - 1) (f x)
--           = iterate f k x ≡ x        (retraction side, using iterate-shift)
-- Caveat: distℕ k 1 only equals k - 1 when k ≥ 1. The k = 0 case means
-- x ≡ x in zero steps; handle it separately, or upgrade fincyc to always
-- return k > 0 (which is always possible since you can add the period).
fin-cyc-to-equiv : {X : Set} → (f : X → X) → is-finitely-cyclic f → is-equiv f
fin-cyc-to-equiv f fincyc = ((λ x → iterate f (distℕ (proj₁ (fincyc x x)) 1ℕ) x) , λ {x → {!!}}) , {!!}
-}
