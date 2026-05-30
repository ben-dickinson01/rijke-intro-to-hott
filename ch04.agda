module ch04 where

open import ch03 public

data Unit : Set where
  * : Unit

𝟙 = Unit

indUnit : {P : Unit → Set} → (P *) → (x : Unit) → P x
indUnit Pstar * = Pstar

data Empty : Set where

𝟘 = Empty

indEmpty : {P : Empty → Set} → (x : Empty) → P x
indEmpty ()

ex-falso : {A : Set} → Empty → A
ex-falso ()

¬ : Set → Set
¬ A = A → Empty

is-empty : Set → Set
is-empty A = A → Empty

contrapositive : {P Q : Set} → (P → Q) → (¬ Q → ¬ P)
contrapositive {P} {Q} f nQ p = nQ (f p)

infixr 1 _⊎_
data _⊎_ (A B : Set) : Set where
 inl : A → A ⊎ B
 inr : B → A ⊎ B

ind⊎ : {A B : Set} → {P : A ⊎ B → Set} →
  ((x : A) → P (inl x)) → ((y : B) → P (inr y)) → (z : A ⊎ B) → P z
ind⊎ {A} {B} {P} fA fB (inl x) = fA x
ind⊎ {A} {B} {P} fA fB (inr y) = fB y

⊎functor : {A B A' B' : Set} → (f : A → A') → (g : B → B') →
  (A ⊎ B → A' ⊎ B')
⊎functor f g (inl x) = inl (f x)
⊎functor f g (inr y) = inr (g y)

⊎-elim-right : {A B : Set} → ¬ A → (A ⊎ B) → B
⊎-elim-right na (inl x) = ex-falso (na x)
⊎-elim-right na (inr y) = y

⊎-elim-left : {A B : Set} → ¬ B → (A ⊎ B) → A
⊎-elim-left nb (inl a) = a
⊎-elim-left nb (inr b) = ex-falso (nb b)


data ℤ : Set where
  0ℤ : ℤ
  in-neg : ℕ → ℤ
  in-pos : ℕ → ℤ



-1ℤ 1ℤ : ℤ

-1ℤ = in-neg 0ℕ
1ℤ = in-pos 0ℕ

int-nat : ℕ → ℤ
int-nat 0ℕ = 0ℤ
int-nat (succℕ n) = in-pos n

indℤ :
  {P : ℤ → Set} →
  P -1ℤ → ((n : ℕ) → (P (in-neg n)) → (P (in-neg (succℕ n)))) →
  P 0ℤ →
  P 1ℤ → ((n : ℕ) → (P (in-pos n)) → P (in-pos (succℕ n))) →
  (k : ℤ) → P k
indℤ P-1 fneg P0 P1 fpos (in-neg 0ℕ) = P-1
indℤ {P} P-1 fneg P0 P1 fpos (in-neg (succℕ x)) =
  fneg x (indℤ {P} P-1 fneg P0 P1 fpos (in-neg x))
indℤ {P} P-1 fneg P0 P1 fpos (0ℤ) = P0
indℤ {P} P-1 fneg P0 P1 fpos (in-pos 0ℕ) = P1
indℤ {P} P-1 fneg P0 P1 fpos (in-pos (succℕ x)) =
  fpos x (indℤ {P} P-1 fneg P0 P1 fpos (in-pos x))

succℤ : ℤ → ℤ
succℤ 0ℤ = 1ℤ
succℤ (in-neg 0ℕ) = 0ℤ
succℤ (in-neg (succℕ x)) = in-neg x
succℤ (in-pos x) = in-pos (succℕ x)

data Σ (A : Set) (B : A → Set) : Set where
  _,_ : (x : A) → (B x → Σ A B)


indΣ : {A : Set} → {B : A → Set} → {P : Σ A B → Set} →
  ((x : A) → (y : B x) → P (x , y)) →
  ((z : Σ A B) → P z)
indΣ fxy (a , b) = fxy a b

proj₁ : {A : Set} → {B : A → Set} → Σ A B → A
proj₁ (x , y) = x

proj₂ : {A : Set} → {B : A → Set} → (z : Σ A B) → B (proj₁ z)
proj₂ (x , y) = y

infixr 2 _×_
_×_ : (A B : Set) → Set
A × B = Σ A (λ _ → B)

ind× : {A B : Set} → {P : A × B → Set} →
  ((x : A) → (y : B) → P (x , y)) → ((z : A × B) → P z)
ind× f (a , b) = f a b


-- Exercises
-- 4.1

predℤ : ℤ → ℤ
predℤ 0ℤ = -1ℤ
predℤ (in-neg x) = in-neg (succℕ x)
predℤ (in-pos 0ℕ) = 0ℤ
predℤ (in-pos (succℕ x)) = in-pos x

infixl 6 _+ℤ_
_+ℤ_ : ℤ → ℤ → ℤ
x +ℤ 0ℤ = x
x +ℤ in-neg 0ℕ = predℤ x
x +ℤ in-neg (succℕ y) = predℤ (x +ℤ in-neg y)
x +ℤ in-pos 0ℕ = succℤ x
x +ℤ in-pos (succℕ y) = succℤ (x +ℤ in-pos y)

infix 11 -ℤ_
-ℤ_ : ℤ → ℤ
-ℤ 0ℤ = 0ℤ
-ℤ (in-neg x) = in-pos x
-ℤ (in-pos x) = in-neg x

infixl 7 _·ℤ_
_·ℤ_ : ℤ → ℤ → ℤ
x ·ℤ 0ℤ = 0ℤ
x ·ℤ in-neg 0ℕ = -ℤ x
x ·ℤ in-neg (succℕ y) = -ℤ x +ℤ x ·ℤ in-neg y
x ·ℤ in-pos 0ℕ = x
x ·ℤ in-pos (succℕ y) = x +ℤ x ·ℤ in-pos y

data Bool : Set where
  true false : Bool

𝟚 = Bool

ind𝟚 : {P : 𝟚 → Set} → P false → P true → (b : 𝟚) → P b
ind𝟚 pf pt true = pt
ind𝟚 pf pt false = pf

neg𝟚 : 𝟚 → 𝟚
neg𝟚 true = false
neg𝟚 false = true

infixr 3 _∧𝟚_
_∧𝟚_ : 𝟚 → 𝟚 → 𝟚
b ∧𝟚 true = b
b ∧𝟚 false = false

infixr 2 _∨𝟚_
_∨𝟚_ : 𝟚 → 𝟚 → 𝟚
b ∨𝟚 true = true
b ∨𝟚 false = b

infix 3 _↔_
_↔_ : Set → Set → Set
P ↔ Q = (P → Q) × (Q → P)

ex-4-3-a : {P : Set} → ¬ (P × ¬ P)
ex-4-3-a (p , np) = ex-falso (np p)

ex-4-3-b : {P : Set} → ¬ (P ↔ ¬ P)
ex-4-3-b {P} (x , y) = f p
  where
  f : ¬ P
  f p = x p p

  p : P
  p = y f

ex-4-3-b-i : {P : Set} → P → ¬ (¬ P)
ex-4-3-b-i p np = np p

dni = ex-4-3-b-i

¬¬ : Set → Set
¬¬ P = ¬ (¬ P)

¬¬¬ : Set → Set
¬¬¬ P = ¬ (¬¬ P)

ex-4-3-b-ii : {P Q : Set} → (P → Q) → (¬¬ P → ¬¬ Q)
ex-4-3-b-ii f = contrapositive (contrapositive f)

dn-functor = ex-4-3-b-ii

ex-4-3-b-iii : {P Q : Set} → (P → ¬¬ Q) → (¬¬ P → ¬¬ Q)
ex-4-3-b-iii f nnp nq = nnp λ p → f p nq

ex-4-3-c-i : {P : Set} → ¬¬ (¬¬ P → P)
ex-4-3-c-i {P} f = f (λ nnp → ex-falso (nnp (λ p → f (λ _ → p))))

ex-4-3-c-ii : {P Q : Set} → ¬¬ (((P → Q) → P) → P)
ex-4-3-c-ii f = f (λ pqp → pqp λ p → ex-falso (f λ _ → p))

ex-4-3-c-iii : {P Q : Set} → ¬¬ ((P → Q) ⊎ (Q → P))
ex-4-3-c-iii f = f (inr λ q → ex-falso (f (inl λ p → q)))

ex-4-3-c-iv : {P : Set} → ¬¬ (P ⊎ ¬ P)
ex-4-3-c-iv f = f (inr λ p → f (inl p))

ex-4-3-d-i : {P : Set} → (P ⊎ ¬ P) → (¬¬ P → P)
ex-4-3-d-i (inl p) nnp = p
ex-4-3-d-i (inr np) nnp = ex-falso (nnp np)

ex-4-3-d-ii : {P Q : Set} → ¬¬ (Q → P) ↔ ((P ⊎ ¬ P) → (Q → P))
ex-4-3-d-ii {P} {Q} = (to , from)
  where
  to : {P Q : Set} → ¬¬ (Q → P) → ((P ⊎ ¬ P) → Q → P)
  to nnqp (inl p) q = p
  to nnqp (inr np) q = ex-falso (nnqp λ f → np (f q))

  from : {P Q : Set} → ((P ⊎ ¬ P) → Q → P) → ¬¬ (Q → P)
  from f nqp = nqp (f (inr λ p → nqp (f (inl p))))

ex-4-3-e-i : {P : Set} → ¬¬¬ P → ¬ P
ex-4-3-e-i nnnp p = nnnp λ np → np p

ex-4-3-e-ii : {P Q : Set} → ¬¬ (P → ¬¬ Q) → (P → ¬¬ Q)
ex-4-3-e-ii f p nq = f λ pnnq → pnnq p nq

ex-4-3-e-iii : {P Q : Set} → ¬¬ ((¬¬ P) × (¬¬ Q)) → (¬¬ P) × (¬¬ Q)
ex-4-3-e-iii x = ((λ np → x λ y → proj₁ y np) , λ nq → x λ y → proj₂ y nq)

ex-4-3-f-i : {P Q : Set} → ¬¬ (P × Q) ↔ ((¬¬ P) × (¬¬ Q))
ex-4-3-f-i = (to , from)
  where
  to : {P Q : Set} → ¬¬ (P × Q) → (¬¬ P) × (¬¬ Q)
  to f = ((λ np → f λ pq → np (proj₁ pq)) , λ nq → f λ pq → nq (proj₂ pq))

  from : {P Q : Set} → ((¬¬ P) × (¬¬ Q)) → ¬¬ (P × Q)
  from (nnp , nnq) f = nnp λ p → nnq λ q → f ((p , q))

ex-4-3-f-ii : {P Q : Set} → ¬¬ (P ⊎ Q) ↔ ¬ (¬ P × ¬ Q)
ex-4-3-f-ii = (to , from) where
  to : {P Q : Set} → ¬¬ (P ⊎ Q) → ¬ (¬ P × ¬ Q)
  to f npnq = f λ where
    (inl p) → proj₁ npnq p
    (inr q) → proj₂ npnq q

  from : {P Q : Set} → ¬ (¬ P × ¬ Q) → ¬¬ (P ⊎ Q)
  from f npuq = f ((λ p → npuq (inl p)) , λ q → npuq (inr q))

ex-4-3-f-iii : {P Q : Set} → ¬¬ (P → Q) ↔ (¬¬ P → ¬¬ Q)
ex-4-3-f-iii = (to , from) where
  to : {P Q : Set} → ¬¬ (P → Q) → (¬¬ P → ¬¬ Q)
  to nnpq nnp nq = nnp λ p → nnpq λ f → nq (f p)

  from : {P Q : Set} → (¬¬ P → ¬¬ Q) → ¬¬ (P → Q)
  from f npq = npq (λ p → ex-falso (f (λ np → np p) λ q → npq λ _ → q))

infixr 7 _∷_

data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

indList : {A : Set} → {P : List A → Set} →
  P [] → ((lst : List A) → (a : A) → P lst → P (a ∷ lst)) →
  (lst : List A) → P lst
indList P0 f [] = P0
indList P0 f (a ∷ lst) = f lst a (indList P0 f lst)

fold-List : {A B : Set} → {b : B} → (μ : A → B → B) → List A → B
fold-List {b = b} μ [] = b
fold-List {b = b} μ (x ∷ lst) = μ x (fold-List {b = b} μ lst)

map-List : {A B : Set} → (A → B) → List A → List B
map-List f [] = []
map-List f (x ∷ lst) = (f x) ∷ (map-List f lst)

length-List : {A : Set} → List A → ℕ
length-List [] = 0ℕ
length-List (x ∷ lst) = succℕ (length-List lst)

sum-List : List ℕ → ℕ
sum-List [] = 0ℕ
sum-List (x ∷ lst) = x +ℕ sum-List lst

prod-List : List ℕ → ℕ
prod-List [] = 1ℕ
prod-List (x ∷ lst) = x ·ℕ prod-List lst

concat-List : {A : Set} → List A → List A → List A
concat-List [] lst2 = lst2
concat-List (x ∷ lst1) lst2 = x ∷ concat-List lst1 lst2

flatten-List : {A : Set} → List (List A) → List A
flatten-List [] = []
flatten-List (lst ∷ lst₁) = concat-List lst (flatten-List lst₁)

reverse-List : {A : Set} → List A → List A
reverse-List [] = []
reverse-List (x ∷ lst) = concat-List (reverse-List lst) (x ∷ [])
