module ch05 where

open import ch04 public

infix 4 _≡_
data _≡_ {A : Set} (a : A) : A → Set where
  refl : a ≡ a

ind≡ : {A : Set} → {a : A} → {P : (x : A) →  a ≡ x → Set} → P a refl → (x : A) → (p : a ≡ x) → P x p
ind≡ pa x refl = pa

concat : {A : Set} → {x y z : A} → x ≡ y → y ≡ z → x ≡ z
concat refl refl = refl

inv : {A : Set} → {x y : A} → x ≡ y → y ≡ x
inv refl = refl

assoc : {A : Set} → {x y z w : A} → (p : x ≡ y) → (q : y ≡ z) → (r : z ≡ w) → concat (concat p q) r ≡ concat p (concat q r)
assoc refl refl refl = refl

left-unit : {A : Set} → {x y : A} → (p : x ≡ y) → ((concat refl p) ≡ p)
left-unit refl = refl

right-unit : {A : Set} → {x y : A} → (p : x ≡ y) → ((concat p refl) ≡ p)
right-unit refl = refl

left-inv : {A : Set} → {x y : A} → (p : x ≡ y) → concat (inv p) p ≡ refl
left-inv refl = refl

right-inv : {A : Set} → {x y : A} → (p : x ≡ y) → concat p (inv p) ≡ refl
right-inv refl = refl

ap : {A B : Set} → (f : A → B) → {x y : A} → (x ≡ y) → (f x ≡ f y)
ap f refl = refl

ap-id : {A : Set} → {a x : A} → (p : a ≡ x) → ap id p ≡ p
ap-id {A} {a} {x} refl = refl

ap-comp : {A B C : Set} → {x y : A} → (f : A → B) → (g : B → C) → (p : x ≡ y) → ap g (ap f p) ≡ ap (g ∘ f) p
ap-comp f g refl = refl

ap-refl : {A B : Set} → (f : A → B) → (x : A) → ap f {x} refl ≡ refl
ap-refl f x = refl

ap-inv : {A B : Set} → {x y : A} → (f : A → B) → (p : x ≡ y) → ap f (inv p) ≡ inv (ap f p)
ap-inv f refl = refl

ap-concat : {A B : Set} → {x y z : A} → (f : A → B) → (p : x ≡ y) → (q : y ≡ z) → ap f (concat p q) ≡ concat (ap f p) (ap f q)
ap-concat f refl refl = refl

tr : {A : Set} → {x y : A} → (B : A → Set) → (p : x ≡ y) → B x → B y
tr B refl bx = bx

apd : {A : Set} → {x y : A} → {B : A → Set} → (f : (a : A) → B a) → (p : x ≡ y) → tr B p (f x) ≡ f y
apd f refl = refl

refl-unique : {A : Set} → (a x : A) → (p : a ≡ x) → _≡_ {Σ A (λ z → a ≡ z)} (a , refl) (x , p)
refl-unique a .a refl = refl

-- Laws of +ℕ
zero-addℕ : (n : ℕ) → (0ℕ +ℕ n) ≡ n
zero-addℕ 0ℕ = refl
zero-addℕ (succℕ n) = ap succℕ (zero-addℕ n)

add-zeroℕ : (n : ℕ) → n +ℕ 0ℕ ≡ n
add-zeroℕ n = refl

succ-addℕ : (m n : ℕ) → succℕ m +ℕ n ≡ succℕ (m +ℕ n)
succ-addℕ m 0ℕ = refl
succ-addℕ m (succℕ n) = ap succℕ (succ-addℕ m n)

add-succℕ : (m n : ℕ) → m +ℕ succℕ n ≡ succℕ (m +ℕ n)
add-succℕ m n = refl

add-assocℕ : (m n k : ℕ) → (m +ℕ n) +ℕ k ≡ m +ℕ (n +ℕ k)
add-assocℕ m n 0ℕ = refl
add-assocℕ m n (succℕ k) = ap succℕ (add-assocℕ m n k)

add-commℕ : (m n : ℕ) → m +ℕ n ≡ n +ℕ m
add-commℕ m 0ℕ = inv (zero-addℕ m)
add-commℕ m (succℕ n) = inv (concat (succ-addℕ n m) (ap succℕ (add-commℕ n m)))

-- Exercises
distrib-inv-concat : {A : Set} → {x y z : A} → (p : x ≡ y) → (q : y ≡ z) → inv (concat p q) ≡ concat (inv q) (inv p)
distrib-inv-concat refl refl = refl

inv-con : {A : Set} → {x y z : A} → (p : x ≡ y) → (q : y ≡ z) → (r : x ≡ z) → concat p q ≡ r → q ≡ concat (inv p) r
inv-con refl refl refl refl = refl

con-inv : {A : Set} → {x y z : A} → (p : x ≡ y) → (q : y ≡ z) → (r : x ≡ z) → concat p q ≡ r → p ≡ concat r (inv q)
con-inv refl refl refl refl = refl

lift : {A : Set} → {a x : A} → (B : A → Set) → (p : a ≡ x) → (b : B a) → (a , b) ≡ (x , tr B p b)
lift B refl b = refl

-- Mac Lane Pentagon
-- Use p is refl for all proofs

-- Laws of ·ℕ
mul-zeroℕ : (m : ℕ) → m ·ℕ 0ℕ ≡ 0ℕ
mul-zeroℕ m = refl

zero-mulℕ : (m : ℕ) → 0ℕ ·ℕ m ≡ 0ℕ
zero-mulℕ 0ℕ = refl
zero-mulℕ (succℕ m) = ap (λ x → 0ℕ +ℕ x) (zero-mulℕ m)

mul-oneℕ : (m : ℕ) → m ·ℕ 1ℕ ≡ m
mul-oneℕ m = refl

one-mulℕ : (m : ℕ) → 1ℕ ·ℕ m ≡ m
one-mulℕ 0ℕ = refl
one-mulℕ (succℕ m) = concat (ap (λ x → 1ℕ +ℕ x) (one-mulℕ m)) (concat (succ-addℕ 0ℕ m) (ap succℕ (zero-addℕ m)))

mul-succℕ : (m n : ℕ) → m ·ℕ succℕ n ≡ m +ℕ m ·ℕ n
mul-succℕ m n = refl

succ-mulℕ : (m n : ℕ) → succℕ m ·ℕ n ≡ m ·ℕ n +ℕ n
succ-mulℕ m 0ℕ = refl
succ-mulℕ m (succℕ n) = concat (ap (λ x → succℕ m +ℕ x) (succ-mulℕ m n)) (concat (inv (add-assocℕ (succℕ m) (m ·ℕ n) n)) (concat (ap (λ x → x +ℕ n) (succ-addℕ m (m ·ℕ n))) (succ-addℕ (m ·ℕ succℕ n) n )))

mul-commℕ : (m n : ℕ) → m ·ℕ n ≡ n ·ℕ m
mul-commℕ m 0ℕ = inv (zero-mulℕ m)
mul-commℕ m (succℕ n) = concat (add-commℕ m (m ·ℕ n)) (concat (ap (λ x → x +ℕ m) (mul-commℕ m n)) (inv (succ-mulℕ n m)))

left-distribℕ : (m n k : ℕ) → m ·ℕ (n +ℕ k) ≡ m ·ℕ n +ℕ m ·ℕ k
left-distribℕ m n 0ℕ = refl
left-distribℕ m n (succℕ k) = concat (ap (λ x → m +ℕ x) (left-distribℕ m n k)) (concat (inv (add-assocℕ m (m ·ℕ n) (m ·ℕ k))) (concat (ap (λ x → x +ℕ m ·ℕ k) (add-commℕ m (m ·ℕ n))) (add-assocℕ (m ·ℕ n) m (m ·ℕ k))))

right-distribℕ : (m n k : ℕ) → (m +ℕ n) ·ℕ k ≡ m ·ℕ k +ℕ n ·ℕ k
right-distribℕ m n k = concat (mul-commℕ (m +ℕ n) k) (concat (left-distribℕ k m n) (concat (ap (λ x → x +ℕ k ·ℕ n) (mul-commℕ k m)) (ap (λ x → m ·ℕ k +ℕ x) (mul-commℕ k n))))

mul-assocℕ : (m n k : ℕ) → (m ·ℕ n) ·ℕ k ≡ m ·ℕ (n ·ℕ k)
mul-assocℕ m n 0ℕ = refl
mul-assocℕ m n (succℕ k) = inv (concat (left-distribℕ m n (n ·ℕ k)) (ap (λ x → m ·ℕ n +ℕ x) (inv (mul-assocℕ m n k))))

succ-predℤ : (k : ℤ) → succℤ (predℤ k) ≡ k
succ-predℤ 0ℤ = refl
succ-predℤ (in-neg x) = refl
succ-predℤ (in-pos 0ℕ) = refl
succ-predℤ (in-pos (succℕ x)) = refl

pred-succℤ : (k : ℤ) → predℤ (succℤ k) ≡ k
pred-succℤ 0ℤ = refl
pred-succℤ (in-neg 0ℕ) = refl
pred-succℤ (in-neg (succℕ x)) = refl
pred-succℤ (in-pos x) = refl

zero-addℤ : (x : ℤ) → 0ℤ +ℤ x ≡ x
zero-addℤ 0ℤ = refl
zero-addℤ (in-neg 0ℕ) = refl
zero-addℤ (in-neg (succℕ x)) = ap predℤ (zero-addℤ (in-neg x))
zero-addℤ (in-pos 0ℕ) = refl
zero-addℤ (in-pos (succℕ x)) = ap succℤ (zero-addℤ (in-pos x))

add-zeroℤ : (x : ℤ) → x +ℤ 0ℤ ≡ x
add-zeroℤ x = refl

pred-addℤ : (x y : ℤ) → predℤ x +ℤ y ≡ predℤ (x +ℤ y)
pred-addℤ x 0ℤ = refl
pred-addℤ x (in-neg 0ℕ) = refl
pred-addℤ x (in-neg (succℕ y)) = ap predℤ (pred-addℤ x (in-neg y))
pred-addℤ x (in-pos 0ℕ) = concat (succ-predℤ x) (inv (pred-succℤ x))
pred-addℤ x (in-pos (succℕ y)) = concat (ap succℤ (pred-addℤ x (in-pos y))) (concat (succ-predℤ (x +ℤ in-pos y)) (inv (pred-succℤ (x +ℤ in-pos y))))

add-predℤ : (x y : ℤ) → x +ℤ predℤ y ≡ predℤ (x +ℤ y)
add-predℤ x 0ℤ = refl
add-predℤ x (in-neg 0ℕ) = refl
add-predℤ x (in-neg (succℕ x₁)) = refl
add-predℤ x (in-pos 0ℕ) = inv (pred-succℤ x)
add-predℤ x (in-pos (succℕ y)) = inv (pred-succℤ (x +ℤ in-pos y))

succ-addℤ : (x y : ℤ) → succℤ x +ℤ y ≡ succℤ (x +ℤ y)
succ-addℤ x 0ℤ = refl
succ-addℤ x (in-neg 0ℕ) = concat (pred-succℤ x) (inv (succ-predℤ x))
succ-addℤ x (in-neg (succℕ y)) = concat (ap predℤ (succ-addℤ x (in-neg y))) (concat (pred-succℤ (x +ℤ in-neg y)) (inv (succ-predℤ (x +ℤ in-neg y))))
succ-addℤ x (in-pos 0ℕ) = refl
succ-addℤ x (in-pos (succℕ y)) = ap succℤ (succ-addℤ x (in-pos y))

add-succℤ : (x y : ℤ) → x +ℤ succℤ y ≡ succℤ (x +ℤ y)
add-succℤ x 0ℤ = refl
add-succℤ x (in-neg 0ℕ) = inv (succ-predℤ x)
add-succℤ x (in-neg (succℕ y)) = inv (succ-predℤ (x +ℤ in-neg y))
add-succℤ x (in-pos y) = refl

add-assocℤ : (x y z : ℤ) → (x +ℤ y) +ℤ z ≡ x +ℤ (y +ℤ z)
add-assocℤ x y 0ℤ = refl
add-assocℤ x y (in-neg 0ℕ) = inv (add-predℤ x y)
add-assocℤ x y (in-neg (succℕ z)) = concat (add-predℤ (x +ℤ y) (in-neg z)) (inv (concat (add-predℤ x (y +ℤ in-neg z)) (ap predℤ (inv (add-assocℤ x y (in-neg z))))))
add-assocℤ x y (in-pos 0ℕ) = inv (add-succℤ x y)
add-assocℤ x y (in-pos (succℕ z)) = concat (add-succℤ (x +ℤ y) (in-pos z)) (inv (concat (add-succℤ x (y +ℤ in-pos z)) (ap succℤ (inv (add-assocℤ x y (in-pos z))))))

add-commℤ : (x y : ℤ) → x +ℤ y ≡ y +ℤ x
add-commℤ x 0ℤ = concat (add-zeroℤ x) (inv (zero-addℤ x))
add-commℤ x (in-neg 0ℕ) = inv (concat (pred-addℤ 0ℤ x) (ap predℤ (inv (add-commℤ x 0ℤ))))
add-commℤ x (in-neg (succℕ y)) = concat (ap predℤ (add-commℤ x (in-neg y))) (inv (pred-addℤ (in-neg y) x))
add-commℤ x (in-pos 0ℕ) = inv (concat (succ-addℤ 0ℤ x) (ap succℤ (inv (add-commℤ x 0ℤ))))
add-commℤ x (in-pos (succℕ y)) = concat (ap succℤ (add-commℤ x (in-pos y))) (inv (succ-addℤ (in-pos y) x))

neg-addℤ : (x : ℤ) → (-ℤ x) +ℤ x ≡ 0ℤ
neg-addℤ 0ℤ = refl
neg-addℤ (in-neg 0ℕ) = refl
neg-addℤ (in-neg (succℕ x)) = concat (ap predℤ (succ-addℤ (in-pos x) (in-neg x))) (concat (pred-succℤ (in-pos x +ℤ in-neg x)) (neg-addℤ (in-neg x)))
neg-addℤ (in-pos 0ℕ) = refl
neg-addℤ (in-pos (succℕ x)) = concat (ap succℤ (pred-addℤ (in-neg x) (in-pos x))) (concat (succ-predℤ (in-neg x +ℤ in-pos x)) (neg-addℤ (in-pos x)))

add-negℤ : (x : ℤ) → x +ℤ (-ℤ x) ≡ 0ℤ
add-negℤ x = concat (add-commℤ x (-ℤ x)) (neg-addℤ x)

zero-mulℤ : (x : ℤ) → 0ℤ ·ℤ x ≡ 0ℤ
zero-mulℤ 0ℤ = refl
zero-mulℤ (in-neg 0ℕ) = refl
zero-mulℤ (in-neg (succℕ x)) = concat (zero-addℤ (0ℤ ·ℤ in-neg x)) (zero-mulℤ (in-neg x))
zero-mulℤ (in-pos 0ℕ) = refl
zero-mulℤ (in-pos (succℕ x)) = concat (zero-addℤ (0ℤ ·ℤ in-pos x)) (zero-mulℤ (in-pos x))

mul-zeroℤ : (x : ℤ) → x ·ℤ 0ℤ ≡ 0ℤ
mul-zeroℤ x = refl

one-mulℤ : (x : ℤ) → 1ℤ ·ℤ x ≡ x
one-mulℤ 0ℤ = refl
one-mulℤ (in-neg 0ℕ) = refl
one-mulℤ (in-neg (succℕ x)) = concat (ap (λ n → -1ℤ +ℤ n) (one-mulℤ (in-neg x))) (concat (pred-addℤ 0ℤ (in-neg x)) (ap predℤ (zero-addℤ (in-neg x))))
one-mulℤ (in-pos 0ℕ) = refl
one-mulℤ (in-pos (succℕ x)) = concat (ap (λ n → 1ℤ +ℤ n) (one-mulℤ (in-pos x))) (concat (succ-addℤ 0ℤ (in-pos x)) (ap succℤ (zero-addℤ (in-pos x))))

mul-oneℤ : (x : ℤ) → x ·ℤ 1ℤ ≡ x
mul-oneℤ x = refl

infixl 6 _-ℤ_
_-ℤ_ : ℤ → ℤ → ℤ
x -ℤ y = x +ℤ (-ℤ y)

neg-predℤ : (x : ℤ) → -ℤ (predℤ x) ≡ succℤ (-ℤ x)
neg-predℤ 0ℤ = refl
neg-predℤ (in-neg x) = refl
neg-predℤ (in-pos 0ℕ) = refl
neg-predℤ (in-pos (succℕ x)) = refl

succ-negℤ : (x : ℤ) → succℤ (-ℤ x) ≡ -ℤ (predℤ x)
succ-negℤ x = inv (neg-predℤ x)

pred-negℤ : (x : ℤ) → predℤ (-ℤ x) ≡ -ℤ (succℤ x)
pred-negℤ 0ℤ = refl
pred-negℤ (in-neg 0ℕ) = refl
pred-negℤ (in-neg (succℕ x)) = refl
pred-negℤ (in-pos 0ℕ) = refl
pred-negℤ (in-pos (succℕ x)) = refl

neg-succℤ : (x : ℤ) → -ℤ succℤ x ≡ predℤ (-ℤ x)
neg-succℤ x = inv (pred-negℤ x)

pred-mulℤ : (x y : ℤ) → predℤ x ·ℤ y ≡ x ·ℤ y -ℤ y
pred-mulℤ x 0ℤ = refl
pred-mulℤ x (in-neg 0ℕ) = neg-predℤ x
pred-mulℤ x (in-neg (succℕ y)) = concat (ap (λ n → -ℤ (predℤ x) +ℤ n) (pred-mulℤ x (in-neg y))) (concat (ap (λ n → -ℤ predℤ x +ℤ n) (add-commℤ (x ·ℤ in-neg y) (-ℤ in-neg y))) (concat (ap (λ n → n +ℤ (-ℤ in-neg y +ℤ x ·ℤ in-neg y)) (neg-predℤ x)) (concat (inv (add-assocℤ (succℤ (-ℤ x)) (-ℤ in-neg y) (x ·ℤ in-neg y) ) ) (concat (ap (λ n → n +ℤ (x ·ℤ in-neg y)) (succ-addℤ (-ℤ x) (-ℤ in-neg y))) (concat (inv (ap (λ n → n +ℤ (x ·ℤ in-neg y)) (add-succℤ (-ℤ x) (-ℤ in-neg y)))) (concat (add-assocℤ (-ℤ x) (succℤ (-ℤ in-neg y)) (x ·ℤ in-neg y)) (concat (ap (λ n → -ℤ x +ℤ n) (add-commℤ (succℤ (-ℤ in-neg y)) (x ·ℤ in-neg y))) (concat (inv (add-assocℤ (-ℤ x) (x ·ℤ in-neg y) (succℤ (-ℤ in-neg y)))) (ap (λ n → x ·ℤ in-neg (succℕ y) +ℤ n) (succ-negℤ (in-neg y)))))))))))
pred-mulℤ x (in-pos 0ℕ) = refl
pred-mulℤ x (in-pos (succℕ y)) = concat (ap (λ n → predℤ x +ℤ n) (pred-mulℤ x (in-pos y))) (concat (ap (λ n → predℤ x +ℤ n) (add-commℤ (x ·ℤ in-pos y) (-ℤ in-pos y))) (concat (inv (add-assocℤ (predℤ x) (-ℤ in-pos y) (x ·ℤ in-pos y))) (concat (ap (λ n → n +ℤ x ·ℤ in-pos y) (concat (pred-addℤ x (-ℤ in-pos y)) (inv (add-predℤ x (-ℤ in-pos y))))) (concat (add-assocℤ x (predℤ (-ℤ in-pos y)) (x ·ℤ in-pos y)) (concat (ap (λ n → x +ℤ n) (add-commℤ (predℤ (-ℤ in-pos y)) (x ·ℤ in-pos y))) (concat (inv (add-assocℤ x (x ·ℤ in-pos y) (predℤ (-ℤ in-pos y)))) (ap (λ n → x +ℤ x ·ℤ in-pos y +ℤ n) (pred-negℤ (in-pos y)) )))))))


mul-predℤ : (x y : ℤ) → x ·ℤ predℤ y ≡ x ·ℤ y -ℤ x
mul-predℤ x 0ℤ = inv (zero-addℤ (-ℤ x))
mul-predℤ x (in-neg 0ℕ) = refl
mul-predℤ x (in-neg (succℕ y)) = concat (ap (λ n → (-ℤ x +ℤ n)) (mul-predℤ x (in-neg y))) (inv (add-assocℤ (-ℤ x) (x ·ℤ in-neg y) (-ℤ x)))
mul-predℤ x (in-pos 0ℕ) = inv (add-negℤ x)
mul-predℤ x (in-pos (succℕ y)) = inv (concat (ap (λ n → n -ℤ x) (add-commℤ x (x ·ℤ in-pos y))) (concat (add-assocℤ (x ·ℤ in-pos y) x (-ℤ x)) (ap (λ n → x ·ℤ in-pos y +ℤ n) (add-negℤ x))))

succ-mulℤ : (x y : ℤ) → succℤ x ·ℤ y ≡ x ·ℤ y +ℤ y
succ-mulℤ x 0ℤ = refl
succ-mulℤ x (in-pos 0ℕ) = refl
succ-mulℤ x (in-pos (succℕ y)) = concat (ap (λ n → succℤ x +ℤ n) (succ-mulℤ x (in-pos y))) (concat (ap (λ n → succℤ x +ℤ n) (add-commℤ (x ·ℤ in-pos y) (in-pos y))) (concat (inv (add-assocℤ (succℤ x) (in-pos y) (x ·ℤ in-pos y))) (concat (ap (λ n → n +ℤ x ·ℤ in-pos y) (concat (succ-addℤ x (in-pos y)) (inv (add-succℤ x (in-pos y))))) (concat (add-assocℤ x (succℤ (in-pos y)) (x ·ℤ in-pos y)) (concat (ap (λ n → x +ℤ n) (add-commℤ (succℤ (in-pos y)) (x ·ℤ in-pos y))) (inv (add-assocℤ x (x ·ℤ in-pos y) (succℤ (in-pos y)))))))))
succ-mulℤ x (in-neg 0ℕ) = neg-succℤ x
succ-mulℤ x (in-neg (succℕ y)) = concat (ap (λ n → -ℤ succℤ x +ℤ n) (concat (succ-mulℤ x (in-neg y)) (add-commℤ (x ·ℤ in-neg y) (in-neg y)))) (concat (inv (add-assocℤ (-ℤ succℤ x) (in-neg y) (x ·ℤ in-neg y))) (concat (ap (λ n → (n +ℤ in-neg y) +ℤ (x ·ℤ in-neg y)) (neg-succℤ x)) (concat (ap (λ n → n +ℤ (x ·ℤ in-neg y)) (concat (pred-addℤ (-ℤ x) (in-neg y)) (inv (add-predℤ (-ℤ x) (in-neg y))))) (concat (add-assocℤ (-ℤ x) (predℤ (in-neg y)) (x ·ℤ in-neg y)) (concat (ap (λ n → -ℤ x +ℤ n) (add-commℤ (in-neg (succℕ y)) (x ·ℤ in-neg y))) (inv (add-assocℤ (-ℤ x) (x ·ℤ in-neg y) (in-neg (succℕ y)))))))))

mul-succℤ : (x y : ℤ) → x ·ℤ succℤ y ≡ x ·ℤ y +ℤ x
mul-succℤ x 0ℤ = inv (zero-addℤ x)
mul-succℤ x (in-neg 0ℕ) = inv (neg-addℤ x)
mul-succℤ x (in-neg (succℕ y)) = inv (concat (ap (λ n → n +ℤ x) (add-commℤ (-ℤ x) (x ·ℤ in-neg y))) (concat (add-assocℤ (x ·ℤ in-neg y) (-ℤ x) x) (ap (λ n → x ·ℤ in-neg y +ℤ n) (neg-addℤ x))))
mul-succℤ x (in-pos 0ℕ) = refl
mul-succℤ x (in-pos (succℕ y)) = add-commℤ x (x ·ℤ in-pos (succℕ y))

left-distribℤ : (x y z : ℤ) → x ·ℤ (y +ℤ z) ≡ x ·ℤ y +ℤ x ·ℤ z
left-distribℤ x y 0ℤ = refl
left-distribℤ x y (in-neg 0ℕ) = mul-predℤ x y
left-distribℤ x y (in-neg (succℕ z)) = concat (mul-predℤ x (y +ℤ in-neg z)) (concat (ap (λ n → n -ℤ x) (left-distribℤ x y (in-neg z))) (concat (add-assocℤ (x ·ℤ y) (x ·ℤ in-neg z) (-ℤ x)) (inv (ap (λ n → x ·ℤ y +ℤ n) (mul-predℤ x (in-neg z))))))
left-distribℤ x y (in-pos 0ℕ) = mul-succℤ x y
left-distribℤ x y (in-pos (succℕ z)) = concat (mul-succℤ x (y +ℤ in-pos z)) (concat (ap (λ n → n +ℤ x) (left-distribℤ x y (in-pos z)))  (concat (add-assocℤ (x ·ℤ y) (x ·ℤ in-pos z) x) (inv (ap (λ n → x ·ℤ y +ℤ n) (mul-succℤ x (in-pos z))))))

neg-distribℤ : (x y : ℤ) → -ℤ (x +ℤ y) ≡ -ℤ x +ℤ -ℤ y
neg-distribℤ x 0ℤ = refl
neg-distribℤ x (in-neg 0ℕ) = neg-predℤ x
neg-distribℤ x (in-neg (succℕ y)) = concat (neg-predℤ (x +ℤ in-neg y)) (concat (ap succℤ (neg-distribℤ x (in-neg y))) (add-succℤ (-ℤ x) (-ℤ in-neg y)))
neg-distribℤ x (in-pos 0ℕ) = neg-succℤ x
neg-distribℤ x (in-pos (succℕ y)) = concat (neg-succℤ (x +ℤ in-pos y)) (concat (ap predℤ (neg-distribℤ x (in-pos y))) (add-predℤ (-ℤ x) (-ℤ in-pos y)))

right-distribℤ : (x y z : ℤ) → (x +ℤ y) ·ℤ z ≡ x ·ℤ z +ℤ y ·ℤ z
right-distribℤ x y 0ℤ = refl
right-distribℤ x y (in-neg 0ℕ) = neg-distribℤ x y
right-distribℤ x y (in-neg (succℕ z)) = concat (ap (λ n → -ℤ (x +ℤ y) +ℤ n) (right-distribℤ x y (in-neg z))) (concat (ap (λ n → n +ℤ (x ·ℤ in-neg z +ℤ y ·ℤ in-neg z)) (neg-distribℤ x y)) (concat (inv (add-assocℤ (-ℤ x +ℤ -ℤ y) (x ·ℤ in-neg z) (y ·ℤ in-neg z))) (concat (ap (λ n → n +ℤ y ·ℤ in-neg z) (concat (ap (λ n → n +ℤ x ·ℤ in-neg z) (add-commℤ (-ℤ x) (-ℤ y))) (concat (add-assocℤ (-ℤ y) (-ℤ x) (x ·ℤ in-neg z)) (add-commℤ (-ℤ y) (-ℤ x +ℤ x ·ℤ in-neg z))))) (add-assocℤ (-ℤ x +ℤ x ·ℤ in-neg z) (-ℤ y) (y ·ℤ in-neg z)))))
right-distribℤ x y (in-pos 0ℕ) = refl
right-distribℤ x y (in-pos (succℕ z)) = concat (ap (λ n → (x +ℤ y) +ℤ n) (right-distribℤ x y (in-pos z))) (concat (inv (add-assocℤ (x +ℤ y) (x ·ℤ in-pos z) (y ·ℤ in-pos z))) (concat (ap (λ n → n +ℤ (y ·ℤ in-pos z)) (concat (ap (λ n → n +ℤ x ·ℤ in-pos z) (add-commℤ x y)) (concat (add-assocℤ y x (x ·ℤ in-pos z)) (add-commℤ y (x +ℤ x ·ℤ in-pos z))) )) (add-assocℤ (x +ℤ x ·ℤ in-pos z) y (y ·ℤ in-pos z))))

neg-negℤ : (x : ℤ) → -ℤ -ℤ x ≡ x
neg-negℤ 0ℤ = refl
neg-negℤ (in-neg x) = refl
neg-negℤ (in-pos x) = refl

neg-mulℤ : (x y : ℤ) → -ℤ x ·ℤ y ≡ -ℤ (x ·ℤ y)
neg-mulℤ x 0ℤ = refl
neg-mulℤ x (in-neg 0ℕ) = refl
neg-mulℤ x (in-neg (succℕ y)) = concat (ap (λ n → -ℤ -ℤ x +ℤ n) (neg-mulℤ x (in-neg y))) (inv (neg-distribℤ (-ℤ x) (x ·ℤ in-neg y)))
neg-mulℤ x (in-pos 0ℕ) = refl
neg-mulℤ x (in-pos (succℕ y)) = concat (ap (λ n → -ℤ x +ℤ n) (neg-mulℤ x (in-pos y))) (inv (neg-distribℤ x (x ·ℤ in-pos y)))

mul-negℤ : (x y : ℤ) → x ·ℤ -ℤ y ≡ -ℤ (x ·ℤ y)
mul-negℤ x 0ℤ = refl
mul-negℤ x (in-neg 0ℕ) = inv (neg-negℤ x)
mul-negℤ x (in-neg (succℕ y)) = concat (ap (λ n → x +ℤ n) (inv (neg-negℤ (x ·ℤ in-pos y)))) (concat (ap (λ n → n +ℤ -ℤ -ℤ (x ·ℤ in-pos y)) (inv (neg-negℤ x))) (concat (ap (λ n → -ℤ -ℤ x +ℤ -ℤ n) (inv (mul-negℤ x (in-pos y)))) (inv (neg-distribℤ (-ℤ x) (x ·ℤ in-neg y)))))
mul-negℤ x (in-pos 0ℕ) = refl
mul-negℤ x (in-pos (succℕ y)) = concat (ap (λ n → -ℤ x +ℤ n) (inv (neg-negℤ (x ·ℤ in-neg y)))) (concat (ap (λ n → -ℤ x +ℤ -ℤ n) (inv (mul-negℤ x (in-neg y)))) (inv (neg-distribℤ x (x ·ℤ in-pos y))))

mul-assocℤ : (x y z : ℤ) → x ·ℤ y ·ℤ z ≡ x ·ℤ (y ·ℤ z)
mul-assocℤ x y 0ℤ = refl
mul-assocℤ x y (in-neg 0ℕ) = inv (mul-negℤ x y)
mul-assocℤ x y (in-neg (succℕ z)) = concat (ap (λ n → -ℤ (x ·ℤ y) +ℤ n) (mul-assocℤ x y (in-neg z))) (concat (ap (λ n → n +ℤ x ·ℤ (y ·ℤ in-neg z)) (inv (mul-negℤ x y))) (inv (left-distribℤ x (-ℤ y) (y ·ℤ in-neg z))))
mul-assocℤ x y (in-pos 0ℕ) = refl
mul-assocℤ x y (in-pos (succℕ z)) = concat (ap (λ n → (x ·ℤ y) +ℤ n) (mul-assocℤ x y (in-pos z))) (inv (left-distribℤ x y (y ·ℤ in-pos z)))

mul-commℤ : (x y : ℤ) → x ·ℤ y ≡ y ·ℤ x
mul-commℤ x 0ℤ = inv (zero-mulℤ x)
mul-commℤ x (in-neg 0ℕ) = inv (concat (neg-mulℤ 1ℤ x) (ap (λ n → -ℤ n) (one-mulℤ x)))
mul-commℤ x (in-neg (succℕ y)) = concat (add-commℤ (-ℤ x) (x ·ℤ in-neg y)) (concat (ap (λ n → n -ℤ x) (mul-commℤ x (in-neg y))) (inv (pred-mulℤ (in-neg y) x)))
mul-commℤ x (in-pos 0ℕ) = inv (one-mulℤ x)
mul-commℤ x (in-pos (succℕ y)) = concat (add-commℤ x (x ·ℤ in-pos y)) (concat (ap (λ n → n +ℤ x) (mul-commℤ x (in-pos y))) (inv (succ-mulℤ (in-pos y) x)))

