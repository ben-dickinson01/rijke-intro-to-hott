module ch7 where

open import ch6 public

infix 4 _∣_
_∣_ : (n : ℕ) → (m : ℕ) → Set lzero
n ∣ m = Σ ℕ (λ k → (k ·ℕ n ≡ m))

one-divℕ : (x : ℕ) → 1ℕ ∣ x
one-divℕ x = (x , refl)

div-zeroℕ : (x : ℕ) → x ∣ 0ℕ
div-zeroℕ x = (0ℕ , zero-mulℕ x)

div-sumℕ : (x y d : ℕ) → (d ∣ x) → (d ∣ y) → (d ∣ (x +ℕ y))
div-sumℕ x y d (kx , refl) (ky , refl) = ((kx +ℕ ky) , right-distribℕ kx ky d)

is-reflexive : {A : Set} → (A → A → Set) → Set
is-reflexive {A} R = (x : A) → R x x

is-symmetric : {A : Set} → (A → A → Set) → Set
is-symmetric {A} R = (x y : A) → R x y → R y x

is-transitive : {A : Set} → (A → A → Set) → Set
is-transitive {A} R = (x y z : A) → R x y → R y z → R x z

infix 4 _≡ℕ_mod_
_≡ℕ_mod_ : ℕ → ℕ → ℕ → Set lzero
x ≡ℕ y mod k = k ∣ distℕ x y

k-is-zero-mod-kℕ : (k : ℕ) → k ≡ℕ 0ℕ mod k
k-is-zero-mod-kℕ k = (1ℕ , one-mulℕ k)

mod-is-rflℕ : (k : ℕ) → is-reflexive (λ x y → x ≡ℕ y mod k)
mod-is-rflℕ k 0ℕ = (0ℕ , zero-mulℕ k)
mod-is-rflℕ k (succℕ x) =
  (0ℕ , concat (zero-mulℕ k) (inv (≡-to-dist0ℕ (succℕ x) (succℕ x) refl)))

mod-is-symmℕ : (k : ℕ) → is-symmetric (λ x y → x ≡ℕ y mod k)
mod-is-symmℕ k 0ℕ 0ℕ p = (0ℕ , zero-mulℕ k)
mod-is-symmℕ k 0ℕ (succℕ y) (n , p) = (n , concat p (dist-symmℕ 0ℕ (succℕ y)))
mod-is-symmℕ k (succℕ x) 0ℕ (n , p) = (n , concat p (dist-symmℕ 0ℕ (succℕ x)))
mod-is-symmℕ k (succℕ x) (succℕ y) (n , p) = (n , concat p (dist-symmℕ x y))

div-distℕ : (a b d : ℕ) → d ∣ a → d ∣ b → d ∣ distℕ a b
div-distℕ a b d (ka , pa) (kb , pb) =
  (distℕ ka kb ,
   concat (mul-commℕ (distℕ ka kb) d)
   (concat (inv (dist-linearℕ ka kb d))
   (concat (ap (λ n → distℕ n (d ·ℕ kb)) (concat (mul-commℕ d ka) pa))
           (ap (distℕ a) (concat (mul-commℕ d kb) pb)))))

dist-add-rightℕ : (a b : ℕ) → distℕ (a +ℕ b) b ≡ a
dist-add-rightℕ a 0ℕ = dist-zero-rightℕ a
dist-add-rightℕ a (succℕ b) = dist-add-rightℕ a b

div-sum-partℕ : (a b d : ℕ) → d ∣ (a +ℕ b) → d ∣ b → d ∣ a
div-sum-partℕ a b d dab db = tr (d ∣_) (dist-add-rightℕ a b) (div-distℕ (a +ℕ b) b d dab db)

mod-is-transℕ : (k : ℕ) → is-transitive (λ x y → x ≡ℕ y mod k)
mod-is-transℕ k x y z pxy pyz with ≤-dichotomyℕ x y | ≤-dichotomyℕ y z | ≤-dichotomyℕ x z
... | inl x≤y | inl y≤z | _ =
  tr (k ∣_)
     (inv (proj₂ (dist-tri-eqℕ x z y) (inl (x≤y , y≤z))))
     (div-sumℕ (distℕ x y) (distℕ z y) k pxy (tr (k ∣_) (dist-symmℕ y z) pyz))
... | inr y≤x | inr z≤y | _ =
  tr (k ∣_)
     (inv (proj₂ (dist-tri-eqℕ x z y) (inr (z≤y , y≤x))))
     (div-sumℕ (distℕ x y) (distℕ z y) k pxy (tr (k ∣_) (dist-symmℕ y z) pyz))
... | inl x≤y | inr z≤y | inl x≤z =
  div-sum-partℕ (distℕ x z) (distℕ y z) k
    (tr (k ∣_) (proj₂ (dist-tri-eqℕ x y z) (inl (x≤z , z≤y))) pxy)
    pyz
... | inl x≤y | inr z≤y | inr z≤x =
  div-sum-partℕ (distℕ x z) (distℕ x y) k
    (tr (k ∣_)
        (concat (dist-symmℕ y z)
        (concat (proj₂ (dist-tri-eqℕ z y x) (inl (z≤x , x≤y)))
        (concat (ap (λ n → n +ℕ distℕ y x) (dist-symmℕ z x))
                (ap (distℕ x z +ℕ_) (dist-symmℕ y x)))))
        pyz)
    pxy
... | inr y≤x | inl y≤z | inl x≤z =
  div-sum-partℕ (distℕ x z) (distℕ x y) k
    (tr (k ∣_)
        (concat (proj₂ (dist-tri-eqℕ y z x) (inl (y≤x , x≤z)))
        (concat (ap (λ n → n +ℕ distℕ z x) (dist-symmℕ y x))
        (concat (ap (distℕ x y +ℕ_) (dist-symmℕ z x))
                (add-commℕ (distℕ x y) (distℕ x z)))))
        pyz)
    pxy
... | inr y≤x | inl y≤z | inr z≤x =
  div-sum-partℕ (distℕ x z) (distℕ y z) k
    (tr (k ∣_)
        (concat (dist-symmℕ x y)
        (concat (proj₂ (dist-tri-eqℕ y x z) (inl (y≤z , z≤x)))
                (add-commℕ (distℕ y z) (distℕ x z))))
        pxy)
    pyz

classical-Fin : ℕ → Set lzero
classical-Fin k = Σ ℕ (λ x → x <ℕ k)

Fin : ℕ → Set
Fin 0ℕ = 𝟘
Fin (succℕ k) = Fin k ⊎ 𝟙

inlFin : (k : ℕ) → Fin k → Fin (succℕ k)
inlFin k = inl

neg-oneFin : (k : ℕ) → Fin (succℕ k)
neg-oneFin k = inr *

indFin : {p : (k : ℕ) → Fin k → Set} → ((k : ℕ) → (x : Fin k) → p (succℕ k) (inlFin k x)) → ((k : ℕ) → p (succℕ k) (neg-oneFin k)) → (k : ℕ) → (x : Fin k) → p k x
indFin {p} f-left f-neg1 (succℕ k) (inl x) = f-left k x
indFin {p} f-left f-neg1 (succℕ k) (inr *) = f-neg1 k

Fin-to-ℕ : (k : ℕ) → Fin k → ℕ
Fin-to-ℕ 0ℕ ()
Fin-to-ℕ (succℕ k) (inl x) = Fin-to-ℕ k x
Fin-to-ℕ (succℕ k) (inr x) = k

Fin-to-ℕ-bounded : (k : ℕ) → (x : Fin k) → (Fin-to-ℕ k x) <ℕ k
Fin-to-ℕ-bounded 0ℕ ()
Fin-to-ℕ-bounded (succℕ k) (inl x) = <-transℕ (Fin-to-ℕ (succℕ k) (inl x)) k (succℕ k) (Fin-to-ℕ-bounded k x) (<-succℕ k)
Fin-to-ℕ-bounded (succℕ k) (inr x) = <-succℕ k

Fin-to-ℕ-injective : (k : ℕ) → (x y : Fin k) → (Fin-to-ℕ k x ≡ Fin-to-ℕ k y) → x ≡ y
Fin-to-ℕ-injective 0ℕ () y p
Fin-to-ℕ-injective (succℕ k) (inl x) (inl y) p = ap inl (Fin-to-ℕ-injective k x y p)
Fin-to-ℕ-injective (succℕ k) (inl x) (inr y) p =
  indEmpty (<-antirflℕ k (tr (λ m → m <ℕ k) p (Fin-to-ℕ-bounded k x)))
Fin-to-ℕ-injective (succℕ k) (inr x) (inl y) p =
  indEmpty (<-antirflℕ k (tr (λ m → m <ℕ k) (inv p) (Fin-to-ℕ-bounded k y)))
Fin-to-ℕ-injective (succℕ k) (inr *) (inr *) p = ap inr refl

is-split-surjective : {A B : Set} → (f : A → B) → (b : B) → Set lzero
is-split-surjective {A} f = λ b → Σ A (λ a → f a ≡ b)

ℕ-mod : (k : ℕ) → Set lzero
ℕ-mod 0ℕ = ℕ
ℕ-mod (succℕ k) = Fin (succℕ k)

zeroFin : (k : ℕ) → Fin (succℕ k)
zeroFin 0ℕ = inr *
zeroFin (succℕ k) = inl (zeroFin k)

skip-zeroFin : (k : ℕ) → Fin k → Fin (succℕ k)
skip-zeroFin (succℕ k) (inl x) = inl (skip-zeroFin k x)
skip-zeroFin (succℕ k) (inr *) = inr *

succFin : (k : ℕ) → Fin k → Fin k
succFin (succℕ k) (inl x) = skip-zeroFin k x
succFin (succℕ k) (inr _) = zeroFin k

ℕ-to-Fin : (k : ℕ) → ℕ → Fin (succℕ k)
ℕ-to-Fin k 0ℕ = zeroFin k
ℕ-to-Fin k (succℕ x) = succFin (succℕ k) (ℕ-to-Fin k x)

infix 10 [_]_
[_]_ : ℕ → (k : ℕ) → ℕ-mod k
[ x ] 0ℕ = x
[ x ] succℕ k = ℕ-to-Fin k x

zeroFin-to-0ℕ : (k : ℕ) → (Fin-to-ℕ (succℕ k) (zeroFin k)) ≡ 0ℕ
zeroFin-to-0ℕ 0ℕ = refl
zeroFin-to-0ℕ (succℕ k) = zeroFin-to-0ℕ k

ιFin = Fin-to-ℕ

skip-zeroFin-to-add-oneℕ : (k : ℕ) → (x : Fin k) → (ιFin (succℕ k) (skip-zeroFin k x)) ≡ (ιFin k x) +ℕ 1ℕ
skip-zeroFin-to-add-oneℕ (succℕ k) (inl x) = skip-zeroFin-to-add-oneℕ k x
skip-zeroFin-to-add-oneℕ (succℕ k) (inr *) = refl

succFin-to-succℕ-mod : (k : ℕ) → (x : Fin k) → (ιFin k (succFin k x)) ≡ℕ (ιFin k x +ℕ 1ℕ) mod k
succFin-to-succℕ-mod (succℕ k) (inl x) = (0ℕ , concat (zero-mulℕ (succℕ k)) (inv (≡-to-dist0ℕ (ιFin (succℕ k) (skip-zeroFin k x)) ((ιFin k x) +ℕ 1ℕ) (skip-zeroFin-to-add-oneℕ k x))))
succFin-to-succℕ-mod (succℕ k) (inr *) = (1ℕ , concat (one-mulℕ (succℕ k)) (inv (ap (λ n → distℕ n (k +ℕ 1ℕ)) (zeroFin-to-0ℕ k))))

Fin-to-modℕ : (k : ℕ) → (x : ℕ) → (ιFin (succℕ k) ([ x ] (succℕ k))) ≡ℕ x mod (k +ℕ 1ℕ)
Fin-to-modℕ k 0ℕ = (0ℕ , concat (zero-mulℕ (succℕ k)) (inv (ap (λ n → distℕ n 0ℕ) (zeroFin-to-0ℕ k))))
Fin-to-modℕ k (succℕ x) =
  mod-is-transℕ (k +ℕ 1ℕ) (ιFin (succℕ k) ([ succℕ x ] (succℕ k))) (ιFin (succℕ k) ([ x ] (succℕ k)) +ℕ 1ℕ) (succℕ x)
    (succFin-to-succℕ-mod (succℕ k) ([ x ] (succℕ k)))
    (proj₁ (Fin-to-modℕ k x) , (proj₂ (Fin-to-modℕ k x)))

<-or-≤ℕ : (x y : ℕ) → (x <ℕ y) ⊎ (y ≤ℕ x)
<-or-≤ℕ 0ℕ 0ℕ = inr *
<-or-≤ℕ (succℕ x) 0ℕ = inr *
<-or-≤ℕ 0ℕ (succℕ y) = inl *
<-or-≤ℕ (succℕ x) (succℕ y) = <-or-≤ℕ x y

¬<0ℕ : (x : ℕ) → ¬ (x <ℕ 0ℕ)
¬<0ℕ 0ℕ ()
¬<0ℕ (succℕ x) ()

<-div-to-zeroℕ : (d x : ℕ) → x <ℕ d → d ∣ x → x ≡ 0ℕ
<-div-to-zeroℕ d 0ℕ p div = refl
<-div-to-zeroℕ d (succℕ x) p (k , pk) with <-or-≤ℕ (succℕ x) d
<-div-to-zeroℕ d (succℕ x) p (0ℕ , pk) | inl sx<d = concat (inv pk) (zero-mulℕ d)
<-div-to-zeroℕ d (succℕ x) p (succℕ k , pk) | inl sx<d = ex-falso ((<-to-≱ (succℕ x) d sx<d) (≤-transℕ {d} {d +ℕ k ·ℕ d} {succℕ x} (add-≤ℕ d 0ℕ (k ·ℕ d) (0ℕ-leℕ (k ·ℕ d))) (≡-to-≤ℕ (concat (add-commℕ d (k ·ℕ d)) (concat (inv (succ-mulℕ k d)) pk)))))
<-div-to-zeroℕ d (succℕ x) p (0ℕ , pk) | inr d≤sx = concat (inv pk) (zero-mulℕ d)
<-div-to-zeroℕ d (succℕ x) p (succℕ k , pk) | inr d≤sx = ex-falso ((<-to-≱ (succℕ x) d p) d≤sx)

eqℕ-to-eq-modℕ : (k : ℕ) → (x y : ℕ) → (x ≡ y) → (x ≡ℕ y mod k)
eqℕ-to-eq-modℕ k x y p = (0ℕ , concat (zero-mulℕ k) (inv (≡-to-dist0ℕ x y p)))

eq-modℕ-to-eqℕ : (k : ℕ) → (x y : ℕ) → (x ≡ℕ y mod k) → (distℕ x y <ℕ k) → x ≡ y
eq-modℕ-to-eqℕ 0ℕ x y (kxy , pxy) d = ex-falso (¬<0ℕ (distℕ x y) d)
eq-modℕ-to-eqℕ (succℕ k) x y (kxy , pxy) d = dist0-to-≡ℕ x y (concat (inv pxy) (concat pxy (<-div-to-zeroℕ (succℕ k) (distℕ x y) d (kxy , pxy))))

dist-bounded-<ℕ : (x y k : ℕ) → x <ℕ k → y <ℕ k → distℕ x y <ℕ k
dist-bounded-<ℕ 0ℕ 0ℕ 0ℕ () yk
dist-bounded-<ℕ (succℕ x) 0ℕ 0ℕ () yk
dist-bounded-<ℕ 0ℕ 0ℕ (succℕ k) xk yk = *
dist-bounded-<ℕ 0ℕ (succℕ y) (succℕ k) xk yk = yk
dist-bounded-<ℕ (succℕ x) 0ℕ (succℕ k) xk yk = xk
dist-bounded-<ℕ (succℕ x) (succℕ y) (succℕ k) xk yk =
  <-transℕ (distℕ x y) k (succℕ k) (dist-bounded-<ℕ x y k xk yk) (<-succℕ k)

Fin-k-is-ℕmod-k : (k : ℕ) → (x y : ℕ) → ([ x ] (succℕ k) ≡ [ y ] (succℕ k) ↔ x ≡ℕ y mod (succℕ k))
Fin-k-is-ℕmod-k k x y = (to k x y , from k x y)
  where
  to : (k : ℕ) → (x y : ℕ) → [ x ] (succℕ k) ≡ [ y ] (succℕ k) → x ≡ℕ y mod (succℕ k)
  to 0ℕ x y p = ((distℕ x y) , refl)
  to (succℕ k) x y p =
    mod-is-transℕ (succℕ (succℕ k)) x (ιFin (succℕ (succℕ k)) ([ x ] (succℕ (succℕ k)))) y
      (mod-is-symmℕ (succℕ (succℕ k)) (ιFin (succℕ (succℕ k)) ([ x ] (succℕ (succℕ k)))) x (Fin-to-modℕ (succℕ k) x))
      (mod-is-transℕ (succℕ (succℕ k)) (ιFin (succℕ (succℕ k)) ([ x ] (succℕ (succℕ k)))) (ιFin (succℕ (succℕ k)) ([ y ] (succℕ (succℕ k)))) y
        (eqℕ-to-eq-modℕ (succℕ (succℕ k)) (ιFin (succℕ (succℕ k)) ([ x ] (succℕ (succℕ k)))) (ιFin (succℕ (succℕ k)) ([ y ] (succℕ (succℕ k)))) (ap (ιFin (succℕ (succℕ k))) p))
        (Fin-to-modℕ (succℕ k) y))

  Fin1-is-𝟙 : (n : ℕ) → ℕ-to-Fin 0ℕ n ≡ inr *
  Fin1-is-𝟙 0ℕ = refl
  Fin1-is-𝟙 (succℕ n) = ap (succFin 1ℕ) (Fin1-is-𝟙 n)

  from : (k : ℕ) →  (x y : ℕ) → x ≡ℕ y mod (succℕ k) → [ x ] (succℕ k) ≡ [ y ] (succℕ k)
  from 0ℕ x y (k , refl) = concat (Fin1-is-𝟙 x) (inv (Fin1-is-𝟙 y))
  from (succℕ k) x y p =
    Fin-to-ℕ-injective (succℕ (succℕ k)) ([ x ] (succℕ (succℕ k))) ([ y ] (succℕ (succℕ k)))
      (eq-modℕ-to-eqℕ (succℕ (succℕ k))
        (ιFin (succℕ (succℕ k)) ([ x ] (succℕ (succℕ k))))
        (ιFin (succℕ (succℕ k)) ([ y ] (succℕ (succℕ k))))
        (mod-is-transℕ (succℕ (succℕ k))
          (ιFin (succℕ (succℕ k)) ([ x ] (succℕ (succℕ k))))
          x
          (ιFin (succℕ (succℕ k)) ([ y ] (succℕ (succℕ k))))
          (Fin-to-modℕ (succℕ k) x)
          (mod-is-transℕ (succℕ (succℕ k))
            x
            y
            (ιFin (succℕ (succℕ k)) ([ y ] (succℕ (succℕ k))))
            p
            (mod-is-symmℕ (succℕ (succℕ k))
              (ιFin (succℕ (succℕ k)) ([ y ] (succℕ (succℕ k))))
              y
              (Fin-to-modℕ (succℕ k) y))))
        (dist-bounded-<ℕ
          (ιFin (succℕ (succℕ k)) ([ x ] (succℕ (succℕ k))))
          (ιFin (succℕ (succℕ k)) ([ y ] (succℕ (succℕ k))))
          (succℕ (succℕ k))
          (Fin-to-ℕ-bounded (succℕ (succℕ k)) ([ x ] (succℕ (succℕ k))))
          (Fin-to-ℕ-bounded (succℕ (succℕ k)) ([ y ] (succℕ (succℕ k))))))

ℕ-to-Fin-split-surj : (k : ℕ) → (x : Fin (succℕ k)) →  is-split-surjective (ℕ-to-Fin k) x
ℕ-to-Fin-split-surj k x = (Fin-to-ℕ (succℕ k) x ,
  Fin-to-ℕ-injective (succℕ k) (ℕ-to-Fin k (Fin-to-ℕ (succℕ k) x)) x
    (eq-modℕ-to-eqℕ (succℕ k)
      (Fin-to-ℕ (succℕ k) (ℕ-to-Fin k (Fin-to-ℕ (succℕ k) x)))
      (Fin-to-ℕ (succℕ k) x)
      (Fin-to-modℕ k (Fin-to-ℕ (succℕ k) x))
      (dist-bounded-<ℕ
        (Fin-to-ℕ (succℕ k) (ℕ-to-Fin k (Fin-to-ℕ (succℕ k) x)))
        (Fin-to-ℕ (succℕ k) x)
        (succℕ k)
        (Fin-to-ℕ-bounded (succℕ k) (ℕ-to-Fin k (Fin-to-ℕ (succℕ k) x)))
        (Fin-to-ℕ-bounded (succℕ k) x))))

ℤ-mod : (k : ℕ) → Set lzero
ℤ-mod 0ℕ = ℤ
ℤ-mod (succℕ k) = Fin (succℕ k)

add-ℤ-mod : (k : ℕ) → ℤ-mod k → ℤ-mod k → ℤ-mod k
add-ℤ-mod 0ℕ x y = x +ℤ y
add-ℤ-mod (succℕ k) x y = [ ιFin (succℕ k) x +ℕ ιFin (succℕ k) y ] (succℕ k)

neg-ℤ-mod : (k : ℕ) → ℤ-mod k → ℤ-mod k
neg-ℤ-mod 0ℕ x = -ℤ x
neg-ℤ-mod (succℕ k) x = [ distℕ (ιFin (succℕ k) x) (succℕ k) ] (succℕ k)

zero-ℤmod : (k : ℕ) → ℤ-mod k
zero-ℤmod 0ℕ = 0ℤ
zero-ℤmod (succℕ k) = zeroFin k

infix 6 _+ℤmod_
_+ℤmod_ : {k : ℕ} → ℤ-mod k → ℤ-mod k → ℤ-mod k
_+ℤmod_ {k} x y = add-ℤ-mod k x y

infix 8 -ℤmod_
-ℤmod_ : {k : ℕ} → ℤ-mod k → ℤ-mod k
-ℤmod_ {k} x = neg-ℤ-mod k x

ι-ℤmod : (k : ℕ) → (x : ℤ-mod (succℕ k)) → ℕ
ι-ℤmod k x = ιFin (succℕ k) x

zero-ℤmod-to-zeroℕ : (k : ℕ) → ι-ℤmod k (zero-ℤmod (succℕ k)) ≡ 0ℕ
zero-ℤmod-to-zeroℕ 0ℕ = refl
zero-ℤmod-to-zeroℕ (succℕ k) = zeroFin-to-0ℕ k

ι-ℤmod-add : (k : ℕ) → (x y : ℤ-mod (succℕ k)) → ι-ℤmod k (x +ℤmod y) ≡ℕ ι-ℤmod k x +ℕ ι-ℤmod k y mod (succℕ k)
ι-ℤmod-add k x y = Fin-to-modℕ k (ιFin (succℕ k) x +ℕ ιFin (succℕ k) y)

ι-ℤmod-neg : (k : ℕ) → (x : ℤ-mod (succℕ k)) → ι-ℤmod k (-ℤmod x) ≡ℕ distℕ (ι-ℤmod k x) (succℕ k) mod (succℕ k)
ι-ℤmod-neg k x = Fin-to-modℕ k (distℕ (ιFin (succℕ k) x) (succℕ k))

add-≡-right-modℕ : (k a b c : ℕ) → a ≡ℕ b mod k → (a +ℕ c) ≡ℕ (b +ℕ c) mod k
add-≡-right-modℕ k a b c p = tr (k ∣_) (inv (dist-trans-invarℕ a b c)) p

add-≡-left-modℕ : (k c a b : ℕ) → a ≡ℕ b mod k → (c +ℕ a) ≡ℕ (c +ℕ b) mod k
add-≡-left-modℕ k c a b p =
  tr (k ∣_)
    (inv (concat (ap (λ x → distℕ x (c +ℕ b)) (add-commℕ c a))
         (concat (ap (distℕ (a +ℕ c)) (add-commℕ c b))
                 (dist-trans-invarℕ a b c))))
    p


comm-ℤmod : (k : ℕ) → (x y : ℤ-mod k) → add-ℤ-mod k x y ≡ add-ℤ-mod k y x
comm-ℤmod 0ℕ x y = add-commℤ x y
comm-ℤmod (succℕ k) x y = ap (ℕ-to-Fin k) (add-commℕ (ιFin (succℕ k) x) (ιFin (succℕ k) y))

add-zero-ℤmod : (k : ℕ) → (x : ℤ-mod k) → add-ℤ-mod k x (zero-ℤmod k) ≡ x
add-zero-ℤmod 0ℕ x = refl
add-zero-ℤmod (succℕ k) x =
  concat
    (ap (ℕ-to-Fin k) (ap (ιFin (succℕ k) x +ℕ_) (zeroFin-to-0ℕ k)))
    (proj₂ (ℕ-to-Fin-split-surj k x))

zero-add-ℤmod : (k : ℕ) → (x : ℤ-mod k) → add-ℤ-mod k (zero-ℤmod k) x ≡ x
zero-add-ℤmod k x = concat (comm-ℤmod k (zero-ℤmod k) x) (add-zero-ℤmod k x)

add-assoc-ℤmod : (k : ℕ) → (x y z : ℤ-mod k) → add-ℤ-mod k (add-ℤ-mod k x y) z ≡ add-ℤ-mod k x (add-ℤ-mod k y z)
add-assoc-ℤmod 0ℕ x y z = add-assocℤ x y z
add-assoc-ℤmod (succℕ k) x y z =
  proj₂ (Fin-k-is-ℕmod-k k
    (ιFin (succℕ k) (add-ℤ-mod (succℕ k) x y) +ℕ ιFin (succℕ k) z)
    (ιFin (succℕ k) x +ℕ ιFin (succℕ k) (add-ℤ-mod (succℕ k) y z)))
    (mod-is-transℕ (succℕ k)
      (ιFin (succℕ k) (add-ℤ-mod (succℕ k) x y) +ℕ ιFin (succℕ k) z)
      ((ιFin (succℕ k) x +ℕ ιFin (succℕ k) y) +ℕ ιFin (succℕ k) z)
      (ιFin (succℕ k) x +ℕ ιFin (succℕ k) (add-ℤ-mod (succℕ k) y z))
      (add-≡-right-modℕ (succℕ k)
        (ιFin (succℕ k) (add-ℤ-mod (succℕ k) x y))
        (ιFin (succℕ k) x +ℕ ιFin (succℕ k) y)
        (ιFin (succℕ k) z)
        (ι-ℤmod-add k x y))
      (mod-is-transℕ (succℕ k)
        ((ιFin (succℕ k) x +ℕ ιFin (succℕ k) y) +ℕ ιFin (succℕ k) z)
        (ιFin (succℕ k) x +ℕ (ιFin (succℕ k) y +ℕ ιFin (succℕ k) z))
        (ιFin (succℕ k) x +ℕ ιFin (succℕ k) (add-ℤ-mod (succℕ k) y z))
        (eqℕ-to-eq-modℕ (succℕ k)
          ((ιFin (succℕ k) x +ℕ ιFin (succℕ k) y) +ℕ ιFin (succℕ k) z)
          (ιFin (succℕ k) x +ℕ (ιFin (succℕ k) y +ℕ ιFin (succℕ k) z))
          (add-assocℕ (ιFin (succℕ k) x) (ιFin (succℕ k) y) (ιFin (succℕ k) z)))
        (mod-is-symmℕ (succℕ k)
          (ιFin (succℕ k) x +ℕ ιFin (succℕ k) (add-ℤ-mod (succℕ k) y z))
          (ιFin (succℕ k) x +ℕ (ιFin (succℕ k) y +ℕ ιFin (succℕ k) z))
          (add-≡-left-modℕ (succℕ k)
            (ιFin (succℕ k) x)
            (ιFin (succℕ k) (add-ℤ-mod (succℕ k) y z))
            (ιFin (succℕ k) y +ℕ ιFin (succℕ k) z)
            (ι-ℤmod-add k y z)))))

add-dist-succℕ : (x k : ℕ) → x <ℕ succℕ k → x +ℕ distℕ x (succℕ k) ≡ succℕ k
add-dist-succℕ x k p = add-distℕ x (succℕ k) (≤-transℕ {x} {k} {succℕ k} (<-to-succ-≤ℕ x (succℕ k) p) (≤-succℕ k))

add-neg-ℤmod : (k : ℕ) → (x : ℤ-mod k) → add-ℤ-mod k x (neg-ℤ-mod k x) ≡ zero-ℤmod k
add-neg-ℤmod 0ℕ x = add-negℤ x
add-neg-ℤmod (succℕ k) x =
  proj₂ (Fin-k-is-ℕmod-k k
    (ιFin (succℕ k) x +ℕ ιFin (succℕ k) (neg-ℤ-mod (succℕ k) x))
    0ℕ)
    (mod-is-transℕ (succℕ k)
      (ιFin (succℕ k) x +ℕ ιFin (succℕ k) (neg-ℤ-mod (succℕ k) x))
      (ιFin (succℕ k) x +ℕ distℕ (ιFin (succℕ k) x) (succℕ k))
      0ℕ
      (mod-is-symmℕ (succℕ k)
        (ιFin (succℕ k) x +ℕ distℕ (ιFin (succℕ k) x) (succℕ k))
        (ιFin (succℕ k) x +ℕ ιFin (succℕ k) (neg-ℤ-mod (succℕ k) x))
        (add-≡-left-modℕ (succℕ k)
          (ιFin (succℕ k) x)
          (distℕ (ιFin (succℕ k) x) (succℕ k))
          (ιFin (succℕ k) (neg-ℤ-mod (succℕ k) x))
          (mod-is-symmℕ (succℕ k)
            (ιFin (succℕ k) (neg-ℤ-mod (succℕ k) x))
            (distℕ (ιFin (succℕ k) x) (succℕ k))
            (ι-ℤmod-neg k x))))
      (mod-is-transℕ (succℕ k)
        (ιFin (succℕ k) x +ℕ distℕ (ιFin (succℕ k) x) (succℕ k))
        (succℕ k)
        0ℕ
        (eqℕ-to-eq-modℕ (succℕ k)
          (ιFin (succℕ k) x +ℕ distℕ (ιFin (succℕ k) x) (succℕ k))
          (succℕ k)
          (add-dist-succℕ (ιFin (succℕ k) x) k (Fin-to-ℕ-bounded (succℕ k) x)))
        (k-is-zero-mod-kℕ (succℕ k))))

neg-add-ℤmod : (k : ℕ) → (x : ℤ-mod k) → add-ℤ-mod k (neg-ℤ-mod k x) x ≡ zero-ℤmod k
neg-add-ℤmod 0ℕ x = neg-addℤ x
neg-add-ℤmod (succℕ k) x =
  concat
    {Fin (succℕ k)}
    {add-ℤ-mod (succℕ k) (neg-ℤ-mod (succℕ k) x) x}
    {add-ℤ-mod (succℕ k) x (neg-ℤ-mod (succℕ k) x)}
    {zero-ℤmod (succℕ k)}
    (comm-ℤmod (succℕ k) (neg-ℤ-mod (succℕ k) x) x)
    (add-neg-ℤmod (succℕ k) x)

-- Ex 7.1
div-sum-rightℕ : (x y d : ℕ) → (d ∣ x) → (d ∣ (x +ℕ y)) → (d ∣ y)
div-sum-rightℕ x y d dx dxy = div-sum-partℕ y x d (tr (d ∣_) (add-commℕ x y) dxy) dx

-- Ex 7.2
is-antisymmetric : {A : Set} → (A → A → Set) → Set
is-antisymmetric {A} R = (x y : A) → R x y → R y x → x ≡ y

div-rflℕ : (d : ℕ) → d ∣ d
div-rflℕ d = (1ℕ , one-mulℕ d)

div-antisymℕ : (d n : ℕ) → d ∣ n → n ∣ d → d ≡ n
div-antisymℕ 0ℕ n (kd , pd) (kn , pn) = pd
div-antisymℕ (succℕ d') n (kd , pd) (kn , pn) =
  inv (concat (inv pd) (concat (ap (λ k → k ·ℕ succℕ d') kd≡1) (one-mulℕ (succℕ d'))))
  where
    kn·kd≡1 : kn ·ℕ kd ≡ 1ℕ
    kn·kd≡1 = proj₂ (mul-injℕ (kn ·ℕ kd) 1ℕ d')
      (concat (mul-assocℕ kn kd (succℕ d'))
      (concat (ap (kn ·ℕ_) pd)
      (concat pn (inv (one-mulℕ (succℕ d'))))))
    kd≡1 : kd ≡ 1ℕ
    kd≡1 = proj₂ (mul-to-oneℕ kn kd kn·kd≡1)

div-transℕ : (d n m : ℕ) → d ∣ n → n ∣ m → d ∣ m
div-transℕ d n m (kd , pd) (kn , pn) =
  ((kn ·ℕ kd) , concat (mul-assocℕ kn kd d) (concat (ap (kn ·ℕ_) pd) pn))

le-to-div-fact : (n : ℕ) → (x : ℕ) → ¬ (x ≡ 0ℕ) → (x ≤ℕ n) → (x ∣ factorialℕ n)
le-to-div-fact n 0ℕ ne0 x≤n = (0ℕ , ex-falso (ne0 refl))
le-to-div-fact 0ℕ (succℕ x) ne0 ()
le-to-div-fact (succℕ n') (succℕ x) ne0 x≤n' with <-or-≤ℕ x n'
... | inl x<n' =
  div-transℕ (succℕ x) (factorialℕ n') (factorialℕ (succℕ n'))
    (le-to-div-fact n' (succℕ x) ne0 (<-to-succ-≤ℕ x n' x<n'))
    (succℕ n' , refl)
... | inr n'≤x =
  tr (λ m → succℕ m ∣ factorialℕ (succℕ n')) (inv (≤-antisymℕ x n' x≤n' n'≤x))
    (factorialℕ n' , mul-commℕ (factorialℕ n') (succℕ n'))

1-Fin : (k : ℕ) → Fin (succℕ k)
1-Fin k = [ 1ℕ ] (succℕ k)

succ-eq-add-one-Fin : (k : ℕ) → (x : Fin (succℕ k)) → (succFin (succℕ k) x) ≡ x +ℤmod (1-Fin k)
succ-eq-add-one-Fin k x =
  Fin-to-ℕ-injective (succℕ k) (succFin (succℕ k) x) (add-ℤ-mod (succℕ k) x (1-Fin k))
    (eq-modℕ-to-eqℕ (succℕ k)
      (ιFin (succℕ k) (succFin (succℕ k) x))
      (ιFin (succℕ k) (add-ℤ-mod (succℕ k) x (1-Fin k)))
      (mod-is-transℕ (succℕ k)
        (ιFin (succℕ k) (succFin (succℕ k) x))
        (ιFin (succℕ k) x +ℕ 1ℕ)
        (ιFin (succℕ k) (add-ℤ-mod (succℕ k) x (1-Fin k)))
        (succFin-to-succℕ-mod (succℕ k) x)
        (mod-is-symmℕ (succℕ k)
          (ιFin (succℕ k) (add-ℤ-mod (succℕ k) x (1-Fin k)))
          (ιFin (succℕ k) x +ℕ 1ℕ)
          (mod-is-transℕ (succℕ k)
            (ιFin (succℕ k) (add-ℤ-mod (succℕ k) x (1-Fin k)))
            (ιFin (succℕ k) x +ℕ ιFin (succℕ k) (1-Fin k))
            (ιFin (succℕ k) x +ℕ 1ℕ)
            (ι-ℤmod-add k x (1-Fin k))
            (add-≡-left-modℕ (succℕ k)
              (ιFin (succℕ k) x)
              (ιFin (succℕ k) (1-Fin k))
              1ℕ
              (Fin-to-modℕ k 1ℕ)))))
      (dist-bounded-<ℕ
        (ιFin (succℕ k) (succFin (succℕ k) x))
        (ιFin (succℕ k) (add-ℤ-mod (succℕ k) x (1-Fin k)))
        (succℕ k)
        (Fin-to-ℕ-bounded (succℕ k) (succFin (succℕ k) x))
        (Fin-to-ℕ-bounded (succℕ k) (add-ℤ-mod (succℕ k) x (1-Fin k)))))

Eq-Fin : (k : ℕ) → Fin k → Fin k → Set lzero
Eq-Fin (succℕ k) (inl x) (inl y) = Eq-Fin k x y
Eq-Fin (succℕ k) (inl x) (inr *) = 𝟘
Eq-Fin (succℕ k) (inr *) (inl y) = 𝟘
Eq-Fin (succℕ k) (inr *) (inr *) = 𝟙

Eq-Fin-to-≡Fin : (k : ℕ) → (x y : Fin k) → Eq-Fin k x y → x ≡ y
Eq-Fin-to-≡Fin 0ℕ () y p
Eq-Fin-to-≡Fin (succℕ k) (inl x) (inl y) p = ap inl (Eq-Fin-to-≡Fin k x y p)
Eq-Fin-to-≡Fin (succℕ k) (inl x) (inr *) ()
Eq-Fin-to-≡Fin (succℕ k) (inr *) (inl y) ()
Eq-Fin-to-≡Fin (succℕ k) (inr *) (inr *) * = refl

≡Fin-to-Eq-Fin : (k : ℕ) → (x y : Fin k) → x ≡ y → Eq-Fin k x y
≡Fin-to-Eq-Fin (succℕ k) (inl x) (inl y) refl = ≡Fin-to-Eq-Fin k x y refl
≡Fin-to-Eq-Fin (succℕ k) (inr *) (inr y) refl = *

ιFin-injective : (k : ℕ) → (x y : Fin k) → ιFin k x ≡ ιFin k y → x ≡ y
ιFin-injective (succℕ k) (inl x) (inl y) p = ap inl (ιFin-injective k x y p)
ιFin-injective (succℕ k) (inl x) (inr *) p =
  indEmpty (<-antirflℕ k (tr (λ m → m <ℕ k) p (Fin-to-ℕ-bounded k x)))
ιFin-injective (succℕ k) (inr *) (inl y) p =
  indEmpty (<-antirflℕ k (tr (λ m → m <ℕ k) (inv p) (Fin-to-ℕ-bounded k y)))
ιFin-injective (succℕ k) (inr *) (inr *) p = refl

succ-inl-ne-zeroFin : (k : ℕ) → (x : Fin k) → ¬ (succFin (succℕ k) (inl x) ≡ zeroFin k)
succ-inl-ne-zeroFin k x p =
  zero-ne-succℕ (ιFin k x)
    (concat (inv (zeroFin-to-0ℕ k))
    (concat (inv (ap (ιFin (succℕ k)) p))
            (skip-zeroFin-to-add-oneℕ k x)))

succFin-injective : (k : ℕ) → (x y : Fin k) → succFin k x ≡ succFin k y → x ≡ y
succFin-injective (succℕ k) (inl x) (inl y) p =
  ap inl (ιFin-injective k x y
    (proj₂ (succ-injℕ (ιFin k x) (ιFin k y))
      (concat (inv (skip-zeroFin-to-add-oneℕ k x))
      (concat (ap (ιFin (succℕ k)) p)
              (skip-zeroFin-to-add-oneℕ k y)))))
succFin-injective (succℕ k) (inl x) (inr *) p =
  indEmpty (succ-inl-ne-zeroFin k x p)
succFin-injective (succℕ k) (inr *) (inl y) p =
  indEmpty (succ-inl-ne-zeroFin k y (inv p))
succFin-injective (succℕ k) (inr *) (inr *) p = refl

neg-twoFin : (k : ℕ) → Fin (succℕ k)
neg-twoFin 0ℕ = inr *
neg-twoFin (succℕ k) = inl (inr *)

skip-neg-twoFin : (k : ℕ) → Fin k → Fin (succℕ k)
skip-neg-twoFin 0ℕ ()
skip-neg-twoFin (succℕ k) (inl x) = inl (inl x)
skip-neg-twoFin (succℕ k) (inr *) = inr *

predFin : (k : ℕ) → Fin k → Fin k
predFin 0ℕ ()
predFin (succℕ k) (inl x) = skip-neg-twoFin k (predFin k x)
predFin (succℕ k) (inr *) = neg-twoFin k

succ-skip-neg-twoFin : (k : ℕ) → (z : Fin k) → succFin (succℕ k) (skip-neg-twoFin k z) ≡ inl (succFin k z)
succ-skip-neg-twoFin (succℕ k) (inl y) = refl
succ-skip-neg-twoFin (succℕ k) (inr *) = refl

succ-predFin : (k : ℕ) → (x : Fin k) → (succFin k (predFin k x)) ≡ x
succ-predFin 0ℕ ()
succ-predFin (succℕ 0ℕ) (inr *) = refl
succ-predFin (succℕ (succℕ k)) (inl x) =
  concat (succ-skip-neg-twoFin (succℕ k) (predFin (succℕ k) x))
         (ap inl (succ-predFin (succℕ k) x))
succ-predFin (succℕ (succℕ k)) (inr *) = refl

pred-succFin : (k : ℕ) → (x : Fin k) → (predFin k (succFin k x)) ≡ x
pred-succFin 0ℕ ()
pred-succFin (succℕ 0ℕ) (inr *) = refl
pred-succFin (succℕ (succℕ k)) (inl (inl y)) =
  ap (skip-neg-twoFin (succℕ k)) (pred-succFin (succℕ k) (inl y))
pred-succFin (succℕ (succℕ k)) (inl (inr *)) = refl
pred-succFin (succℕ (succℕ k)) (inr *) =
  ap (skip-neg-twoFin (succℕ k)) (pred-succFin (succℕ k) (inr *))

-- Ex 7.7 (a)
<-propℕ : (m n : ℕ) → (p q : m <ℕ n) → p ≡ q
<-propℕ 0ℕ 0ℕ () q
<-propℕ 0ℕ (succℕ n) * * = refl
<-propℕ (succℕ m) 0ℕ () q
<-propℕ (succℕ m) (succℕ n) p q = <-propℕ m n p q

≡-classical-Fin : (k : ℕ) → (x y : classical-Fin k) → (proj₁ x ≡ proj₁ y) → x ≡ y
≡-classical-Fin k (a , p) (b , q) e =
  concat (lift (λ z → z <ℕ k) e p)
         (ap (λ r → (b , r)) (<-propℕ b k (tr (λ z → z <ℕ k) e p) q))

≡-iff-proj₁-classical-Fin : (k : ℕ) → (x y : classical-Fin k) → (x ≡ y) ↔ (proj₁ x ≡ proj₁ y)
≡-iff-proj₁-classical-Fin k x y = (ap proj₁ , ≡-classical-Fin k x y)

-- Ex 7.7 (b)
Fin-to-classical-Fin : (k : ℕ) → Fin k → classical-Fin k
Fin-to-classical-Fin k x = (Fin-to-ℕ k x , Fin-to-ℕ-bounded k x)

bounded-ℕ-to-Fin : (k : ℕ) → (n : ℕ) → n <ℕ k → Fin k
bounded-ℕ-to-Fin 0ℕ 0ℕ ()
bounded-ℕ-to-Fin 0ℕ (succℕ n) ()
bounded-ℕ-to-Fin (succℕ k) 0ℕ p = zeroFin k
bounded-ℕ-to-Fin (succℕ k) (succℕ n) p = skip-zeroFin k (bounded-ℕ-to-Fin k n p)

classical-Fin-to-Fin : (k : ℕ) → classical-Fin k → Fin k
classical-Fin-to-Fin k (n , p) = bounded-ℕ-to-Fin k n p

ι-bounded-ℕ-to-Fin : (k : ℕ) → (n : ℕ) → (p : n <ℕ k) → Fin-to-ℕ k (bounded-ℕ-to-Fin k n p) ≡ n
ι-bounded-ℕ-to-Fin 0ℕ 0ℕ ()
ι-bounded-ℕ-to-Fin 0ℕ (succℕ n) ()
ι-bounded-ℕ-to-Fin (succℕ k) 0ℕ p = zeroFin-to-0ℕ k
ι-bounded-ℕ-to-Fin (succℕ k) (succℕ n) p =
  concat (skip-zeroFin-to-add-oneℕ k (bounded-ℕ-to-Fin k n p))
         (ap succℕ (ι-bounded-ℕ-to-Fin k n p))

α-ιFin : (k : ℕ) → (x : Fin k) → classical-Fin-to-Fin k (Fin-to-classical-Fin k x) ≡ x
α-ιFin k x =
  Fin-to-ℕ-injective k
    (bounded-ℕ-to-Fin k (Fin-to-ℕ k x) (Fin-to-ℕ-bounded k x)) x
    (ι-bounded-ℕ-to-Fin k (Fin-to-ℕ k x) (Fin-to-ℕ-bounded k x))

ι-αFin : (k : ℕ) → (y : classical-Fin k) → Fin-to-classical-Fin k (classical-Fin-to-Fin k y) ≡ y
ι-αFin k (n , p) =
  ≡-classical-Fin k
    (Fin-to-classical-Fin k (bounded-ℕ-to-Fin k n p)) (n , p)
    (ι-bounded-ℕ-to-Fin k n p)

infix 7 _·ℤmod_
_·ℤmod_ : {k : ℕ} → (x y : ℤ-mod k) → ℤ-mod k
_·ℤmod_ {0ℕ} x y = x ·ℤ y
_·ℤmod_ {succℕ k} x y = [ ιFin (succℕ k) x ·ℕ ιFin (succℕ k) y ] (succℕ k)

-- Ex 7.8 (a)
ι-ℤmod-mul : (k : ℕ) → (x y : ℤ-mod (succℕ k)) → ι-ℤmod k (x ·ℤmod y) ≡ℕ ι-ℤmod k x ·ℕ ι-ℤmod k y mod (succℕ k)
ι-ℤmod-mul k x y = Fin-to-modℕ k (ιFin (succℕ k) x ·ℕ ιFin (succℕ k) y)

-- Ex 7.8 (b)
mul-≡-right-modℕ : (k a b c : ℕ) → a ≡ℕ b mod k → (a ·ℕ c) ≡ℕ (b ·ℕ c) mod k
mul-≡-right-modℕ k a b c (j , p) = ((c ·ℕ j) , proof)
  where
  proof : (c ·ℕ j) ·ℕ k ≡ distℕ (a ·ℕ c) (b ·ℕ c)
  proof =
    concat (mul-assocℕ c j k)
    (concat (ap (c ·ℕ_) p)
    (concat (inv (dist-linearℕ a b c))
    (concat (ap (λ n → distℕ n (c ·ℕ b)) (mul-commℕ c a))
            (ap (distℕ (a ·ℕ c)) (mul-commℕ c b)))))

mul-≡-left-modℕ : (k c a b : ℕ) → a ≡ℕ b mod k → (c ·ℕ a) ≡ℕ (c ·ℕ b) mod k
mul-≡-left-modℕ k c a b p =
  tr (k ∣_)
    (concat (ap (λ n → distℕ n (b ·ℕ c)) (mul-commℕ a c))
            (ap (distℕ (c ·ℕ a)) (mul-commℕ b c)))
    (mul-≡-right-modℕ k a b c p)

mul-≡-modℕ : (k a b c d : ℕ) → a ≡ℕ b mod k → c ≡ℕ d mod k → (a ·ℕ c) ≡ℕ (b ·ℕ d) mod k
mul-≡-modℕ k a b c d pab pcd =
  mod-is-transℕ k (a ·ℕ c) (b ·ℕ c) (b ·ℕ d)
    (mul-≡-right-modℕ k a b c pab)
    (mul-≡-left-modℕ k b c d pcd)

-- Ex 7.8 (c)
one-ℤmod : (k : ℕ) → ℤ-mod k
one-ℤmod 0ℕ = 1ℤ
one-ℤmod (succℕ k) = 1-Fin k

mul-ℤ-mod : (k : ℕ) → ℤ-mod k → ℤ-mod k → ℤ-mod k
mul-ℤ-mod k x y = _·ℤmod_ {k} x y

comm-mul-ℤmod : (k : ℕ) → (x y : ℤ-mod k) → mul-ℤ-mod k x y ≡ mul-ℤ-mod k y x
comm-mul-ℤmod 0ℕ x y = mul-commℤ x y
comm-mul-ℤmod (succℕ k) x y = ap (ℕ-to-Fin k) (mul-commℕ (ιFin (succℕ k) x) (ιFin (succℕ k) y))

mul-one-ℤmod : (k : ℕ) → (x : ℤ-mod k) → mul-ℤ-mod k x (one-ℤmod k) ≡ x
mul-one-ℤmod 0ℕ x = refl
mul-one-ℤmod (succℕ k) x =
  concat
    (proj₂ (Fin-k-is-ℕmod-k k
      (ιFin (succℕ k) x ·ℕ ιFin (succℕ k) (1-Fin k))
      (ιFin (succℕ k) x))
      (mul-≡-left-modℕ (succℕ k)
        (ιFin (succℕ k) x)
        (ιFin (succℕ k) (1-Fin k))
        1ℕ
        (Fin-to-modℕ k 1ℕ)))
    (proj₂ (ℕ-to-Fin-split-surj k x))

one-mul-ℤmod : (k : ℕ) → (x : ℤ-mod k) → mul-ℤ-mod k (one-ℤmod k) x ≡ x
one-mul-ℤmod k x = concat (comm-mul-ℤmod k (one-ℤmod k) x) (mul-one-ℤmod k x)

assoc-mul-ℤmod : (k : ℕ) → (x y z : ℤ-mod k) → mul-ℤ-mod k (mul-ℤ-mod k x y) z ≡ mul-ℤ-mod k x (mul-ℤ-mod k y z)
assoc-mul-ℤmod 0ℕ x y z = mul-assocℤ x y z
assoc-mul-ℤmod (succℕ k) x y z =
  proj₂ (Fin-k-is-ℕmod-k k
    (ιFin (succℕ k) (x ·ℤmod y) ·ℕ ιFin (succℕ k) z)
    (ιFin (succℕ k) x ·ℕ ιFin (succℕ k) (y ·ℤmod z)))
    (mod-is-transℕ (succℕ k)
      (ιFin (succℕ k) (x ·ℤmod y) ·ℕ ιFin (succℕ k) z)
      ((ιFin (succℕ k) x ·ℕ ιFin (succℕ k) y) ·ℕ ιFin (succℕ k) z)
      (ιFin (succℕ k) x ·ℕ ιFin (succℕ k) (y ·ℤmod z))
      (mul-≡-right-modℕ (succℕ k)
        (ιFin (succℕ k) (x ·ℤmod y))
        (ιFin (succℕ k) x ·ℕ ιFin (succℕ k) y)
        (ιFin (succℕ k) z)
        (ι-ℤmod-mul k x y))
      (mod-is-transℕ (succℕ k)
        ((ιFin (succℕ k) x ·ℕ ιFin (succℕ k) y) ·ℕ ιFin (succℕ k) z)
        (ιFin (succℕ k) x ·ℕ (ιFin (succℕ k) y ·ℕ ιFin (succℕ k) z))
        (ιFin (succℕ k) x ·ℕ ιFin (succℕ k) (y ·ℤmod z))
        (eqℕ-to-eq-modℕ (succℕ k)
          ((ιFin (succℕ k) x ·ℕ ιFin (succℕ k) y) ·ℕ ιFin (succℕ k) z)
          (ιFin (succℕ k) x ·ℕ (ιFin (succℕ k) y ·ℕ ιFin (succℕ k) z))
          (mul-assocℕ (ιFin (succℕ k) x) (ιFin (succℕ k) y) (ιFin (succℕ k) z)))
        (mod-is-symmℕ (succℕ k)
          (ιFin (succℕ k) x ·ℕ ιFin (succℕ k) (y ·ℤmod z))
          (ιFin (succℕ k) x ·ℕ (ιFin (succℕ k) y ·ℕ ιFin (succℕ k) z))
          (mul-≡-left-modℕ (succℕ k)
            (ιFin (succℕ k) x)
            (ιFin (succℕ k) (y ·ℤmod z))
            (ιFin (succℕ k) y ·ℕ ιFin (succℕ k) z)
            (ι-ℤmod-mul k y z)))))

add-≡-modℕ : (k a b c d : ℕ) → a ≡ℕ b mod k → c ≡ℕ d mod k → (a +ℕ c) ≡ℕ (b +ℕ d) mod k
add-≡-modℕ k a b c d pab pcd =
  mod-is-transℕ k (a +ℕ c) (b +ℕ c) (b +ℕ d)
    (add-≡-right-modℕ k a b c pab)
    (add-≡-left-modℕ k b c d pcd)

left-distrib-ℤmod : (k : ℕ) → (x y z : ℤ-mod k) → mul-ℤ-mod k x (add-ℤ-mod k y z) ≡ add-ℤ-mod k (mul-ℤ-mod k x y) (mul-ℤ-mod k x z)
left-distrib-ℤmod 0ℕ x y z = left-distribℤ x y z
left-distrib-ℤmod (succℕ k) x y z =
  proj₂ (Fin-k-is-ℕmod-k k
    (ιFin (succℕ k) x ·ℕ ιFin (succℕ k) (y +ℤmod z))
    (ιFin (succℕ k) (x ·ℤmod y) +ℕ ιFin (succℕ k) (x ·ℤmod z)))
    (mod-is-transℕ (succℕ k)
      (ιFin (succℕ k) x ·ℕ ιFin (succℕ k) (y +ℤmod z))
      (ιFin (succℕ k) x ·ℕ (ιFin (succℕ k) y +ℕ ιFin (succℕ k) z))
      (ιFin (succℕ k) (x ·ℤmod y) +ℕ ιFin (succℕ k) (x ·ℤmod z))
      (mul-≡-left-modℕ (succℕ k)
        (ιFin (succℕ k) x)
        (ιFin (succℕ k) (y +ℤmod z))
        (ιFin (succℕ k) y +ℕ ιFin (succℕ k) z)
        (ι-ℤmod-add k y z))
      (mod-is-transℕ (succℕ k)
        (ιFin (succℕ k) x ·ℕ (ιFin (succℕ k) y +ℕ ιFin (succℕ k) z))
        (ιFin (succℕ k) x ·ℕ ιFin (succℕ k) y +ℕ ιFin (succℕ k) x ·ℕ ιFin (succℕ k) z)
        (ιFin (succℕ k) (x ·ℤmod y) +ℕ ιFin (succℕ k) (x ·ℤmod z))
        (eqℕ-to-eq-modℕ (succℕ k)
          (ιFin (succℕ k) x ·ℕ (ιFin (succℕ k) y +ℕ ιFin (succℕ k) z))
          (ιFin (succℕ k) x ·ℕ ιFin (succℕ k) y +ℕ ιFin (succℕ k) x ·ℕ ιFin (succℕ k) z)
          (left-distribℕ (ιFin (succℕ k) x) (ιFin (succℕ k) y) (ιFin (succℕ k) z)))
        (mod-is-symmℕ (succℕ k)
          (ιFin (succℕ k) (x ·ℤmod y) +ℕ ιFin (succℕ k) (x ·ℤmod z))
          (ιFin (succℕ k) x ·ℕ ιFin (succℕ k) y +ℕ ιFin (succℕ k) x ·ℕ ιFin (succℕ k) z)
          (add-≡-modℕ (succℕ k)
            (ιFin (succℕ k) (x ·ℤmod y))
            (ιFin (succℕ k) x ·ℕ ιFin (succℕ k) y)
            (ιFin (succℕ k) (x ·ℤmod z))
            (ιFin (succℕ k) x ·ℕ ιFin (succℕ k) z)
            (ι-ℤmod-mul k x y)
            (ι-ℤmod-mul k x z)))))

right-distrib-ℤmod : (k : ℕ) → (x y z : ℤ-mod k) → mul-ℤ-mod k (add-ℤ-mod k x y) z ≡ add-ℤ-mod k (mul-ℤ-mod k x z) (mul-ℤ-mod k y z)
right-distrib-ℤmod k x y z =
  concat (comm-mul-ℤmod k (add-ℤ-mod k x y) z)
  (concat (left-distrib-ℤmod k z x y)
  (concat (ap (λ (w : ℤ-mod k) → add-ℤ-mod k w (mul-ℤ-mod k z y)) (comm-mul-ℤmod k z x))
          (ap (λ (w : ℤ-mod k) → add-ℤ-mod k (mul-ℤ-mod k x z) w) (comm-mul-ℤmod k z y))))

-- Ex 7.9 (a)
mod-add-mulℕ : (k q r : ℕ) → (q ·ℕ k +ℕ r) ≡ℕ r mod k
mod-add-mulℕ k q r = tr (k ∣_) (inv (dist-add-rightℕ (q ·ℕ k) r)) (q , refl)

euclidean-divℕ : (a b : ℕ) → ¬ (b ≡ 0ℕ) → Σ ℕ (λ q → Σ ℕ (λ r → (a ≡ q ·ℕ b +ℕ r) × (r <ℕ b)))
euclidean-divℕ 0ℕ 0ℕ ne = ex-falso (ne refl)
euclidean-divℕ 0ℕ (succℕ b) ne = (0ℕ , (0ℕ , (inv (zero-mulℕ (succℕ b)) , *)))
euclidean-divℕ (succℕ a) 0ℕ ne = ex-falso (ne refl)
euclidean-divℕ (succℕ a) (succℕ b) ne = eucl-step (euclidean-divℕ a (succℕ b) ne)
  where
  eucl-step : Σ ℕ (λ q → Σ ℕ (λ r → (a ≡ q ·ℕ succℕ b +ℕ r) × (r <ℕ succℕ b))) →
              Σ ℕ (λ q → Σ ℕ (λ r → (succℕ a ≡ q ·ℕ succℕ b +ℕ r) × (r <ℕ succℕ b)))
  eucl-step (q , (r , (eq , rlt))) with <-or-≤ℕ r b
  ... | inl r<b = (q , (succℕ r , (ap succℕ eq , r<b)))
  ... | inr b≤r =
    let r≡b = ≤-antisymℕ r b (<-to-succ-≤ℕ r (succℕ b) rlt) b≤r
    in (succℕ q , (0ℕ , (concat (ap succℕ (concat eq (ap (q ·ℕ succℕ b +ℕ_) r≡b)))
                                (inv (succ-mulℕ q (succℕ b))) , *)))

-- Ex 7.9 (b)
euclidean-div-uniqueℕ : (a b q q' r r' : ℕ) → ¬ (b ≡ 0ℕ) →
  a ≡ q ·ℕ b +ℕ r → a ≡ q' ·ℕ b +ℕ r' → r <ℕ b → r' <ℕ b →
  (q ≡ q') × (r ≡ r')
euclidean-div-uniqueℕ a 0ℕ q q' r r' ne eq1 eq2 rlt rlt' = ex-falso (ne refl)
euclidean-div-uniqueℕ a (succℕ b) q q' r r' ne eq1 eq2 rlt rlt' = (q≡q' , r≡r')
  where
  r-mod : r ≡ℕ r' mod (succℕ b)
  r-mod = mod-is-transℕ (succℕ b) r (q ·ℕ succℕ b +ℕ r) r'
    (mod-is-symmℕ (succℕ b) (q ·ℕ succℕ b +ℕ r) r (mod-add-mulℕ (succℕ b) q r))
    (mod-is-transℕ (succℕ b) (q ·ℕ succℕ b +ℕ r) (q' ·ℕ succℕ b +ℕ r') r'
      (eqℕ-to-eq-modℕ (succℕ b) (q ·ℕ succℕ b +ℕ r) (q' ·ℕ succℕ b +ℕ r') (concat (inv eq1) eq2))
      (mod-add-mulℕ (succℕ b) q' r'))

  r≡r' : r ≡ r'
  r≡r' = eq-modℕ-to-eqℕ (succℕ b) r r' r-mod (dist-bounded-<ℕ r r' (succℕ b) rlt rlt')

  q≡q' : q ≡ q'
  q≡q' = proj₂ (mul-injℕ q q' b)
    (proj₂ (add-injℕ (q ·ℕ succℕ b) (q' ·ℕ succℕ b) r)
      (concat (inv eq1) (concat eq2 (ap (q' ·ℕ succℕ b +ℕ_) (inv r≡r')))))

