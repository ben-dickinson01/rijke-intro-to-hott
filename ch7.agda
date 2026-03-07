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
