{-# OPTIONS --without-K #-}
module ch15 where

open import ch14 public

-- 15.1 The image of a map

-- Definition 15.1.1: a morphism from f to g over X is hom X f g (ch13),
-- a map h : A → B with a homotopy f ∼ g ∘ h

-- Definition 15.1.2: given φ = (q , H) : hom X f i with i an embedding, i is an image of f
-- if precomposing with φ is an equivalence hom X i m ≃ hom X f m for every embedding m.
-- The book assumes i is an embedding; that hypothesis goes on the lemmas, not here.
-- The level ℓ₃ of the test embeddings m is implicit: Agda infers it once m is supplied.
is-image : {A : Set ℓ} {I : Set ℓ₁} {X : Set ℓ₂} → (f : A → X) → (i : I → X) → hom X f i
  → Set (ℓ ⊔ ℓ₁ ⊔ ℓ₂ ⊔ lsuc ℓ₃)
is-image {ℓ₃ = ℓ₃} {X = X} f i φ =
  (B : Set ℓ₃) → (m : B → X) → (memb : is-emb m) → is-equiv (λ (ψ : hom X i m) → hom-comp f i m φ ψ)

-- Lemma 15.1.3
hom-emb-is-prop : {A : Set ℓ₁} {X : Set ℓ₂} {B : Set ℓ₃} → (f : A → X) → (m : B → X) → is-emb m → is-prop (hom X f m)
hom-emb-is-prop f m memb = equiv-to-same-k-type (hom-equiv-Π-fib f m) (Π-prop (λ z → fib m (f z)) λ a → emb-to-fib-prop m memb (f a))

-- Proposition 15.1.4
-- (ii): every morphism from f into an embedding m extends to one from i
has-image-ext : {A : Set ℓ} {I : Set ℓ₁} {X : Set ℓ₂} → (f : A → X) → (i : I → X)
  → Set (ℓ ⊔ ℓ₁ ⊔ ℓ₂ ⊔ lsuc ℓ₃)
has-image-ext {ℓ₃ = ℓ₃} {X = X} f i = (B : Set ℓ₃) → (m : B → X) → is-emb m → hom X f m → hom X i m

-- (i) implies (ii)
is-image-to-has-image-ext : {A : Set ℓ} {I : Set ℓ₁} {X : Set ℓ₂} → (f : A → X) → (i : I → X) → (φ : hom X f i)
  → is-image {ℓ₃ = ℓ₃} f i φ → has-image-ext {ℓ₃ = ℓ₃} f i
is-image-to-has-image-ext f i (h , H) fimage B m memb (g , G) = proj₁ (proj₁ (fimage B m memb)) (g , G)

-- (ii) implies (i)
has-image-ext-to-is-image : {A : Set ℓ} {I : Set ℓ₁} {X : Set ℓ₂} → (f : A → X) → (i : I → X) → (φ : hom X f i)
  → has-image-ext {ℓ₃ = ℓ₃} f i → is-image {ℓ₃ = ℓ₃} f i φ
has-image-ext-to-is-image f i φ fext B m memb = proj₂ (iff-to-≃ (hom-emb-is-prop i m memb) (hom-emb-is-prop f m memb) ((λ z →
     (proj₁ z ∘ proj₁ φ) ,
     concat-htpy (proj₂ φ) (λ a → proj₂ z (proj₁ φ a))) , λ {(g , G) → fext B m memb (g , G)}))

-- Existence of image
im : {A : Set ℓ} {X : Set ℓ₁} → (f : A → X) → Set _
im {A = A} {X = X} f = Σ X (λ x → ∥ fib f x ∥)

im-incl : {A : Set ℓ} {X : Set ℓ₁} → (f : A → X) → im f → X
im-incl f = proj₁

im-unit : {A : Set ℓ} {X : Set ℓ₁} → (f : A → X) → A → im f
im-unit f x = (f x) , (η (x , refl)) 

im-htpy : {A : Set ℓ} {X : Set ℓ₁} → (f : A → X) → f ∼ im-incl f ∘ im-unit f
im-htpy f x = refl

im-incl-is-emb : {A : Set ℓ} {X : Set ℓ₁} → (f : A → X) → is-emb (im-incl f)
im-incl-is-emb f = proj₁-of-subtype-is-emb (λ x → ∥ fib f x ∥) λ x → prop-trunc-is-prop _

-- the triangle (q_f , I_f) as a morphism over X
im-hom : {A : Set ℓ} {X : Set ℓ₁} → (f : A → X) → hom X f (im-incl f)
im-hom f = im-unit f , im-htpy f

-- Theorem 15.1.7
im-incl-is-image : {A : Set ℓ} {X : Set ℓ₁} → (f : A → X) → is-image {ℓ₃ = ℓ₂} f (im-incl f) (im-hom f)
im-incl-is-image {ℓ₂ = ℓ₂} f = has-image-ext-to-is-image f (im-incl f) (im-hom f) ext
  where
    ext : has-image-ext {ℓ₃ = ℓ₂} f (im-incl f)
    ext B m memb φm = (λ z → proj₁ (to-fib-m z)) , (λ z → inv (proj₂ (to-fib-m z)))
      where
        to-fib-m : (z : im f) → fib m (proj₁ z)
        to-fib-m (x , t) = rec-prop-trunc (fib m x) (emb-to-fib-prop m memb x) (λ {(a , p) → tr (fib m) p (hom-to-Π-fib f m φm a)}) t

-- Uniqueness of image

-- Theorem 15.1.8: uniqueness of the image, as a 3-for-2 property
-- (iii): equivalences e : B ≃ B' over X, i.e. with i ∼ i' ∘ e
equiv-over : (X : Set ℓ₂) {B : Set ℓ} {B' : Set ℓ₁} → (i : B → X) → (i' : B' → X) → Set (ℓ ⊔ ℓ₁ ⊔ ℓ₂)
equiv-over X {B} {B'} i i' = Σ (B ≃ B') (λ e → i ∼ i' ∘ proj₁ e)

-- B and B' share a level, since each image is tested against the other inclusion
-- (i) and (ii) give (iii)
image-uniq-i-i'-to-e : {A : Set ℓ} {B B' : Set ℓ₁} {X : Set ℓ₂} → (f : A → X)
  → (i : B → X) → (i' : B' → X) → is-emb i → is-emb i'
  → (φ : hom X f i) → (φ' : hom X f i')
  → is-image {ℓ₃ = ℓ₁} f i φ → is-image {ℓ₃ = ℓ₁} f i' φ' → is-contr (equiv-over X i i')
image-uniq-i-i'-to-e {B = B} {B' = B'} {X = X} f i i' iemb i'emb φ φ' iimage i'image =
  is-prop'-to-inhab-contr
    (is-prop-to-is-prop' (equiv-to-same-k-type reassoc
      (fam-trunc-to-Σ-trunc (hom-emb-is-prop i i' i'emb) λ h → equiv-is-prop (proj₁ h))))
    ((proj₁ ψ , ψequiv) , proj₂ ψ)
  where
    -- the morphisms each universal property gives, one in each direction
    ψ : hom X i i'
    ψ = is-image-to-has-image-ext f i φ iimage B' i' i'emb φ'
    ψ' : hom X i' i
    ψ' = is-image-to-has-image-ext f i' φ' i'image B i iemb φ

    -- regroup so that the proposition hom X i i' is the base
    reassoc : equiv-over X i i' ≃ Σ (hom X i i') (λ h → is-equiv (proj₁ h))
    reassoc = (λ { ((h , hequiv) , H) → (h , H) , hequiv }) ,
      (((λ { ((h , H) , hequiv) → (h , hequiv) , H }) , λ { ((h , H) , hequiv) → refl }) ,
       ((λ { ((h , H) , hequiv) → (h , hequiv) , H }) , λ { ((h , hequiv) , H) → refl }))

    -- both composites are the identity, since hom X i i and hom X i' i' are propositions
    ψequiv : is-equiv (proj₁ ψ)
    ψequiv = inverse-to-equiv (proj₁ ψ) (proj₁ ψ' ,
      (htpy-eq _ _ (ap proj₁ (is-prop-to-is-prop' (hom-emb-is-prop i' i' i'emb) (hom-comp i' i i' ψ' ψ) (id , λ x → refl))) ,
       htpy-eq _ _ (ap proj₁ (is-prop-to-is-prop' (hom-emb-is-prop i i iemb) (hom-comp i i' i ψ ψ') (id , λ x → refl)))))

-- (i) and (iii) give (ii)
image-uniq-i-e-to-i' : {A : Set ℓ} {B B' : Set ℓ₁} {X : Set ℓ₂} → (f : A → X)
  → (i : B → X) → (i' : B' → X) → is-emb i → is-emb i'
  → (φ : hom X f i) → (φ' : hom X f i')
  → is-image {ℓ₃ = ℓ₁} f i φ → is-contr (equiv-over X i i') → is-image {ℓ₃ = ℓ₁} f i' φ'
image-uniq-i-e-to-i' {X = X} f i i' iemb i'emb φ φ' iimage econtr = has-image-ext-to-is-image f i' φ' λ B'' m memb χ → hom-comp i' i m back (is-image-to-has-image-ext f i φ iimage B'' m memb χ)
    where
        back : hom X i' i
        back with proj₁ econtr
        ... | ((e , ((g , eg) , _)) , H) = g , λ b' → concat (ap i' (inv (eg b'))) (inv (H (g b')))

-- (ii) and (iii) give (i)
image-uniq-i'-e-to-i : {A : Set ℓ} {B B' : Set ℓ₁} {X : Set ℓ₂} → (f : A → X)
  → (i : B → X) → (i' : B' → X) → is-emb i → is-emb i'
  → (φ : hom X f i) → (φ' : hom X f i')
  → is-image {ℓ₃ = ℓ₁} f i' φ' → is-contr (equiv-over X i i') → is-image {ℓ₃ = ℓ₁} f i φ
image-uniq-i'-e-to-i {X = X} f i i' iemb i'emb φ φ' i'image econtr = has-image-ext-to-is-image f i φ λ B'' m memb χ → hom-comp i i' m back (is-image-to-has-image-ext f i' φ' i'image B'' m memb χ)
    where
        back : hom X i i'
        back with proj₁ econtr
        ... | ((e , ((g , eg) , (h , he))) , H) = e , λ b → H b

