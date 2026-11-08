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

-- every morphism from an embedding to itself is the identity, since hom X m m is a proposition
hom-emb-endo-htpy-id : {B : Set ℓ} {X : Set ℓ₁} → (m : B → X) → is-emb m → (φ : hom X m m) → proj₁ φ ∼ id
hom-emb-endo-htpy-id m memb φ = htpy-eq _ _ (ap proj₁ (is-prop-to-is-prop' (hom-emb-is-prop m m memb) φ (id , λ x → refl)))

-- Proposition 15.1.4
-- (ii): every morphism from f into an embedding m extends to one from i
has-image-ext : {A : Set ℓ} {I : Set ℓ₁} {X : Set ℓ₂} → (f : A → X) → (i : I → X)
  → Set (ℓ ⊔ ℓ₁ ⊔ ℓ₂ ⊔ lsuc ℓ₃)
has-image-ext {ℓ₃ = ℓ₃} {X = X} f i = (B : Set ℓ₃) → (m : B → X) → (memb : is-emb m) → (χ : hom X f m) → hom X i m

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
      (hom-emb-endo-htpy-id i' i'emb (hom-comp i' i i' ψ' ψ) ,
       hom-emb-endo-htpy-id i iemb (hom-comp i i' i ψ ψ')))

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
image-uniq-i'-e-to-i {X = X} f i i' iemb i'emb φ φ' i'image econtr = has-image-ext-to-is-image f i φ λ B'' m memb χ → hom-comp i i' m fwd (is-image-to-has-image-ext f i' φ' i'image B'' m memb χ)
    where
        fwd : hom X i i'
        fwd with proj₁ econtr
        ... | ((e , ((g , eg) , (h , he))) , H) = e , λ b → H b

-- 15.2 Surjective maps

-- Definition 15.2.1
is-surj : {A : Set ℓ} {B : Set ℓ₁} → (f : A → B) → Set _
is-surj {A = A} {B = B} f = (b : B) → ∥ fib f b ∥

-- Example 15.2.2: equivalences, and more generally maps with a section, are surjective
equiv-to-surj : {A : Set ℓ} {B : Set ℓ₁} → (f : A → B) → is-equiv f → is-surj f
equiv-to-surj f ((g , fg) , (h , hf)) b = η (g b , fg b)

sec-to-surj : {A : Set ℓ} {B : Set ℓ₁} → (f : A → B) → sec f → is-surj f
sec-to-surj f (s , fs) b = η (s b , fs b)

-- Proposition 15.2.3
-- (ii): the dependent universal property of a surjective map
-- the level ℓ₂ of the families P is implicit, as with ℓ₃ in is-image
dup-surj : {A : Set ℓ} {B : Set ℓ₁} → (f : A → B) → Set (ℓ ⊔ ℓ₁ ⊔ lsuc ℓ₂)
dup-surj {ℓ₂ = ℓ₂} {B = B} f = (P : B → Set ℓ₂) → (Pprop : (y : B) → is-prop (P y)) → is-equiv (precomp-Π f P)

-- (iii): precomposition with f is k-truncated on families of (k+1)-truncated types
dup-surj-trunc : {A : Set ℓ} {B : Set ℓ₁} → (f : A → B) → Set (ℓ ⊔ ℓ₁ ⊔ lsuc ℓ₂)
dup-surj-trunc {ℓ₂ = ℓ₂} {B = B} f =
  (k : 𝕋) → (P : B → Set ℓ₂) → (Ptrunc : (y : B) → is-trunc (succ𝕋 k) (P y)) → is-trunc-map k (precomp-Π f P)

-- (i) implies (ii)
surj-to-dup-surj : {A : Set ℓ} {B : Set ℓ₁} → (f : A → B) → is-surj f → dup-surj {ℓ₂ = ℓ₂} f
surj-to-dup-surj f fsurj P Pprop =
  proj₂ (iff-to-≃ (Π-prop _ Pprop) (Π-prop _ (λ x → Pprop (f x)))
    (precomp-Π f P ,
     λ t y → rec-prop-trunc (P y) (Pprop y) (λ { (x , p) → tr P p (t x) }) (fsurj y)))

-- (ii) implies (iii), by induction on k
-- the inductive step splits the book's square along its diagonal into two triangles
dup-surj-to-dup-surj-trunc : {A : Set ℓ} {B : Set ℓ₁} → (f : A → B) → dup-surj {ℓ₂ = ℓ₂} f → dup-surj-trunc {ℓ₂ = ℓ₂} f
dup-surj-to-dup-surj-trunc f fdup -2𝕋 P Ptrunc = equiv-to-contr-map (precomp-Π f P) (fdup P Ptrunc)
dup-surj-to-dup-surj-trunc f fdup (succ𝕋 k) P Ptrunc = ap-k-trunc-to-k+1-trunc-map (precomp-Π f P) ap-trunc
  where
    ap-trunc : (g h : (y : _) → P y) → is-trunc-map k (ap (precomp-Π f P) {g} {h})
    ap-trunc g h =
      comm-tri-k-trunc-g-to-k-trunc-f-to-k-trunc-h _ (htpy-eq (precomp-Π f P g) (precomp-Π f P h)) (ap (precomp-Π f P))
        (λ p → refl)
        (equiv-to-k-trunc-map k _ (fun-ext _ _))
        diag-trunc
      where
        diag-trunc : is-trunc-map k (htpy-eq (precomp-Π f P g) (precomp-Π f P h) ∘ ap (precomp-Π f P))
        diag-trunc = comm-tri-k-trunc-g-to-k-trunc-h-to-k-trunc-f _ (precomp-Π f (λ y → g y ≡ h y)) (htpy-eq g h)
          (λ { refl → refl })
          (dup-surj-to-dup-surj-trunc f fdup k (λ y → g y ≡ h y) (λ y → Ptrunc y (g y) (h y)))
          (equiv-to-k-trunc-map k _ (fun-ext g h))

-- (iii) implies (i); the families are tested at level ℓ ⊔ ℓ₁, so that P y can be ∥ fib f y ∥
dup-surj-trunc-to-surj : {A : Set ℓ} {B : Set ℓ₁} → (f : A → B) → dup-surj-trunc {ℓ₂ = ℓ ⊔ ℓ₁} f → is-surj f
dup-surj-trunc-to-surj f fdup =
  proj₁ (proj₁ (contr-map-to-equiv (precomp-Π f (λ y → ∥ fib f y ∥))
    (fdup -2𝕋 _ (λ y → prop-trunc-is-prop _))))
    (λ x → η (x , refl))

-- Corollary 15.2.4: a map into a proposition is a propositional truncation iff it is surjective
-- (i) implies (ii)
prop-trunc-to-surj : {A P : Set ℓ} → (Pprop : is-prop P) → (f : A → P) → is-prop-trunc Pprop f → is-surj f
prop-trunc-to-surj Pprop f fproptrunc =
  dup-surj-trunc-to-surj f (dup-surj-to-dup-surj-trunc f (prop-trunc-to-dep-prop-trunc Pprop f fproptrunc))

-- (ii) implies (i)
surj-to-prop-trunc : {A P : Set ℓ} → (Pprop : is-prop P) → (f : A → P) → is-surj f → is-prop-trunc Pprop f
surj-to-prop-trunc Pprop f fsurj = dep-prop-trunc-to-prop-trunc Pprop f (surj-to-dup-surj f fsurj)

-- Theorem 15.2.5: for f ∼ m ∘ q with m an embedding, m is an image of f iff q is surjective
-- (i) implies (ii); the test domain Σ B (λ y → ∥ fib q y ∥) lives at level ℓ ⊔ ℓ₁
is-image-to-surj : {A : Set ℓ} {B : Set ℓ₁} {X : Set ℓ₂} → (f : A → X) → (q : A → B) → (m : B → X)
  → is-emb m → (H : triangle-commutes f q m) → is-image {ℓ₃ = ℓ ⊔ ℓ₁} f m (q , H) → is-surj q
is-image-to-surj {B = B} {X = X} f q m memb H mimage = proj₁ sec-proj₁-equiv-Π (proj₁ hK , sec-htpy)
  where
    S : Set _
    S = Σ B (λ y → ∥ fib q y ∥)

    incl : S → X
    incl = m ∘ proj₁

    incl-emb : is-emb incl
    incl-emb = emb-comp proj₁ m (proj₁-of-subtype-is-emb (λ y → ∥ fib q y ∥) (λ y → prop-trunc-is-prop _)) memb

    φ : hom X f incl
    φ = (λ x → q x , η (x , refl)) , H

    hK : hom X m incl
    hK = is-image-to-has-image-ext f m (q , H) mimage S incl incl-emb φ

    sec-htpy : proj₁ ∘ proj₁ hK ∼ id
    sec-htpy = hom-emb-endo-htpy-id m memb ((proj₁ ∘ proj₁ hK) , proj₂ hK)

-- (ii) implies (i)
surj-to-is-image : {A : Set ℓ} {B : Set ℓ₁} {X : Set ℓ₂} → (f : A → X) → (q : A → B) → (m : B → X)
  → is-emb m → (H : triangle-commutes f q m) → is-surj q → is-image {ℓ₃ = ℓ₃} f m (q , H)
surj-to-is-image {ℓ₃ = ℓ₃} {A = A} {B = B} {X = X} f q m memb H qsurj = has-image-ext-to-is-image f m (q , H) ext
  where
    -- suffices by Proposition 15.1.4
    ext : has-image-ext {ℓ₃ = ℓ₃} f m
    ext B' m' m'emb φ' = proj₁ (proj₁ (hom-to-Π-fib-is-equiv m m')) over-m
      where
        over-f : (a : A) → fib m' (f a)
        over-f = hom-to-Π-fib f m' φ'

        over-mq : (a : A) → fib m' (m (q a))
        over-mq = λ a → tr (fib m') (H a) (over-f a)

        over-m : (y : B) → fib m' (m y)
        over-m = proj₁ (proj₁ (surj-to-dup-surj q qsurj (λ y → fib m' (m y)) (λ y → emb-to-fib-prop m' m'emb (m y))))
          over-mq

-- Corollary 15.2.6: factorisations of f as a surjection followed by an embedding are unique
-- the conclusion is that of image-uniq-i-i'-to-e, so B and B' share a level as there
surj-emb-fact-uniq : {A : Set ℓ} {B B' : Set ℓ₁} {X : Set ℓ₂} → (f : A → X)
  → (q : A → B) → (i : B → X) → (I : triangle-commutes f q i) → is-surj q → is-emb i
  → (q' : A → B') → (i' : B' → X) → (I' : triangle-commutes f q' i') → is-surj q' → is-emb i'
  → is-contr (equiv-over X i i')
surj-emb-fact-uniq f q i I qsurj iemb q' i' I' q'surj i'emb =
  -- the book's identification (e , H) ∘ (q , I) = (q' , I') is automatic, as hom X f i' is a proposition
  image-uniq-i-i'-to-e f i i' iemb i'emb (q , I) (q' , I')
    (surj-to-is-image f q i iemb I qsurj)
    (surj-to-is-image f q' i' i'emb I' q'surj)

-- 15.3 Cantor's diagonal argument

-- Definition 15.3.1
pow-set : (ℓ₁ : Level) → (X : Set ℓ) → Set _
pow-set ℓ₁ X = X → hProp ℓ₁

-- Theorem 15.3.2
no-surj-to-pow-set : (X : Set ℓ) → (f : X → pow-set ℓ₁ X) → ¬ (is-surj f)
no-surj-to-pow-set X f fsurj = rec-prop-trunc 𝟘 empty-prop aim (fsurj P)
  where
    P : pow-set _ X
    P x = ¬ (proj₁ (f x x)) , ¬-prop _

    -- 𝟘 is a proposition, so it suffices to refute an untruncated preimage of P
    aim : fib f P → 𝟘
    aim (x , p) = no-self-iff-neg {P = proj₁ (f x x)} ((λ fx → tr id r fx) , λ nfx → tr id (inv r) nfx)
      where
        -- p at the point x, as a path of underlying types
        r : proj₁ (f x x) ≡ ¬ (proj₁ (f x x))
        r = ap proj₁ (htpy-eq _ _ p x)

-- Exercises
-- 15.1
-- (a): a morphism back from g to f makes g an image of f
hom-g-f-to-is-image : {A : Set ℓ} {B : Set ℓ₁} {X : Set ℓ₂} → (f : A → X) → (h : A → B) → (g : B → X)
  → is-emb g → (H : triangle-commutes f h g) → hom X g f → is-image {ℓ₃ = ℓ₃} f g (h , H)
hom-g-f-to-is-image f h g gemb H k = has-image-ext-to-is-image f g (h , H) λ C m memb χ → hom-comp g f m k χ

-- (b): when f is also an embedding, g is an image of f iff h is an equivalence
-- (i) implies (ii); the universal property is tested against f itself, so it is assumed at level ℓ
emb-f-is-image-to-equiv-h : {A : Set ℓ} {B : Set ℓ₁} {X : Set ℓ₂} → (f : A → X) → (h : A → B) → (g : B → X)
  → is-emb f → is-emb g → (H : triangle-commutes f h g) → is-image {ℓ₃ = ℓ} f g (h , H) → is-equiv h
emb-f-is-image-to-equiv-h {A = A} {X = X} f h g femb gemb H gimage = inverse-to-equiv h (proj₁ k , (hk , kh))
  where
    k : hom X g f
    k = is-image-to-has-image-ext f g (h , H) gimage A f femb (id , λ x → refl)

    hk : h ∘ proj₁ k ∼ id
    hk = hom-emb-endo-htpy-id g gemb (hom-comp g f g k (h , H))

    kh : proj₁ k ∘ h ∼ id
    kh = hom-emb-endo-htpy-id f femb (hom-comp f g f (h , H) k)

-- (ii) implies (i)
emb-f-equiv-h-to-is-image : {A : Set ℓ} {B : Set ℓ₁} {X : Set ℓ₂} → (f : A → X) → (h : A → B) → (g : B → X)
  → is-emb f → is-emb g → (H : triangle-commutes f h g) → is-equiv h → is-image {ℓ₃ = ℓ₃} f g (h , H)
emb-f-equiv-h-to-is-image {X = X} f h g femb gemb H ((s , hs) , _) = hom-g-f-to-is-image f h g gemb H k
  where
    k : hom X g f
    k = s , λ x → concat (ap g (inv (hs x))) (inv (H (s x)))

-- 15.2
-- (a): a proposition embeds into 𝟙, and propositions are exactly the types embedding into 𝟙
is-prop-to-emb-𝟙 : {P : Set ℓ} → is-prop P → is-emb (const {A = P} {B = 𝟙} {b = *})
is-prop-to-emb-𝟙 Pprop = inhab-contr-to-emb-𝟙 (λ p → p , (λ q → proj₁ (Pprop q p)))

Σ-emb-𝟙-≃-hProp : Σ (Set ℓ) (λ A → A ↪ 𝟙) ≃ hProp ℓ
Σ-emb-𝟙-≃-hProp = tot (λ A → proj₁ (e A)) , fam-equiv-to-tot-equiv (λ A → proj₁ (e A)) λ A → proj₂ (e A)
  where
    e : (A : Set ℓ) → A ↪ 𝟙 ≃ is-prop A
    e A = iff-to-≃
      (fam-trunc-to-Σ-trunc (Π-prop _ λ _ → unit-prop) λ f → Π-prop _ λ x → Π-prop _ λ y → equiv-is-prop _)
      (trunc-is-prop A)
      ((λ { (f , femb) → emb-𝟙-to-is-prop (htpy-of-emb-is-emb f const (λ x → proj₂ 𝟙-contractible (f x)) femb) }) ,
       λ Aprop → const , is-prop-to-emb-𝟙 Aprop)

-- (b): for f : A → P into a proposition, f is a propositional truncation iff
-- the constant map P → 𝟙 is an image of the constant map A → 𝟙
-- (i) implies (ii)
prop-trunc-to-const𝟙-is-image : {A P : Set ℓ} → (Pprop : is-prop P) → (f : A → P) → is-prop-trunc Pprop f
  → is-image {ℓ₃ = ℓ} (const {A = A} {B = 𝟙} {b = *}) (const {A = P} {B = 𝟙} {b = *}) (f , λ a → refl)
prop-trunc-to-const𝟙-is-image Pprop f fproptrunc =
  surj-to-is-image const f const (is-prop-to-emb-𝟙 Pprop) (λ x → refl) (prop-trunc-to-surj Pprop f fproptrunc)

-- (ii) implies (i)
const𝟙-is-image-to-prop-trunc : {A P : Set ℓ} → (Pprop : is-prop P) → (f : A → P)
  → is-image {ℓ₃ = ℓ} (const {A = A} {B = 𝟙} {b = *}) (const {A = P} {B = 𝟙} {b = *}) (f , λ a → refl)
  → is-prop-trunc Pprop f
const𝟙-is-image-to-prop-trunc Pprop f constimage =
  surj-to-prop-trunc Pprop f (is-image-to-surj const f const (is-prop-to-emb-𝟙 Pprop) (λ x → refl) constimage)
