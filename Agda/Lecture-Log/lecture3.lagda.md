```agda
{-# OPTIONS --without-K --safe #-}

module lecture3 where

-- lecture 3
-- Plan: Complete last lecture.
--       Generalize some definitions to use universe levels.
--       Uses of Sigma, including examples like monoids.
--       Use of universes to prove that ¬ (false ≡ true).
--       Characterization of equality in Σ types.


open import lecture1 hiding (𝟘 ; 𝟙 ; ⋆ ; D ; _≣_)
open import lecture2 using (is-prime ; _*_ ; 𝟘 ; 𝟙 ; ⋆ ; _≥_)

-- Give Σ a universe-polymorphic type

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
                           renaming (Set to 𝓤)
                           public

variable i j k : Level

record Σ {A : 𝓤 i} (B : A → 𝓤 j) : 𝓤 (i ⊔ j) where
 constructor
  _,_
 field
  pr₁ : A
  pr₂ : B pr₁

open Σ public
infixr 1 _,_

Sigma : (A : 𝓤 i) (B : A → 𝓤 j) → 𝓤 (i ⊔ j)
Sigma {i} {j} A B = Σ {i} {j} {A} B

syntax Sigma A (λ x → b) = Σ x ꞉ A , b

infix -1 Sigma

_×_ : 𝓤 i → 𝓤 j → 𝓤 (i ⊔ j)
A × B = Σ x ꞉ A , B

-- (x : X) → A x
-- (x : X) × A x

infixr 2 _×_

-- More general type of negation:

¬_ : 𝓤 i → 𝓤 i
¬ A = A → 𝟘

-- Give the identity type more general universe assignments:

data _≡_ {X : 𝓤 i} : X → X → 𝓤 i where
 refl : (x : X) → x ≡ x

_≢_ : {X : 𝓤 i} → X → X → 𝓤 i
x ≢ y = ¬ (x ≡ y)

infix 0 _≡_

≡-elim : {X : 𝓤 i} (A : (x y : X) → x ≡ y → 𝓤 j)
       → ((x : X) → A x x (refl x))
       → (x y : X) (p : x ≡ y) → A x y p
≡-elim A f x x (refl x) = f x

≡-nondep-elim : {X : 𝓤 i} (A : X → X → 𝓤 j)
              → ((x : X) → A x x)
              → (x y : X) → x ≡ y → A x y
≡-nondep-elim A = ≡-elim (λ x y _ → A x y)

trans : {A : 𝓤 i} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans p (refl y) = p

sym : {A : 𝓤 i} {x y : A} → x ≡ y → y ≡ x
sym (refl x) = refl x

ap : {A : 𝓤 i} {B : 𝓤 j} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
ap f (refl x) = refl (f x)

ap₂ : {A : 𝓤 i} {B : 𝓤 j} {C : 𝓤 k} (f : A → B → C) {x x' : A} {y y' : B}
    → x ≡ x' → y ≡ y' → f x y ≡ f x' y'
ap₂ f (refl x) (refl y) = refl (f x y)

transport : {X : 𝓤 i} (A : X → 𝓤 j)
          → {x y : X} → x ≡ y → A x → A y
transport A (refl x) a = a

_∙_ : {A : 𝓤 i} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
_∙_ = trans

infixl 7 _∙_

_⁻¹ : {A : 𝓤 i} {x y : A} → x ≡ y → y ≡ x
_⁻¹ = sym

infix  40 _⁻¹

-- The (sub)type of prime numbers

ℙ : 𝓤₀
ℙ = Σ p ꞉ ℕ , is-prime p

ℙ-inclusion : ℙ → ℕ
ℙ-inclusion = pr₁

-- We can prove that this map is left-cancellable, i.e. it satisfies
-- ℙ-inclusion u ≡ ℙ-inclusion u → u ≡ v.
-- Moreover, this map is an embedding (we haven't defined this concept yet).

-- Not quite the type of composite numbers:

CN : 𝓤
CN = Σ x ꞉ ℕ , Σ (y , z) ꞉ ℕ × ℕ , x ≡ y * z

CN' : 𝓤
CN' = Σ x ꞉ ℕ , Σ (y , z) ꞉ ℕ × ℕ , (y ≥ 2) × (z ≥ 2) × (x ≡ y * z)

CN-projection : CN → ℕ
CN-projection = pr₁

-- This map is not left-cancellable, and hence can't be considered to
-- be an an inclusion.

counter-example : CN-projection (6 , (3 , 2) , refl 6)
                ≡ CN-projection (6 , (2 , 3) , refl 6)
counter-example = refl 6

-- But how do we prove that these two tuples are *different*? They
-- certainly do look different. We'll do this later.

-- We will need to define
--
-- CN = Σ x ꞉ ℕ , ∥ Σ (y , z) ꞉ ℕ × ℕ , x ≡ y * z ∥, or equivalently
-- CN = Σ x ꞉ ℕ , ∃ (y , z) ꞉ ℕ × ℕ , x ≡ y * z ∥
--
-- to really get a *subtype* of composite numbers.


-- Another use of Σ.
-- The type of monoids.

is-prop : 𝓤 i → 𝓤 i
is-prop X = (x y : X) → x ≡ y

is-set : 𝓤 i → 𝓤 i
is-set X = (x y : X) → is-prop (x ≡ y)

Mon : 𝓤 (lsuc i)
Mon {i} = Σ X ꞉ 𝓤 i  -- data
            , is-set X  -- property (we show that)
            × (Σ 𝟏 ꞉ X ,  -- data (but...)
               Σ _·_ ꞉ (X → X → X) -- data
                  , (((x : X) → (x · 𝟏 ≡ x)) -- (1) property
                  ×  ((x : X) → (𝟏 · x ≡ x)) -- (2) property
                  ×  ((x y z : X) → (x · (y · z)) ≡ ((x · y) · z)))) -- (3) property

-- This can be defined using a record in Agda:

record Mon' : 𝓤 (lsuc i) where
 constructor mon
 field
  carrier        : 𝓤 i  -- X
  carrier-is-set : is-set carrier
  𝟏              : carrier
  _·_            : carrier → carrier → carrier
  left-unit-law  : (x : carrier) → x · 𝟏 ≡ x
  right-unit-law : (x : carrier) → 𝟏 · x ≡ x
  assoc-law      : (x y z : carrier) → (x · (y · z)) ≡ ((x · y) · z)

α : Mon {i} → Mon' {i}
α (X , X-is-set , 𝟏 , _·_ , l , r , a) = mon X X-is-set 𝟏 _·_ l r a

β : Mon' {i} → Mon {i}
β (mon X X-is-set 𝟏 _·_ l r a) = (X , X-is-set , 𝟏 , _·_ , l , r , a)

βα : (M : Mon {i}) → β (α M) ≡ M
βα = refl

αβ : (M : Mon' {i}) → α (β M) ≡ M
αβ = refl

-- This kind of proof doesn't belong to the realm of MLTT:

false-is-not-true[not-an-MLTT-proof] : false ≢ true
false-is-not-true[not-an-MLTT-proof] ()

-- Proof in MLTT, which requires a universe (Cf. Ulrik's 2nd HoTT
-- lecture):

_≣_ : Bool → Bool → 𝓤₀
true  ≣ true  = 𝟙
true  ≣ false = 𝟘
false ≣ true  = 𝟘
false ≣ false = 𝟙

≡-gives-≣ : {x y : Bool} → x ≡ y → x ≣ y
≡-gives-≣ (refl true)  = ⋆
≡-gives-≣ (refl false) = ⋆

false-is-not-true : ¬ (false ≡ true)
false-is-not-true p = II
 where
  I : false ≣ true
  I = ≡-gives-≣ p

  II : 𝟘
  II = I

false-is-not-true' : ¬ (false ≡ true)
false-is-not-true' = ≡-gives-≣

-- Notice that this proof is different from the one given by Ulrik in
-- the HoTT track. Exercise: implement Ulrik's proof in Agda.

-- Exercise: prove that ¬ (0 ≡ 1) in the natural numbers in MLTT style
-- without using `()`.

-- contrapositives.

contrapositive : {A : 𝓤 i} {B : 𝓤 j} → (A → B) → (¬ B → ¬ A)
contrapositive f g a = g (f a)

Π-¬-gives-¬-Σ : {X : 𝓤 i} {A : X → 𝓤 j}
              → ((x : X) → ¬ A x)
              → ¬ (Σ x ꞉ X , A x)
Π-¬-gives-¬-Σ ϕ (x , a) = ϕ x a

¬-Σ-gives-Π-¬ : {X : 𝓤 i} {A : X → 𝓤 j}
              → ¬ (Σ x ꞉ X , A x)
              → ((x : X) → ¬ A x)
¬-Σ-gives-Π-¬ γ x a = γ (x , a)


-- Equality in Σ types.

from-Σ-≡' : {X : 𝓤 i} {A : X → 𝓤 j}
            {(x , a) (y , b) : Σ A}
          → (x , a) ≡ (y , b)
          → Σ p ꞉ (x ≡ y) , (transport A p a ≡ b)
from-Σ-≡' (refl (x , a)) = (refl x , refl a)

to-Σ-≡' : {X : 𝓤 i} {A : X → 𝓤 j}
          {(x , a) (y , b) : Σ A}
        → (Σ p ꞉ (x ≡ y) , (transport A p a ≡ b))
        → (x , a) ≡ (y , b)
to-Σ-≡' (refl x , refl a) = refl (x , a)

module _ {X : 𝓤 i} {A : 𝓤 j}
         {(x , a) (y , b) : X × A} where

 from-×-≡ : (x , a) ≡ (y , b)
          → (x ≡ y) × (a ≡ b)
 from-×-≡ (refl (x , a)) = refl x , refl a


 to-×-≡ : (x ≡ y) × (a ≡ b)
        → (x , a) ≡ (y , b)
 to-×-≡ (refl x , refl a) = refl (x , a)

module _ {X : 𝓤 i} {A : X → 𝓤 j}
         {(x , a) (y , b) : Σ A} where

 -- x y : X
 -- a : A x
 -- b : A y

 from-Σ-≡ : (x , a) ≡ (y , b)
          → Σ p ꞉ (x ≡ y) , transport A p a ≡ b
 from-Σ-≡ (refl (x , a)) = refl x , refl a


 to-Σ-≡ : (Σ p ꞉ (x ≡ y) , (transport A p a ≡ b))
        → (x , a) ≡ (y , b)
 to-Σ-≡ (refl x , refl a) = refl (x , a)


 contra-from-Σ-≡ : ¬ (Σ p ꞉ (x ≡ y) , (transport A p a ≡ b))
                 → (x , a) ≢ (y , b)
 contra-from-Σ-≡ = contrapositive from-Σ-≡

 contra-to-Σ-≡ : (x , a) ≢ (y , b)
               → ¬ (Σ p ꞉ (x ≡ y) , (transport A p a ≡ b))
 contra-to-Σ-≡ = contrapositive to-Σ-≡

 to-Σ-≢ : ((p : x ≡ y) → transport A p a ≢ b)
        → (x , a) ≢ (y , b)
 to-Σ-≢ u = contra-from-Σ-≡ (Π-¬-gives-¬-Σ u)

 from-Σ-≢ : (x , a) ≢ (y , b)
          → ((p : x ≡ y) → transport A p a ≢ b)
 from-Σ-≢ v = ¬-Σ-gives-Π-¬ (contra-to-Σ-≡ v)
```

We now revisit the example above. How do we prove that aa and bb are
different? It's not easy. We use the above lemmas.

```agda
aa bb : CN
aa = (6 , (3 , 2) , refl 6)
bb = (6 , (2 , 3) , refl 6)
```

To prove that aa ≢ bb, we need to know that ℕ is a set! And this is
difficult. See the module
[Hedbergs-Theorem](../Lecture-Notes/Hedbergs-Theorem.lagda.md) for a
complete proof.

For the moment we just assume that ℕ is a set, and prove that 3 ≢ 2 by
cheating (produce a genuine MLTT proof as an exercise).

```agda

3-is-not-2 : 3 ≢ 2
3-is-not-2 ()

example-revisited : is-set ℕ → aa ≢ bb
example-revisited ℕ-is-set = I
 where
  A : ℕ → 𝓤₀
  A x = Σ (y , z) ꞉ ℕ × ℕ , x ≡ y * z

  II : (p : 6 ≡ 6) → transport A p ((3 , 2) , refl 6) ≢  ((2 , 3) , refl 6)
  II p = VIII
   where
    III : p ≡ refl 6
    III = ℕ-is-set 6 6 p (refl 6)

    IV : transport A p ((3 , 2) , refl 6) ≡ ((3 , 2) , refl 6)
    IV = ap (λ - → transport A - ((3 , 2) , refl 6)) III

    V : ((3 , 2) , refl 6) ≢ ((2 , 3) , refl 6)
    V q = 3-is-not-2 VII
     where
      VI : (3 , 2) ≡ (2 , 3)
      VI = ap pr₁ q

      VII : 3 ≡ 2
      VII = ap pr₁ VI

    VIII : transport A p ((3 , 2) , refl 6) ≢  ((2 , 3) , refl 6)
    VIII r = V IX
     where
      IX : ((3 , 2) , refl 6) ≡ ((2 , 3) , refl 6)
      IX = trans (IV ⁻¹) r

  I : aa ≢ bb
  I = to-Σ-≢ II
```

If there is time, I will do some isomorphisms.
