```agda
{-# OPTIONS --without-K --safe #-}

module lecture2 where

-- lecture 2
-- Plan: basic MLTT types, including their elimination principles.
--

open import lecture1 hiding (𝟘 ; 𝟙 ; D)

-- empty type
data 𝟘 : Type where

-- Π x ꞉ X , A x
-- (X → B) =. Π x ꞉ X , B

𝟘-elim : {A : 𝟘 → Type} (x : 𝟘) → A x
𝟘-elim ()

-- 𝟘 interpreted as "false"

¬_ : Type → Type
¬ A = A → 𝟘

infix 1000 ¬_

𝟘-nondep-elim : {B : Type} → 𝟘 → B
𝟘-nondep-elim {B} = 𝟘-elim {λ _ → B}

-- A := λ _ → B


is-empty : Type → Type
is-empty A = A → 𝟘

-- A ≡ 𝟘 or A ≃ 𝟘.

𝟘-is-empty'' : is-empty 𝟘
𝟘-is-empty'' = λ ()

𝟘-is-empty : is-empty 𝟘
𝟘-is-empty = 𝟘-nondep-elim

𝟘-is-empty' : is-empty 𝟘
𝟘-is-empty' = id

-- Unit type:

-- Record definitions satisfy a certain "η" rule.

record 𝟙 : Type where
 constructor
  ⋆

open 𝟙 public

𝟙-is-nonempty' : ¬ is-empty 𝟙
𝟙-is-nonempty' = λ (f : 𝟙 → 𝟘) → f ⋆

𝟙-is-nonempty : ¬ is-empty 𝟙
𝟙-is-nonempty f = f ⋆

𝟙-elim : {A : 𝟙 → Type}
       → A ⋆
       → (x : 𝟙) → A x
𝟙-elim a x = a

𝟙-nondep-elim : {A : Type}
              → A
              → 𝟙 → A
𝟙-nondep-elim {A} = 𝟙-elim {λ _ → A}

-- Type of binary digits:

data 𝟚 : Type where
 𝟎 𝟏 : 𝟚

𝟚-elim : {A : 𝟚 → Type}
       → A 𝟎
       → A 𝟏
       → (x : 𝟚) → A x
𝟚-elim a₀ a₁ 𝟎 = a₀
𝟚-elim a₀ a₁ 𝟏 = a₁

𝟚-nondep-elim : {A : Type}
              → A
              → A
              → 𝟚 → A
𝟚-nondep-elim {A} = 𝟚-elim {λ _ → A}

-- Π types in Agda are primitive.
--
-- We have that Π x ꞉ X , A x is written
--
--              (x : X) → A x,   or
--              ∀ (x : X) → A x, or
--              ∀ x → A x        (if Agda can infer X).
--
-- We can introduce Π-syntax if we wish:

Pi : (A : Type) (B : A → Type) → Type
Pi A B = (x : A) → B x

syntax Pi A (λ x → b) = Π x ꞉ A , b
--                          ↑
--                         this is typed "\:4" in emacs mode and is not the same as ":".
--                         (we can't use the normal one unfortunately.)


-- Function composition.

-- The usual one found in mathematics:

module _ where
 private
  _∘_ : {A B C : Type} → (B → C) → (A → B) → (A → C)
  (g ∘ f) x = g (f x)

-- A more general version:

_∘_ : {A B : Type} {C : B → Type}
    → ((y : B) → C y)
    → (f : A → B)
    → (x : A) → C (f x)
(g ∘ f) x = g (f x)

-- The types-as-mathematical-statements reading of dependent function composition is:
--
-- If (for all y : B we have that C y) and f : A → B is any function, then
-- for all x : A we have that C (f x).
--
-- The proof is function composition.


-- Σ-types:

module _ where
 private

  data Σ {A : Type } (B : A → Type) : Type  where
   _,_ : (x : A) (y : B x) → Σ {A} B

  pr₁ : {A : Type} {B : A → Type} → Σ B → A
  pr₁ (x , y) = x

  pr₂ : {A : Type} {B : A → Type} → (z : Σ B) → B (pr₁ z)
  pr₂ (x , y) = y

-- Our preferred definition:

record Σ {A : Type } (B : A → Type) : Type  where
 constructor
  _,_
 field
  pr₁ : A
  pr₂ : B pr₁

open Σ public
infixr 0 _,_

pr₁-again : {A : Type} {B : A → Type} → Σ B → A
pr₁-again = pr₁

pr₂-again : {A : Type} {B : A → Type} ((x , y) : Σ B) → B x
pr₂-again = pr₂


-- This satisfies the η-rule z = (pr₁ z , pr₂ z), which the definition using `data` doesn't.


Sigma : (A : Type) (B : A → Type) → Type
Sigma A B = Σ {A} B

syntax Sigma A (λ x → b) = Σ x ꞉ A , b

infix -1 Sigma

-- Recall that we defined D as follows in the first lecture:

D : Bool → Type
D true  = ℕ
D false = Bool

-- Example

Σ-example₁ Σ-example₂ : Σ b ꞉ Bool , D b
Σ-example₁ = (true  , 17)
Σ-example₂ = (false , true)

-- Σ-elim is "curry":

Σ-elim : {A : Type } {B : A → Type} {C : (Σ x ꞉ A , B x) → Type}
       → ((x : A) (y : B x) → C (x , y))
       → (z : Σ x ꞉ A , B x) → C z
Σ-elim f (x , y) = f x y

Σ-uncurry : {A : Type } {B : A → Type} {C : (Σ x ꞉ A , B x) → Type}
          → ((z : Σ x ꞉ A , B x) → C z)
          → (x : A) (y : B x) → C (x , y)
Σ-uncurry g x y = g (x , y)

_×_ : Type → Type → Type
A × B = Σ x ꞉ A , B

-- (x : X) → A x
-- (x : X) × A x

infixr 2 _×_

-- We will have that A₀ × A₁ ≅ Π (n : 𝟚) , A n ≅ ((n : 𝟚) → A n)
-- where A 𝟎 = A₀
--       A 𝟏 = A₁
--       A : 𝟚 → Type
-- f ↦ (f 𝟎 , f 𝟏)
-- (a₀ , a₁) ↦ 𝟚-elim a₀ a₁
-- But we need function extensionality to prove that this works.
-- Binary products are special cases of products.

```

Various uses of Σ:

  *
  *
  *

```agda

-- Binary sums _+_ ∔

data _∔_ (A B : Type) : Type where
 inl : A → A ∔ B
 inr : B → A ∔ B

-- Mathematically A ∔ B is (disjoint) union.
-- Logically, it is "or" (disjunction).
-- ∥ A ∔ B ∥.

infixr 20 _∔_

∔-elim : {A B : Type} (C : A ∔ B → Type)
       → ((x : A) → C (inl x)) -- f
       → ((y : B) → C (inr y)) -- g
       → (z : A ∔ B) → C z
∔-elim C f g (inl x) = f x
∔-elim C f g (inr y) = g y

∔-nondep-elim : {A B C : Type}
              → (A → C)
              → (B → C)
              → (A ∔ B → C)
∔-nondep-elim {A} {B} {C} = ∔-elim (λ z → C)

-- We will have that A₀ ∔ A₁ ≅ Σ (n : 𝟚) , A n
-- where A 𝟎 = A₀
--       A 𝟏 = A₁
-- inl a₀ ↦ (𝟎 , a₀)
-- inr a₁ ↦ (𝟏 , a₁)
-- Binary sums are special cases of sums.


-- We call an element of the identity type x ≡ y an
-- "identification". The terminology "path" is also used.
-- I prefer the former.

data _≡_ {A : Type} : A → A → Type where
 refl : (x : A) → x ≡ x

-- refl x : proof that x is equal to itself.

infix 0 _≡_

-- The following is also called "J":

≡-elim : {X : Type} (A : (x y : X) → x ≡ y → Type)
       → ((x : X) → A x x (refl x))
       → (x y : X) (p : x ≡ y) → A x y p
≡-elim A f x x (refl x) = f x

-- To conclude that a property A x y p of identifications p of
-- elements x and y holds for all x, y and p, it is enough to show
-- that A x x (refl x) holds for all x.

≡-nondep-elim : {X : Type} (A : X → X → Type)
              → ((x : X) → A x x)
              → (x y : X) → x ≡ y → A x y
≡-nondep-elim A = ≡-elim (λ x y _ → A x y)

trans : {A : Type} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans p (refl y) = p

sym : {A : Type} {x y : A} → x ≡ y → y ≡ x
sym (refl x) = refl x

ap : {A B : Type} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
ap f (refl x) = refl (f x)

ap₂ : {A B C : Type} (f : A → B → C) {x x' : A} {y y' : B}
    → x ≡ x' → y ≡ y' → f x y ≡ f x' y'
ap₂ f (refl x) (refl y) = refl (f x y)

transport : {X : Type} (A : X → Type)
          → {x y : X} → x ≡ y → A x → A y
transport A (refl x) a = a

_∙_ : {A : Type} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
_∙_ = trans

infixl 7 _∙_

_⁻¹ : {A : Type} {x y : A} → x ≡ y → y ≡ x
_⁻¹ = sym

infix  40 _⁻¹

_≤_ : ℕ → ℕ → Type
0     ≤ y     = 𝟙
suc x ≤ 0     = 𝟘
suc x ≤ suc y = x ≤ y

_≥_ : ℕ → ℕ → Type
x ≥ y = y ≤ x

_*_ : ℕ → ℕ → ℕ
0     * y = 0
suc x * y = x * y + y

infixr 30 _*_

is-prime : ℕ → Type
is-prime p = (p ≥ 2) × ((x y : ℕ) → x * y ≡ p → (x ≡ 1) ∔ (x ≡ p))


twin-prime-conjecture : Type
twin-prime-conjecture = (n : ℕ) → Σ p ꞉ ℕ , (p ≥ n)
                                          × is-prime p
                                          × is-prime (p + 2)

there-are-infinitely-many-primes : Type
there-are-infinitely-many-primes = (n : ℕ) → Σ p ꞉ ℕ , (p ≥ n) × is-prime p
```

(x , p) ≡ (y , refl)

p : x ≡ y
