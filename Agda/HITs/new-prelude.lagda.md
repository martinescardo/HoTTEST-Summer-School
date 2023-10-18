This file contains selected definitions from the Lecture 1, 2, 3 code
(see ../Lecture-Notes) that we will use in Lectures 4, 5, 6.  Some
definitions have been made "universe polymorphic" (see Lecture 3) so
that we can use them for more than one universe, because we will need
this soon.


```agda

{-# OPTIONS --without-K #-}

module new-prelude where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_) renaming (Set to Type) public

data _≡_ {l : Level} {A : Type l} : A → A → Type l where
 refl : (x : A) → x ≡ x

Path : {l : Level} (A : Type l) → A → A → Type l
Path A x y = x ≡ y

syntax Path A x y = x ≡ y [ A ] 

infix 0 _≡_

_∙_ : {l : Level} {A : Type l} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
p ∙ (refl y) = p

infixl 7 _∙_

-- path inverses/symmetry was called (-)⁻¹ in previous lectures, but I prefer a prefix
-- rather than post-fix notation
! : {l : Level} {A : Type l} {x y : A} → x ≡ y → y ≡ x
! (refl x) = refl x

ap : {l1 l2 : Level} {A : Type l1} {B : Type l2} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
ap f (refl x) = refl (f x)

ap₂ : {l1 l2 l3 : Level} {A : Type l1} {B : Type l2} {C : Type l3} (f : A → B → C) {x x' : A} {y y' : B}
    → x ≡ x' → y ≡ y' → f x y ≡ f x' y'
ap₂ f (refl x) (refl y) = refl (f x y)

transport : {l1 l2 : Level} {X : Type l1} (A : X → Type l2)
          → {x y : X} → x ≡ y → A x → A y
transport A (refl x) a = a


_∼_ : {l1 l2 : Level} {A : Type l1} {B : A → Type l2} → ((x : A) → B x) → ((x : A) → B x) → Type (l1 ⊔ l2)
f ∼ g = ∀ x → f x ≡ g x

infix 0 _∼_

_≡⟨_⟩_ : {l : Level} {X : Type l} (x : X) {y z : X} → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ p ⟩ q = p ∙ q

_∎ : {l : Level} {X : Type l} (x : X) → x ≡ x
x ∎ = refl x

infixr  0 _≡⟨_⟩_
infix   1 _∎

record Σ {l1 l2 : Level} {A : Type l1 } (B : A → Type l2) : Type (l1 ⊔ l2)  where
 constructor
  _,_
 field
  pr₁ : A
  pr₂ : B pr₁

open Σ public
infixr 0 _,_

Sigma : {l1 l2 : Level} (A : Type l1) (B : A → Type l2) → Type (l1 ⊔ l2)
Sigma A B = Σ B

syntax Sigma A (λ x → b) = Σ x ꞉ A , b

infix -1 Sigma

id : {l : Level} {A : Type l} → A → A
id x = x

_∘_ : {l1 l2 l3 : Level} {A : Type l1} {B : Type l2} {C : B → Type l3}
    → ((y : B) → C y)
    → (f : A → B)
    → (x : A) → C (f x)
g ∘ f = λ x → g (f x)

_×_ : ∀ {l1 l2} → Type l1 → Type l2 → Type (l1 ⊔ l2)
A × B = Sigma A (\ _ → B)

infixr 2 _×_

-- sums-equality.to-×-≡ in ../Lecture-Notes/sums-equality
pair≡ : {l1 l2 : Level} {A : Type l1} {B : Type l2} {x x' : A} {y y' : B}
      → x ≡ x'
      → y ≡ y'
      → _≡_{_}{A × B} (x , y) (x' , y')
pair≡ (refl _) (refl _) = refl _

postulate
  λ≡ : {l1 l2 : Level} {A : Type l1} {B : A → Type l2} {f g : (x : A) → B x} → f ∼ g → f ≡ g

record is-bijection {l1 l2 : Level} {A : Type l1} {B : Type l2} (f : A → B) : Type (l1 ⊔ l2) where
 constructor
  Inverse
 field
  inverse : B → A
  η       : inverse ∘ f ∼ id
  ε       : f ∘ inverse ∼ id

record _≅_ {l1 l2 : Level} (A : Type l1) (B : Type l2) : Type (l1 ⊔ l2) where
 constructor
  Isomorphism
 field
  bijection   : A → B
  bijectivity : is-bijection bijection

infix 0 _≅_

is-prop : {l : Level} → Type l → Type l
is-prop X = (x y : X) → x ≡ y

is-set : {l : Level} → Type l → Type l
is-set X = (x y : X) → is-prop (x ≡ y)

data BoolL {l : Level} : Type l where
 true false : BoolL

Bool : Type
Bool = BoolL {lzero}

if_then_else_ : {l : Level} {A : Type l} → Bool → A → A → A
if true  then x else y = x
if false then x else y = y

record Unit {l : Level} : Type l where
 constructor
  ⋆

𝟙 : Type
𝟙 = Unit {lzero}

data ℕ : Type where
 zero : ℕ
 suc  : ℕ → ℕ

the : ∀ {l} (A : Type l) → A → A
the _ x = x
```
