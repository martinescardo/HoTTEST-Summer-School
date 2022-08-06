```agda
{-# OPTIONS --cubical #-}

module cubical-prelude where

open import Agda.Builtin.Cubical.Path public
open import Agda.Builtin.Cubical.Sub public
  renaming ( inc to inS
           ; primSubOut to outS
           )
open import Agda.Primitive.Cubical public
  renaming ( primIMin       to _∧_  -- I → I → I
           ; primIMax       to _∨_  -- I → I → I
           ; primINeg       to ~_   -- I → I
           ; isOneEmpty     to empty
           ; primComp       to comp
           ; primHComp      to hcomp
           ; primTransp     to transp
           ; itIsOne        to 1=1 )

-- These two are to make sure all the primitives are loaded and ready
-- to compute hcomp/transp for the universe.
import Agda.Builtin.Cubical.Glue
-- HCompU is already imported from Glue, and older Agda versions do
-- not have it. So we comment it out for now.
-- import Agda.Builtin.Cubical.HCompU

open import Agda.Primitive public
  using    ( Level
           ; SSet
           ; lzero
           ; lsuc
           ; _⊔_ )
  renaming ( Set to Type )

-- We parametrize everything by some universe levels
variable
  ℓ ℓ' ℓ'' : Level


-- This file document the Cubical Agda primitives. The primitives
-- themselves are bound by the Agda files imported above.

-- * The Interval
-- I : IUniv

-- Endpoints, Connections, Reversal
-- i0 i1   : I
-- _∧_ _∨_ : I → I → I
-- ~_      : I → I


-- * Dependent path type. (Path over Path)

-- Introduced with lambda abstraction and eliminated with application,
-- just like function types.

-- PathP : ∀ {ℓ} (A : I → Type ℓ) → A i0 → A i1 → Type ℓ

infix 4 _[_≡_]

_[_≡_] : ∀ {ℓ} (A : I → Type ℓ) → A i0 → A i1 → Type ℓ
_[_≡_] = PathP


-- Non dependent path types

Path : ∀ {ℓ} (A : Type ℓ) → A → A → Type ℓ
Path A a b = PathP (λ _ → A) a b

-- PathP (λ i → A) x y gets printed as x ≡ y when A does not mention i.
--  _≡_ : ∀ {ℓ} {A : Type ℓ} → A → A → Type ℓ
--  _≡_ {A = A} = PathP (λ _ → A)


-- * @IsOne r@ represents the constraint "r = i1".
-- Often we will use "φ" for elements of I, when we intend to use them
-- with IsOne (or Partial[P]).
-- IsOne : I → SSet ℓ-zero

-- i1 is indeed equal to i1.
-- 1=1 : IsOne i1


-- * Types of partial elements, and their dependent version.

-- "Partial φ A" is a special version of "IsOne φ → A" with a more
-- extensional judgmental equality.
-- "PartialP φ A" allows "A" to be defined only on "φ".

-- Partial : ∀ {ℓ} → I → Type ℓ → SSet ℓ
-- PartialP : ∀ {ℓ} → (φ : I) → Partial φ (Type ℓ) → SSet ℓ

-- Partial elements are introduced by pattern matching with (r = i0)
-- or (r = i1) constraints, like so:

private
  sys : ∀ i → Partial (i ∨ ~ i) Type₁
  sys i (i = i0) = Type₀
  sys i (i = i1) = Type₀ → Type₀

  -- It also works with pattern matching lambdas:
  --  http://wiki.portal.chalmers.se/agda/pmwiki.php?n=ReferenceManual.PatternMatchingLambdas
  sys' : ∀ i → Partial (i ∨ ~ i) Type₁
  sys' i = λ { (i = i0) → Type₀
             ; (i = i1) → Type₀ → Type₀
             }

  -- When the cases overlap they must agree.
  sys2 : ∀ i j → Partial (i ∨ (i ∧ j)) Type₁
  sys2 i j = λ { (i = i1)          → Type₀
               ; (i = i1) (j = i1) → Type₀
               }

  -- (i0 = i1) is actually absurd.
  sys3 : Partial i0 Type₁
  sys3 = λ { () }


-- * There are cubical subtypes as in CCHM. Note that these are not
-- fibrant (hence in SSet ℓ):

_[_↦_] : ∀ {ℓ} (A : Type ℓ) (φ : I) (u : Partial φ A) → SSet ℓ
A [ φ ↦ u ] = Sub A φ u

infix 4 _[_↦_]

-- Any element u : A can be seen as an element of A [ φ ↦ u ] which
-- agrees with u on φ:

-- inS : ∀ {ℓ} {A : Type ℓ} {φ} (u : A) → A [ φ ↦ (λ _ → u) ]

-- One can also forget that an element agrees with u on φ:

-- outS : ∀ {ℓ} {A : Type ℓ} {φ : I} {u : Partial φ A} → A [ φ ↦ u ] → A


-- * Composition operation according to [CCHM 18].
-- When calling "comp A φ u a" Agda makes sure that "a" agrees with "u i0" on "φ".
-- compCCHM : ∀ {ℓ} (A : (i : I) → Type ℓ) (φ : I) (u : ∀ i → Partial φ (A i)) (a : A i0) → A i1

-- Note: this is not recommended to use, instead use the CHM
-- primitives! The reason is that these work with HITs and produce
-- fewer empty systems.


-- * Generalized transport and homogeneous composition [CHM 18].

-- When calling "transp A φ a" Agda makes sure that "A" is constant on "φ" (see below).
-- transp : ∀ {ℓ} (A : I → Type ℓ) (φ : I) (a : A i0) → A i1

-- "A" being constant on "φ" means that "A" should be a constant function whenever the
-- constraint "φ = i1" is satisfied. For example:
-- - If "φ" is "i0" then "A" can be anything, since this condition is vacuously true.
-- - If "φ" is "i1" then "A" must be a constant function.
-- - If "φ" is some in-scope variable "i" then "A" only needs to be a constant function
--   when substituting "i1" for "i".

-- When calling "hcomp A φ u a" Agda makes sure that "a" agrees with "u i0" on "φ".
-- hcomp : ∀ {ℓ} {A : Type ℓ} {φ : I} (u : I → Partial φ A) (a : A) → A

-- Homogeneous filling
hfill : {A : Type ℓ}
        {φ : I}
        (u : ∀ i → Partial φ A)
        (u0 : A [ φ ↦ u i0 ])
        -----------------------
        (i : I) → A
hfill {φ = φ} u u0 i =
  hcomp (λ j → λ { (φ = i1) → u (i ∧ j) 1=1
                 ; (i = i0) → outS u0 })
        (outS u0)

-- Heterogeneous composition can defined as in CHM, however we use the
-- builtin one as it doesn't require u0 to be a cubical subtype. This
-- reduces the number of inS's a lot.
-- comp : (A : ∀ i → Type (ℓ' i))
--        {φ : I}
--        (u : ∀ i → Partial φ (A i))
--        (u0 : A i0 [ φ ↦ u i0 ])
--      → ---------------------------
--        A i1
-- comp A {φ = φ} u u0 =
--   hcomp (λ i → λ { (φ = i1) → transp (λ j → A (i ∨ j)) i (u _ 1=1) })
--         (transp A i0 (outS u0))

-- Heterogeneous filling defined using comp
fill : {ℓ' : I → Level}
       (A : ∀ i → Type (ℓ' i))
       {φ : I}
       (u : ∀ i → Partial φ (A i))
       (u0 : A i0 [ φ ↦ u i0 ])
       ---------------------------
       (i : I) → A i
fill A {φ = φ} u u0 i =
  comp (λ j → A (i ∧ j))
       (λ j → λ { (φ = i1) → u (i ∧ j) 1=1
                ; (i = i0) → outS u0 })
       (outS u0)

-- TODO: move?
_∙_ : {A : Type ℓ} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
_∙_ {x = x} p q i = hcomp (λ j → λ { (i = i0) → x
                                   ; (i = i1) → q j })
                          (p i)


-- Σ-types
record Σ {l1 l2 : Level} {A : Type l1} (B : A → Type l2) : Type (l1 ⊔ l2)  where
 constructor
  _,_
 field
  pr₁ : A
  pr₂ : B pr₁

open Σ public
infixr 0 _,_

Sigma : {l1 l2 : Level} (A : Type l1) (B : A → Type l2) → Type (l1 ⊔ l2)
Sigma {l1} {l2} A B = Σ {l1} {l2} {A} B

syntax Sigma A (λ x → b) = Σ x ꞉ A , b

infix -1 Sigma

_×_ : ∀ {l1 l2} → Type l1 → Type l2 → Type (l1 ⊔ l2)
A × B = Sigma A (\ _ → B)

infixr 2 _×_
```
