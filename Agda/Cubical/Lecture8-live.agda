-- Lecture 8: Cubical Agda

{-# OPTIONS --cubical #-}

module Lecture8-live where

{-

Last time:
- Path types and the cubical interval   (I with endpoints i0, i1. _≡_ is now a PathP)
- Cubical higher inductive types

Today:
- Set quotients
- Cubical transport (`transp`) and path induction
- Homogeneous composition (`hcomp`)

-}

open import cubical-prelude
open import Lecture7-notes

private
  variable
    A B : Type ℓ


-- Set quotients

-- A Type
-- R : A → A → Type   (hProp)
-- Want a quotient type    A / R

data _/_ (A : Type) (R : A → A → Type) : Type where
  [_] : A → A / R
  eq/ : (a b : A) → R a b → [ a ] ≡ [ b ]
  trunc : isSet (A / R)                       -- (a b : A / R) (p q : a ≡ b) → p ≡ q



-- (a , b) ~ (c , d)   iff   a + d ≡ c + b
ℤ' : Type
ℤ' = (ℕ × ℕ) / rel
  where
  rel : ℕ × ℕ → ℕ × ℕ → Type           -- Press C-c C-s and get the type automagically
  rel (a , b) (c , d) = a + d ≡ b + c

-- Exercise: prove ℤ ≃ ℤ'
-- Exercise: define 0, 1, +, -, * and prove standard properties

-- Can also do ℤ / nℤ

-- Similarly we can define ℚ as a quotient pairs of a number with a nonzero number

-- And so on...

-- All of these can be defined without quotients in type theory, but
-- the quotient definition is sometimes more efficient.

-- ℚ can be defined not as a quotient by taking pairs of coprime numbers (i.e. as normalized fractions)

-- Problem: need to normalize constantly

-- With the quotient definition we don't have to normalize unless we want to

-- Practical benefit with quotients: can get more efficient because you don't have to normalize



-- Q: What happens if A is a set and R is prop valued, do you need trunc?

-- A = Unit
-- R is the total

-- Unit / total ≃ S¹   (if we don't have trunc constructor)


-- Q: What happens if A is not a set, but R is not prop valued?

-- It will be a set by def.

-- Nothing too bad... But A / R won't have all the properties you want. For example:

-- effectivity : (a b : A) → [ a ] ≡ [ b ] → R a b

-- (Also need R equivalence relation, and proof of effectivity uses univalence for hProp (prop. ext.))







-- Another example: finite multisets

infixr 5 _∷_

data FMSet (A : Type) : Type where
  [] : FMSet A
  _∷_ : (x : A) → (xs : FMSet A) → FMSet A
  comm : (x y : A) (xs : FMSet A) → x ∷ y ∷ xs ≡ y ∷ x ∷ xs
  trunc : isSet (FMSet A)


-- Didn't use _/_ because it gets a bit longer and annoying
-- Also nice to have a simple path constructor comm to pattern-match on

infixr 30 _++_

_++_ : (xs ys : FMSet A) → FMSet A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)
comm x y xs i ++ ys = comm x y (xs ++ ys) i
trunc xs zs p q i j ++ ys =
  trunc (xs ++ ys) (zs ++ ys) (λ k → p k ++ ys) (λ k → q k ++ ys) i j

-- unitr-++ : (xs : FMSet A) → xs ++ [] ≡ xs
-- unitr-++ [] = refl
-- unitr-++ (x ∷ xs) = ap (x ∷_) (unitr-++ xs)
-- unitr-++ (comm x y xs i) j = comm x y (unitr-++ xs j) i
-- unitr-++ (trunc xs xs₁ x y i i₁) = {!!}  -- Ugh...

-- unitr-++ : (xs : FMSet A) → xs ++ [] ≡ xs
-- unitr-++ = ElimProp.f (trunc _ _) refl (λ x p → ap (x ∷_) p)

-- Can do set quotients this way, but need good lemmas and combinators!


-- In the notes there's a more efficient representation of FMSet, but don't have time to cover it now...


-- Set quotients:
-- Either use _/_      -- get good lemmas, but maybe not the constructors you want
-- Or write your own   -- need to prove good lemmas (but they are boilerplate), but get good constructors to pattern-match on




-- Cubical transport and path induction

-- Last time we saw that we can prove many things for path types using
-- the operations on the interval I (like ~_ , _∧_ , _∨_)

-- But we cannot yet compose paths or transport along paths or prove things by path induction...


-- Basic/primitive operation in Cubical Agda for transport is called `transp`

-- Special case is cubical transport:

transport : A ≡ B → A → B
transport p a = transp (λ i → p i) i0 a

-- In general transp has this (slightly simplified type):

-- transp : (L : I → Type) → (r : I) → L i0 → L i1

-- The r lets us specify where the transp is the identity function
--
-- transp L i1 a ≐ a
--
-- For this to make sense L has to be "constant" whenever r = i1


-- What we cubists call subst, Book HoTT calls transport

subst : (B : A → Type) {x y : A} → x ≡ y → B x → B y
subst B p bx = transport (ap B p) bx


-- Because we are *not* defining things by path-induction transport along refl
-- isn't the identity function

transportRefl : (x : A) → transport refl x ≡ x
transportRefl {A = A} x i = transp (λ _ → A) i x


-- Path-induction is not a primitive concept in Cubical Agda, rather
-- we have to prove it

-- General fact: subst + contractibility of singletons ⇒ path induction

-- Book HoTT version: transport + singleton contractibility ⇒ based path induction ⇒ path induction

-- Path-induction has traditionally been called J in the type theory community

J : {x : A}
    (P : (y : A) → x ≡ y → Type)
    (d : P x refl)
    {y : A}
    (p : x ≡ y)
    →
    P y p
J {A = A} {x = x} P d p = subst (λ X → P (pr₁ X) (pr₂ X)) (lem .pr₂ (_ , p)) d
  where
  lem : isContr (Σ y ꞉ A , x ≡ y)
  lem = isContrSingl x


-- A little bit annoying to use because it doesn't satisfy the computation rule at refl

-- Also can lead to very big terms when Agda unfolds things  (bad for readability and efficiency)

-- Often better to avoid J and stick to cubical primitives directly




-- Homogenous composition (`hcomp`)

-- Special case is path composition

compPath : {x y z : A} → x ≡ y → y ≡ z → x ≡ z
compPath {x = x} p q i = hcomp (λ j → λ { (i = i0) → x
                                        ; (i = i1) → q j })
                               (p i)

{-

         hcomp
    x  - - - - -> z
    ^             ^
    ¦             ¦
  x ¦             ¦ q j
    ¦             ¦
    x ----------> y
          p i


-}


