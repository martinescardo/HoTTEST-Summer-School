-- Lecture 7: Cubical Agda

{-# OPTIONS --cubical #-}

module Lecture7-live where

-- Today:
-- - Path types and the cubical interval
-- - Cubical higher inductive types

open import cubical-prelude

-- Libraries:
-- - agda/cubical library
-- - 1lab

-- The interval in Cubical Agda is written I
-- Endpoints are called i0 and i1

apply0 : (A : Type) → (p : I → A) → A
apply0 A p = p i0

-- Path types:
-- p : x ≡ y consists of  p : I → A   s.t. p i0 == x  and  p i1 == y

refl : {A : Type} {x : A} → x ≡ x
refl {x = x} = λ i → x

-- Cannot pattern-match on r:
-- oops : {A : Type} → I → A
-- oops r = {!r!}

variable
  A B : Type ℓ   -- ℓ is \ell

-- ap is called cong in the agda/cubical library
ap : (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
ap f p i = f (p i)

-- Satisfies definitional/judgmental/strict computation rules (see exercises)

-- Funext can be seen as turning
-- A → (I → B)
-- into
-- I → (A → B)

funExt : {f g : A → B} → (p : (x : A) → f x ≡ g x) → f ≡ g
funExt p = λ i → λ x → p x i
-- To convince oneself that this makes sense: plug in i0 and i1 for i

-- In Cubical Agda we also have three operations on I

-- Minimum:     _∧_ : I → I → I
-- Maximum:     _∨_ : I → I → I
-- Symmetry:     ~_ : I → I

-- ! or ⁻¹
sym : {x y : A} → x ≡ y → y ≡ x
sym p i = p (~ i)

-- For examples of _∧_ and _∨_ see the notes for now

-- Path overs in Book HoTT are called PathP in Cubical Agda
-- In fact,  x ≡ y  is short for  PathP (λ i → A) x y

reflP : {x : A} → PathP (λ i → A) x x
reflP {x = x} = λ i → x



-- Cubical higher inductive types

-- HITs: S1, Circle2, Torus, ...

-- Dan introduced these using postulates

-- In Cubical Agda you can just write them as data types,
-- in particular you don't have postulate the recursor/eliminator
-- and can instead use pattern matching

data S¹ : Type where
  base : S¹
  loop : base ≡ base   -- I → S¹  with  endpoints base and base

double : S¹ → S¹
double base = base
double (loop i) = (loop ∙ loop) i

helix : S¹ → Type
helix base = ℤ
helix (loop i) = sucPath i

winding : base ≡ base → ℤ
winding p = transp (λ i → helix (p i)) i0 (pos 0)

_ : winding (loop ∙ loop) ≡ pos 2
_ = refl

-- Following Dan's lecture one can prove that winding is an equivalence
-- using the encode-decode, see Cubical.HITs.S1.Base


-- Torus

  --            line1
  --       p ----------> p
  --       ^             ^
  --       ¦             ¦
  -- line2 ¦   square    ¦ line2
  --       ¦             ¦
  --       p ----------> p
  --            line1

data Torus : Type where
  point : Torus
  line1 : point ≡ point
  line2 : point ≡ point
  square : PathP (λ i → line1 i ≡ line1 i) line2 line2

-- Exercise: define the Klein bottle

t2c : Torus → S¹ × S¹
t2c point = base , base
t2c (line1 i) = (loop i) , base
t2c (line2 i) = base , (loop i)
t2c (square i j) = (loop i) , (loop j)

c2t : S¹ × S¹ → Torus
c2t (base , base) = point
c2t (base , loop i) = line2 i
c2t (loop i , base) = line1 i
c2t (loop i , loop j) = square i j

c2t-t2c : (t : Torus) → c2t (t2c t) ≡ t
c2t-t2c point = refl
c2t-t2c (line1 i) = refl
c2t-t2c (line2 i) = refl
c2t-t2c (square i j) = refl

t2c-c2t : (t : S¹ × S¹) → t2c (c2t t) ≡ t
t2c-c2t (base , base) = refl
t2c-c2t (base , loop i) = refl
t2c-c2t (loop i , base) = refl
t2c-c2t (loop i , loop j) = refl

Torus≡S¹×S¹ : Torus ≡ S¹ × S¹
Torus≡S¹×S¹ = isoToPath (iso t2c c2t t2c-c2t c2t-t2c)


-- Alternative definition:
data Torus' : Type where
  point : Torus'
  line1 : point ≡ point
  line2 : point ≡ point
  square : line1 ∙ line2 ≡ line2 ∙ line1

-- (Probably very hard) Exercise: prove that Torus ≃ Torus'


-- More HITs:

-- Suspension

data Susp (A : Type) : Type where
  north : Susp A
  south : Susp A
  merid : (a : A) → north ≡ south

flip : Susp S¹ → Susp S¹
flip north = south
flip south = north
flip (merid a i) = merid a (~ i)

-- Pushout

--      f
--  A  --->   B
--  |         |
-- g|         |
--  V         V
--  C  --->  Pushout


data Pushout {A B C : Type} (f : A → B) (g : A → C) : Type where
  inl : B → Pushout f g
  inr : C → Pushout f g
  push : (a : A) → inl (f a) ≡ inr (g a)


-- Today:
-- - Interval and path types
-- - Cubical HITs

-- Next time (Friday)
-- - Cubical transport and path induction
-- - Set truncated HITs and how to work with them
