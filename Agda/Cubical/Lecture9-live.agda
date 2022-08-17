-- Lecture 9: Cubical Agda

{-# OPTIONS --cubical #-}

module Lecture9-live where

open import cubical-prelude hiding (_∙_)
open import Lecture7-notes
open import Lecture8-notes hiding (compPath)

private
  variable
    A B : Type ℓ

-- Last time:
-- - Set quotients
-- - Cubical transport and path induction
-- - Homogeneous composition (`hcomp`)


-- Today:
-- - More about homogeneous composition (`hcomp`)
-- - Cubical univalence (Glue types)
-- - The structure identity principle (SIP)




-- More about hcomp


compPath : {x y z : A} → x ≡ y → y ≡ z → x ≡ z
compPath {x = x} p q i =
  hcomp (λ j → λ { (i = i0) → x
                 ; (i = i1) → q j })   -- System of sides
        (p i)                          -- The base of the hcomp

{-
    x             z
    ^             ^
    ¦             ¦
  x ¦             ¦ q j
    ¦             ¦
    x ----------> y
          p i
-}

_∙∙_∙∙_ : {x y z w : A} → x ≡ y → y ≡ z → z ≡ w → x ≡ w
_∙∙_∙∙_ p q r i =
  hcomp (λ j → λ { (i = i0) → p (~ j)
                 ; (i = i1) → r j })
        (q i)

{-
         x             w
         ^             ^
         ¦             ¦
 p (~ j) ¦             ¦ r j
         ¦             ¦
         y ----------> z
               q i
-}

_∙_ : {x y z : A} → x ≡ y → y ≡ z → x ≡ z
_∙_ p q = refl ∙∙ p ∙∙ q


-- The hcomp operation is a cubical version of lifting conditions for Kan complexes


-- What is the type of the weird first argument to hcomp?

-- Answer: I → .(IsOne φ) → A

-- IsOne φ   represents   (φ = i1)

-- Partial φ A   the type of partial elements of A, i.e. the type of cubes in A that are defined when IsOne φ holds

-- Question: is Partial φ A the same as (IsOne φ) → A ?
-- Answer: not exactly, Partial φ A is "more extensional" (elements equal up to permutation, duplication...)

-- Partial (i ∨ ~ i) Bool   ≐   Partial (~ i ∨ i) Bool

partialBool : (i : I) → Partial (i ∨ ~ i) Bool
partialBool i = λ { (i = i0) → true
                  ; (i = i1) → false }

partialBool' : (i j : I) → Partial (~ i ∨ i ∨ (i ∧ j)) Bool
partialBool' i j (i = i0) = true
partialBool' i j (i = i1) = true
partialBool' i j (i = i1) (j = i1) = true


-- partialBoolBad : (i : I) → Bool
-- partialBoolBad i0 = true
-- partialBoolBad i1 = false



-- Cubical subtypes

{-

_[_↦_] : (A : Type ℓ) (φ : I) (u : Partial φ A) → SSet ℓ
A [ φ ↦ u ] = Sub A φ u

inS : {A : Type ℓ} {φ : I} (u : A) → A [ φ ↦ (λ _ → u) ]

outS : {A : Type ℓ} {φ : I} {u : Partial φ A} → A [ φ ↦ u ] → A

They satisfy the following equalities:

outS (inS a) ≐ a

inS {φ = φ} (outS {φ = φ} a) ≐ a

outS {φ = i1} {u} _ ≐ u 1=1

-}


hcomp' : {A : Type} {φ : I} (u : I → Partial φ A) (u0 : A [ φ ↦ u i0 ]) → A [ φ ↦ u i1 ]
hcomp' u u0 = inS (hcomp u (outS u0))





-- Cubical univalence (Glue types)


ua : {A B : Type} → A ≃ B → A ≡ B
ua {A = A} {B = B} e i =
  Glue B λ { (i = i0) → A , e
           ; (i = i1) → B , idEquiv B }


uaβ : (e : A ≃ B) → (a : A) → transport (ua e) a ≡ pr₁ e a
uaβ e a = transportRefl (pr₁ e a)


uaβℕ : (e : ℕ ≃ ℕ) → (a : ℕ) → transport (ua e) a ≡ pr₁ e a
uaβℕ e a = refl


-- Fact: ua + uaβ ⇒ univalence axiom


-- Examples

not : Bool → Bool
not true = false
not false = true

notPath : Bool ≡ Bool
notPath = ua (isoToEquiv (iso not not rem rem))
  where
  rem : (b : Bool) → not (not b) ≡ b
  rem true = refl
  rem false = refl



-- The structure identity principle (SIP)


substEquiv : (S : Type → Type) (e : A ≃ B) → S A → S B
substEquiv S e = subst S (ua e)


-- Easy exercise (in the notes): substEquiv induces and equivalence

-- Example: S could be IsMonoid


-- This is useful for many things!

-- One application: Can program with one type and prove using another equivalent type

{-

data Pos : Type where
  pos1 : Pos
  x0 : Pos → Pos
  x1 : Pos → Pos

-- x1 (x0 (x1 pos1)) = 1101 = 13

data Bin : Type where
  bin0 : Bin
  binPos : Pos → Bin

-}


ℕ≃Bin : ℕ ≃ Bin
ℕ≃Bin = isoToEquiv (iso ℕ→Bin Bin→ℕ Bin→ℕ→Bin ℕ→Bin→ℕ)


SemiGroup : Type → Type
SemiGroup A = Σ _·_ ꞉ (A → A → A) , ((x y z : A) → x · (y · z) ≡ (x · y) · z)

SemiGroupℕ : SemiGroup ℕ
SemiGroupℕ = _+_ , +-assoc

SemiGroupBin : SemiGroup Bin
SemiGroupBin = substEquiv SemiGroup ℕ≃Bin SemiGroupℕ

_+Bin_ : Bin → Bin → Bin
_+Bin_ = pr₁ SemiGroupBin

+Bin-assoc : (x y z : Bin) → x +Bin (y +Bin z) ≡ (x +Bin y) +Bin z
+Bin-assoc = pr₂ SemiGroupBin



mutual
  _+P_ : Pos → Pos → Pos
  pos1  +P y     = sucPos y
  x0 x  +P pos1  = x1 x
  x0 x  +P x0 y  = x0 (x +P y)
  x0 x  +P x1 y  = x1 (x +P y)
  x1 x  +P pos1  = x0 (sucPos x)
  x1 x  +P x0 y  = x1 (x +P y)
  x1 x  +P x1 y  = x0 (x +PC y)

  _+B_ : Bin → Bin → Bin
  bin0      +B y         = y
  x         +B bin0      = x
  binPos x  +B binPos y  = binPos (x +P y)

  -- Add with carry
  _+PC_ : Pos → Pos → Pos
  pos1  +PC pos1  = x1 pos1
  pos1  +PC x0 y  = x0 (sucPos y)
  pos1  +PC x1 y  = x1 (sucPos y)
  x0 x  +PC pos1  = x0 (sucPos x)
  x0 x  +PC x0 y  = x1 (x +P y)
  x0 x  +PC x1 y  = x0 (x +PC y)
  x1 x  +PC pos1  = x1 (sucPos x)
  x1 x  +PC x0 y  = x0 (x +PC y)
  x1 x  +PC x1 y  = x1 (x +PC y)





-- How to prove that +B is associative?  (By hand = total pain)






-- Correctness:
+PC-suc : (x y : Pos) → x +PC y ≡ sucPos (x +P y)
+PC-suc pos1 pos1     = refl
+PC-suc pos1 (x0 y)   = refl
+PC-suc pos1 (x1 y)   = refl
+PC-suc (x0 x) pos1   = refl
+PC-suc (x0 x) (x0 y) = refl
+PC-suc (x0 x) (x1 y) = ap x0 (+PC-suc x y)
+PC-suc (x1 x) pos1   = refl
+PC-suc (x1 x) (x0 y) = ap x0 (+PC-suc x y)
+PC-suc (x1 x) (x1 y) = refl

sucPos-+P : (x y : Pos) → sucPos (x +P y) ≡ sucPos x +P y
sucPos-+P pos1 pos1     = refl
sucPos-+P pos1 (x0 y)   = refl
sucPos-+P pos1 (x1 y)   = refl
sucPos-+P (x0 x) pos1   = refl
sucPos-+P (x0 x) (x0 y) = refl
sucPos-+P (x0 x) (x1 y) = ap x0 (sym (+PC-suc x y))
sucPos-+P (x1 x) pos1   = refl
sucPos-+P (x1 x) (x0 y) = ap x0 (sucPos-+P x y)
sucPos-+P (x1 x) (x1 y) = ap x1 (+PC-suc  x y ∙ sucPos-+P x y)

ℕ→Pos-+P : (x y : ℕ) → ℕ→Pos (suc x + suc y) ≡ ℕ→Pos (suc x) +P ℕ→Pos (suc y)
ℕ→Pos-+P zero _    = refl
ℕ→Pos-+P (suc x) y = ap sucPos (ℕ→Pos-+P x y) ∙ sucPos-+P (ℕ→Pos (suc x)) (ℕ→Pos (suc y))

ℕ→Bin-+B : (x y : ℕ) → ℕ→Bin (x + y) ≡ ℕ→Bin x +B ℕ→Bin y
ℕ→Bin-+B zero y          = refl
ℕ→Bin-+B (suc x) zero    = ap (λ x → binPos (ℕ→Pos (suc x))) (+-zero x)
ℕ→Bin-+B (suc x) (suc y) = ap binPos (ℕ→Pos-+P x y)




+B≡+Bin : _+B_ ≡ _+Bin_
+B≡+Bin i x y = goal x y i
  where
  goal : (x y : Bin) → x +B y ≡ ℕ→Bin (Bin→ℕ x + Bin→ℕ y)
  goal x y =  (λ i → Bin→ℕ→Bin x (~ i) +B Bin→ℕ→Bin y (~ i))
           ∙  sym (ℕ→Bin-+B (Bin→ℕ x) (Bin→ℕ y))




+B-assoc : (m n o : Bin) → m +B (n +B o) ≡ (m +B n) +B o
+B-assoc m n o =
           (λ i → +B≡+Bin i m (+B≡+Bin i n o))
               ∙∙ +Bin-assoc m n o
               ∙∙ (λ i → +B≡+Bin (~ i) (+B≡+Bin (~ i) m n) o)



-- The agda/cubical library has convenient automation for making a lot
-- of this easier
