This file contains whatever is needed from the agda/cubical library to
get the lectures to typecheck. Warning: it is not very organized or
documented.

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


open import Agda.Builtin.Cubical.Glue public
  using ( isEquiv       -- ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (f : A → B) → Type (ℓ ⊔ ℓ')

        ; equiv-proof   -- ∀ (y : B) → isContr (fiber f y)

        ; _≃_           -- ∀ {ℓ ℓ'} (A : Type ℓ) (B : Type ℓ') → Type (ℓ ⊔ ℓ')

        ; equivFun      -- ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → A ≃ B → A → B

        ; equivProof    -- ∀ {ℓ ℓ'} (T : Type ℓ) (A : Type ℓ') (w : T ≃ A) (a : A) φ →
                        -- Partial φ (fiber (equivFun w) a) → fiber (equivFun w) a

        ; primGlue      -- ∀ {ℓ ℓ'} (A : Type ℓ) {φ : I} (T : Partial φ (Type ℓ'))
                        -- → (e : PartialP φ (λ o → T o ≃ A)) → Type ℓ'

        ; prim^unglue   -- ∀ {ℓ ℓ'} {A : Type ℓ} {φ : I} {T : Partial φ (Type ℓ')}
                        -- → {e : PartialP φ (λ o → T o ≃ A)} → primGlue A T e → A

        -- The ∀ operation on I. This is commented out as it is not currently used for anything
        -- ; primFaceForall -- (I → I) → I
        )
  renaming ( prim^glue   to glue         -- ∀ {ℓ ℓ'} {A : Type ℓ} {φ : I} {T : Partial φ (Type ℓ')}
                                         -- → {e : PartialP φ (λ o → T o ≃ A)}
                                         -- → PartialP φ T → A → primGlue A T e
           )


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

-- Non dependent path types

Path : ∀ {ℓ} (A : Type ℓ) → A → A → Type ℓ
Path A a b = PathP (λ _ → A) a b

-- PathP (λ i → A) x y gets printed as x ≡ y when A does not mention i.
--  _≡_ : ∀ {ℓ} {A : Type ℓ} → A → A → Type ℓ
--  _≡_ {A = A} = PathP (λ _ → A)

-- Path composition
_∙_ : {A : Type ℓ} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
_∙_ {x = x} p q i = hcomp (λ j → λ { (i = i0) → x
                                   ; (i = i1) → q j })
                          (p i)

infixr 30 _∙_


-- Equality reasoning
infix  3 _∎
infixr 2 _≡⟨_⟩_ _≡⟨⟩_

_≡⟨_⟩_ : {A : Type ℓ} (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
_ ≡⟨ x≡y ⟩ y≡z = x≡y ∙ y≡z

≡⟨⟩-syntax : {A : Type ℓ} (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
≡⟨⟩-syntax = _≡⟨_⟩_
infixr 2 ≡⟨⟩-syntax
syntax ≡⟨⟩-syntax x (λ i → B) y = x ≡[ i ]⟨ B ⟩ y

_≡⟨⟩_ : {A : Type ℓ} (x : A) {y : A} → x ≡ y → x ≡ y
_ ≡⟨⟩ x≡y = x≡y

_∎ : {A : Type ℓ} (x : A) → x ≡ x
x ∎ = λ _ → x


_[_↦_] : ∀ {ℓ} (A : Type ℓ) (φ : I) (u : Partial φ A) → SSet ℓ
A [ φ ↦ u ] = Sub A φ u

infix 4 _[_↦_]

--- Homogeneous filling
hfill : {A : Type ℓ} {φ : I} (u : ∀ i → Partial φ A) (u0 : A [ φ ↦ u i0 ]) (i : I) → A
hfill {φ = φ} u u0 i =
  hcomp (λ j → λ { (φ = i1) → u (i ∧ j) 1=1
                 ; (i = i0) → outS u0 })
        (outS u0)

-- Use built in Σ types to avoid problems with the imported Cubical
-- Agda operations that use Σ types
open import Agda.Builtin.Sigma public renaming (fst to pr₁ ; snd to pr₂)

Sigma : {l1 l2 : Level} (A : Type l1) (B : A → Type l2) → Type (l1 ⊔ l2)
Sigma {l1} {l2} A B = Σ {l1} {l2} A B

syntax Sigma A (λ x → b) = Σ x ꞉ A , b

infix -1 Sigma

_×_ : ∀ {l1 l2} → Type l1 → Type l2 → Type (l1 ⊔ l2)
A × B = Sigma A (\ _ → B)

infixr 5 _×_

-- Contractible types, propositions and sets:

isContr : Type ℓ → Type ℓ
isContr A = Σ x ꞉ A , ((y : A) → x ≡ y)

isProp : Type ℓ → Type ℓ
isProp A = (x y : A) → x ≡ y

isSet : Type ℓ → Type ℓ
isSet A = (x y : A) → isProp (x ≡ y)

-- Fibers
fiber : {A : Type ℓ} {B : Type ℓ'} (f : A → B) (y : B) → Set (ℓ ⊔ ℓ')
fiber {A = A} f y = Σ x ꞉ A , f x ≡ y

-- In the agda/cubical library we call these h-levels following
-- Voevodsky instead of n-types and index by natural numbers instead
-- of ℕ₋₂. So isContr is isOfHLevel 0, isProp is isOfHLevel 1, isSet
-- is isOfHLevel 2, etc. For details see Cubical/Foundations/HLevels.agda


-- Sections and retractions
module _ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} where
  section : (f : A → B) → (g : B → A) → Type ℓ'
  section f g = ∀ b → f (g b) ≡ b

  -- NB: `g` is the retraction!
  retract : (f : A → B) → (g : B → A) → Type ℓ
  retract f g = ∀ a → g (f a) ≡ a

-- Isomorphisms
record Iso {ℓ ℓ'} (A : Type ℓ) (B : Type ℓ') : Type (ℓ ⊔ ℓ') where
  no-eta-equality
  constructor iso
  field
    fun : A → B
    inv : B → A
    rightInv : section fun inv
    leftInv  : retract fun inv

-- Any iso is an equivalence (called "improve" by Dan, here we use the
-- contractible fibers version of equivalences)
module _ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (i : Iso A B) where
  open Iso i renaming ( fun to f
                      ; inv to g
                      ; rightInv to s
                      ; leftInv to t)

  private
    module _ (y : B) (x0 x1 : A) (p0 : f x0 ≡ y) (p1 : f x1 ≡ y) where
      fill0 : I → I → A
      fill0 i = hfill (λ k → λ { (i = i1) → t x0 k
                               ; (i = i0) → g y })
                      (inS (g (p0 (~ i))))

      fill1 : I → I → A
      fill1 i = hfill (λ k → λ { (i = i1) → t x1 k
                               ; (i = i0) → g y })
                      (inS (g (p1 (~ i))))

      fill2 : I → I → A
      fill2 i = hfill (λ k → λ { (i = i1) → fill1 k i1
                               ; (i = i0) → fill0 k i1 })
                      (inS (g y))

      p : x0 ≡ x1
      p i = fill2 i i1

      sq : I → I → A
      sq i j = hcomp (λ k → λ { (i = i1) → fill1 j (~ k)
                              ; (i = i0) → fill0 j (~ k)
                              ; (j = i1) → t (fill2 i i1) (~ k)
                              ; (j = i0) → g y })
                     (fill2 i j)

      sq1 : I → I → B
      sq1 i j = hcomp (λ k → λ { (i = i1) → s (p1 (~ j)) k
                               ; (i = i0) → s (p0 (~ j)) k
                               ; (j = i1) → s (f (p i)) k
                               ; (j = i0) → s y k })
                      (f (sq i j))

      lemIso : (x0 , p0) ≡ (x1 , p1)
      lemIso i .pr₁ = p i
      lemIso i .pr₂ = λ j → sq1 i (~ j)

  isoToIsEquiv : isEquiv f
  isoToIsEquiv .equiv-proof y .pr₁ .pr₁ = g y
  isoToIsEquiv .equiv-proof y .pr₁ .pr₂ = s y
  isoToIsEquiv .equiv-proof y .pr₂ z = lemIso y (g y) (pr₁ z) (s y) (pr₂ z)


isoToEquiv : {ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'} → Iso A B → A ≃ B
isoToEquiv i .pr₁ = i .Iso.fun
isoToEquiv i .pr₂ = isoToIsEquiv i

Glue : (A : Type ℓ) {φ : I}
       → (Te : Partial φ (Σ T ꞉ Type ℓ' , T ≃ A))
       → Type ℓ'
Glue A Te = primGlue A (λ x → Te x .pr₁) (λ x → Te x .pr₂)

idEquiv : ∀ {ℓ} (A : Type ℓ) → A ≃ A
idEquiv A .pr₁ = λ x → x
equiv-proof (idEquiv A .pr₂) = λ y → (y , (λ i → y)) , (λ h i → (h .pr₂ (~ i)) , λ j → h .pr₂ ((j ∨ ~ i)))

isoToPath : {A B : Type ℓ} → Iso A B → A ≡ B
isoToPath {A = A} {B = B} f i =
  Glue B (λ { (i = i0) → (A , isoToEquiv f)
            ; (i = i1) → (B , idEquiv B) })

-- Natural numbers. We use the built in ones to be able to use
-- numerals.
open import introduction public
  using (ℕ; zero; suc; _+_)
  renaming (_*_ to _·_)

_-_ : ℕ → ℕ → ℕ
n     - zero = n
zero  - suc m = zero
suc n - suc m = n - m

{-# BUILTIN NATMINUS _-_ #-}


-- Integers (slightly different from how Dan did them in order to have
-- one less constructor to pattern match on)
data ℤ : Type₀ where
  pos    : (n : ℕ) → ℤ
  negsuc : (n : ℕ) → ℤ

sucℤ : ℤ → ℤ
sucℤ (pos n)          = pos (suc n)
sucℤ (negsuc zero)    = pos zero
sucℤ (negsuc (suc n)) = negsuc n

predℤ : ℤ → ℤ
predℤ (pos zero)    = negsuc zero
predℤ (pos (suc n)) = pos n
predℤ (negsuc n)    = negsuc (suc n)

sucPred : ∀ i → sucℤ (predℤ i) ≡ i
sucPred (pos zero)    = λ i → pos zero
sucPred (pos (suc n)) = λ i → pos (suc n)
sucPred (negsuc n)    = λ i → negsuc n

predSuc : ∀ i → predℤ (sucℤ i) ≡ i
predSuc (pos n)          = λ i → pos n
predSuc (negsuc zero)    = λ i → negsuc zero
predSuc (negsuc (suc n)) = λ i → negsuc (suc n)

sucPath : ℤ ≡ ℤ
sucPath = isoToPath (iso sucℤ predℤ sucPred predSuc)



-- 'Data' types from Martín's prelude
record Unit : Type where
 constructor
  ⋆

open Unit public

data Bool : Type where
 true false : Bool

```
