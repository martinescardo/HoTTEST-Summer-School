# Lecture 9

Contents:

- More about homogeneous composition (`hcomp`)
- Cubical univalence (Glue types) + SIP
- Some cool example of transporting programs/proofs using the SIP and
  then computing with the result

```agda
{-# OPTIONS --cubical #-}

module Lecture9-notes where

open import cubical-prelude
open import Lecture7-notes
open import Lecture8-notes hiding (compPath ; _∙∙_∙∙_)

private
  variable
    A B : Type ℓ

```

## More about homogeneous composition (`hcomp`)

Recall from Lecture 8: in order to compose two paths we write:

```agda
compPath : {x y z : A} → x ≡ y → y ≡ z → x ≡ z
compPath {x = x} p q i = hcomp (λ j → λ { (i = i0) → x
                                        ; (i = i1) → q j })
                               (p i)
```

This is best understood with the following drawing:

```text
    x             z
    ^             ^
    ¦             ¦
  x ¦             ¦ q j
    ¦             ¦
    x ----------> y
          p i
```

In the drawing the direction `i` goes left-to-right and `j` goes
bottom-to-top. As we are constructing a path from `x` to `z` along `i`
we have `i : I` in the context already and we put `p i` as bottom. The
direction `j` that we are doing the composition in is abstracted in
the first argument to `hcomp`.

Side remark: this operation is related to lifting conditions for Kan
cubical sets, i.e. it's a form of open box filling analogous to horn
filling in Kan complexes.

A more natural form of composition of paths in Cubical Agda is
ternary composition:

```text
         x             w
         ^             ^
         ¦             ¦
 p (~ j) ¦             ¦ r j
         ¦             ¦
         y ----------> z
               q i
```

This is written `p ∙∙ q ∙∙ r` in the agda/cubical library and
implemented by:

```agda
_∙∙_∙∙_ : {x y z w : A} → x ≡ y → y ≡ z → z ≡ w → x ≡ w
(p ∙∙ q ∙∙ r) i = hcomp (λ j → λ { (i = i0) → p (~ j)
                                 ; (i = i1) → r j })
                        (q i)
```

Using this we can define compPath much slicker:

```text
_∙_ : {x y z : A} → x ≡ y → y ≡ z → x ≡ z
p ∙ q = refl ∙∙ p ∙∙ q
```

In order to understand the second argument to `hcomp` we need to talk
about partial elements and cubical subtypes. These allow us to write
partially specified n-dimensional cubes (i.e. cubes where some faces
are missing as in the input to `hcomp`).

### Partial elements

Given an element of the interval `r : I` there is a predicate `IsOne`
which represents the constraint `r = i1`. This comes with a proof that
`i1` is in fact equal to `i1` called `1=1 : IsOne i1`. We use Greek
letters like `φ` or `ψ` when such an `r` should be thought of as being
in the domain of `IsOne`.

Using this we introduce a type of partial elements called `Partial φ
A`, this is a special version of `IsOne φ → A` with a more extensional
judgmental equality (two elements of `Partial φ A` are considered
equal if they represent the same subcube, so the faces of the cubes
can for example be given in different order and the two elements will
still be considered the same). The idea is that `Partial φ A` is the
type of cubes in `A` that are only defined when `IsOne φ`. There is also a
dependent version of this called `PartialP φ A` which allows `A` to be
defined only when `IsOne φ`.

```text
Partial : ∀ {ℓ} → I → Set ℓ → SSet ℓ

PartialP : ∀ {ℓ} → (φ : I) → Partial φ (Set ℓ) → SSet ℓ
```

Here `SSet` is the universe of *strict* sets.

Cubical Agda has a new form of pattern matching that can be used to
introduce partial elements:

```agda
partialBool : (i : I) → Partial (i ∨ ~ i) Bool
partialBool i (i = i0) = true
partialBool i (i = i1) = false
```

The term `partialBool i` should be thought of a boolean with different
values when `(i = i0)` and `(i = i1)`. Note that this is different
from pattern matching on the interval which is not allowed, so we
couldn't have written:

```text
partialBool : (i : I) → Bool
partialBool i0 = true
partialBool i1 = false
```

Terms of type `Partial φ A` can also be introduced using a pattern
matching lambda and this is what we have been using when we wrote
`hcomp`'s above.

```agda
partialBool' : (i : I) → Partial (i ∨ ~ i) Bool
partialBool' i = λ { (i = i0) → true
                   ; (i = i1) → false }
```

When the cases overlap they must agree (note that the order of the
cases doesn’t have to match the interval formula exactly):

```agda
partialBool'' : (i j : I) → Partial (~ i ∨ i ∨ (i ∧ j)) Bool
partialBool'' i j = λ { (i = i1)          → true
                      ; (i = i1) (j = i1) → true
                      ; (i = i0)          → false }
```

Furthermore `IsOne i0` is actually absurd.

```agda
_ : {A : Type} → Partial i0 A
_ = λ { () }
```

With this cubical infrastructure we can now describe the type of the
`hcomp` operation.

```text
hcomp : {A : Type ℓ} {φ : I} (u : I → Partial φ A) (u0 : A) → A
```

When calling `hcomp {φ = φ} u u0` Agda makes sure that `u0` agrees
with `u i0` on `φ`. The result is then an element of `A` which agrees
with `u i1` on `φ`. The idea being that `u0` is the base and `u`
specifies the sides of an open box while `hcomp u u0` is the lid of
the box. In fact, we can use yet another cubical construction to
specify these side conditions in the type of `hcomp`. For this we need
to talk about cubical subtypes.

### Cubical subtypes and filling

Cubical Agda also has cubical subtypes as in the CCHM type theory:

```text
_[_↦_] : (A : Type ℓ) (φ : I) (u : Partial φ A) → SSet ℓ
A [ φ ↦ u ] = Sub A φ u
```

A term `v : A [ φ ↦ u ]` should be thought of as a term of type `A`
which is definitionally equal to `u : A` when `IsOne φ` is
satisfied. Any term `u : A` can be seen as a term of `A [ φ ↦ u ]`
which agrees with itself on `φ`:

```text
inS : {A : Type ℓ} {φ : I} (u : A) → A [ φ ↦ (λ _ → u) ]
```

One can also forget that a partial element agrees with `u` on `φ`:

```text
outS : {A : Type ℓ} {φ : I} {u : Partial φ A} → A [ φ ↦ u ] → A
```

They satisfy the following equalities:

```text
outS (inS a) ≐ a

inS {φ = φ} (outS {φ = φ} a) ≐ a

outS {φ = i1} {u} _ ≐ u 1=1
```

Note that given `a : A [ φ ↦ u ]` and `α : IsOne φ`, it is not the case
that `outS a ≐ u α`; however, underneath the pattern binding `(φ = i1)`,
one has `outS a ≐ u 1=1`.

With this we can now give `hcomp` the following more specific type:

```agda
hcomp' : {A : Type ℓ} {φ : I} (u : I → Partial φ A) (u0 : A [ φ ↦ u i0 ]) → A [ φ ↦ u i1 ]
hcomp' u u0 = inS (hcomp u (outS u0))
```

This more specific type is of course more informative, but it quickly
gets quite annoying to write `inS`/`outS` everywhere. So the builtin
`hcomp` operation comes with the slightly less informative type and
the side conditions are then implicit and checked internally.

Another very useful operation is open box *filling*. This produces an
element corresponding to the interior of the open box:

```agda
hfill' : {A : Type ℓ} {φ : I}
         (u : ∀ i → Partial φ A)
         (u0 : A [ φ ↦ u i0 ])
         (i : I) →
         A [ φ ∨ ~ i ∨ i ↦
            (λ { (φ = i1) → u i 1=1
               ; (i = i0) → outS u0
               ; (i = i1) → hcomp u (outS u0) }) ]
hfill' {φ = φ} u u0 i = inS (hcomp (λ j → λ { (φ = i1) → u (i ∧ j) 1=1
                                       ; (i = i0) → outS u0 })
                              (outS u0))
```

This has a slightly less informative type in the cubical-prelude:

```text
hfill : {A : Type ℓ} {φ : I} (u : ∀ i → Partial φ A) (u0 : A [ φ ↦ u i0 ]) (i : I) → A
hfill {φ = φ} u u0 i =
  hcomp (λ j → λ { (φ = i1) → u (i ∧ j) 1=1
                 ; (i = i0) → outS u0 })
        (outS u0)
```

Having defined this operation we can prove various groupoid laws for
`_≡_` very cubically as `_∙_` is defined using `hcomp`.

```agda
compPathRefl : {A : Type ℓ} {x y : A} (p : x ≡ y) → p ∙ refl ≡ p
compPathRefl {x = x} {y = y} p j i = hfill (λ _ → λ { (i = i0) → x
                                                    ; (i = i1) → y })
                                           (inS (p i))
                                           (~ j)
```

For more examples see Cubical.Foundations.GroupoidLaws in agda/cubical.


## Cubical univalence (Glue types) + SIP

A key concept in HoTT/UF is univalence. As we have seen earlier in the
week this is assumed as an axiom in Book HoTT. In Cubical Agda it is
instead provable and has computational content. This means that
transporting with paths constructed using univalence reduces as
opposed to Book HoTT where they would be stuck. This simplifies many
proofs and make it possible to actually do concrete computations using
univalence.

The part of univalence which is most useful for our applications is to
be able to turn equivalences (written `_≃_` and defined as a Σ-type of
a function and a proof that it has contractible fibers) into paths:

```agda
ua : {A B : Type ℓ} → A ≃ B → A ≡ B
ua {A = A} {B = B} e i = Glue B (λ { (i = i0) → (A , e)
                                   ; (i = i1) → (B , idEquiv B) })
```

This term is defined using "Glue types" which were introduced in the
CCHM paper. We won't have time to go into too much details about them
today, but for practical applications one can usually forget about
them and use `ua` as a black box. The key idea though is that they are
similar to `hcomp`'s, but instead of attaching (higher dimensional)
paths to a base we attach equivalence to a type. One of the original
applications of this was to give computational meaning to transporting
in a line of types constructed by `hcomp` in the universe (`Type`).

For us today the important point is that transporting along the path
constructed using `ua` applies the function underlying the
equivalence. This is easily proved using `transportRefl`:

```agda
uaβ : (e : A ≃ B) (x : A) → transport (ua e) x ≡ pr₁ e x
uaβ e x = transportRefl (equivFun e x)
```

Note that for concrete types this typically hold definitionally, but
for an arbitrary equivalence `e` we have to prove it.

The fact that we have both ua and uaβ suffices to be able to prove the
standard formulation of univalence. For details see
Cubical.Foundations.Univalence in the agda/cubical library.x

The standard way of constructing equivalences is to start with an
isomorphism and then improve it into an equivalence. The lemma in
the library which does this is

```text
isoToEquiv : {A B : Type ℓ} → Iso A B → A ≃ B
```

Composing this with `ua` lets us directly turn isomorphisms into paths:

```text
isoToPath : {A B : Type ℓ} → Iso A B → A ≡ B
isoToPath e = ua (isoToEquiv e)
```

Time for an example!

```agda
not : Bool → Bool
not false = true
not true  = false

notPath : Bool ≡ Bool
notPath = isoToPath (iso not not rem rem)
  where
  rem : (b : Bool) → not (not b) ≡ b
  rem false = refl
  rem true  = refl

_ : transport notPath true ≡ false
_ = refl
```

Another example, integers:

```agda
_ : transport sucPath (pos 0) ≡ pos 1
_ = refl

_ : transport (sucPath ∙ sucPath) (pos 0) ≡ pos 2
_ = refl

_ : transport (sym sucPath) (pos 0) ≡ negsuc 0
_ = refl
```

Note that we have already used this in the `winding` function in Lecture 7.

One can do more fun things with `sucPath`. For example by composing it
with `n` times and then transporting along this we get a new addition
function. By transporting along it backwards we will get subtraction.
We can use this to `_+ℤ'_` for which is easier to prove `isEquiv (λ n
→ n +ℤ' m)` since `_+ℤ'_` is defined by `transport`.

```agda
addPath : ℕ → ℤ ≡ ℤ
addPath zero = refl
addPath (suc n) = addPath n ∙ sucPath

predPath : ℤ ≡ ℤ
predPath = isoToPath (iso predℤ sucℤ predSuc sucPred)

subPath : ℕ → ℤ ≡ ℤ
subPath zero = refl
subPath (suc n) = subPath n ∙ predPath

_+ℤ'_ : ℤ → ℤ → ℤ
m +ℤ' pos n    = transport (addPath n) m
m +ℤ' negsuc n = transport (subPath (suc n)) m

-- This agrees with regular addition defined by pattern-matching
+ℤ'≡+ℤ : _+ℤ'_ ≡ _+ℤ_
+ℤ'≡+ℤ i m (pos zero) = m
+ℤ'≡+ℤ i m (pos (suc n)) = sucℤ (+ℤ'≡+ℤ i m (pos n))
+ℤ'≡+ℤ i m (negsuc zero) = predℤ m
+ℤ'≡+ℤ i m (negsuc (suc n)) = predℤ (+ℤ'≡+ℤ i m (negsuc n))

-- We can prove that transport is an equivalence easily
isEquivTransport : {A B : Type ℓ} (p : A ≡ B) → isEquiv (transport p)
isEquivTransport p =
  transport (λ i → isEquiv (transp (λ j → p (i ∧ j)) (~ i))) (idEquiv _ .pr₂)

-- So +ℤ' with a fixed element is an equivalence
isEquivAddℤ' : (m : ℤ) → isEquiv (λ n → n +ℤ' m)
isEquivAddℤ' (pos n)    = isEquivTransport (addPath n)
isEquivAddℤ' (negsuc n) = isEquivTransport (subPath (suc n))

isEquivAddℤ : (m : ℤ) → isEquiv (λ n → n +ℤ m)
isEquivAddℤ = subst (λ add → (m : ℤ) → isEquiv (λ n → add n m)) +ℤ'≡+ℤ isEquivAddℤ'
```


### The structure identity principle

Combining subst and ua lets us transport any structure on A to get
a structure on an equivalent type B

```agda
substEquiv : (S : Type ℓ → Type ℓ') (e : A ≃ B) → S A → S B
substEquiv S e = subst S (ua e)
```


**TODO:** do something about the SIP!

```agda


data Pos : Type where
  pos1  : Pos
  x0    : Pos → Pos
  x1    : Pos → Pos

sucPos : Pos → Pos
sucPos pos1     = x0 pos1
sucPos (x0 ps)  = x1 ps
sucPos (x1 ps)  = x0 (sucPos ps)

-- Conversion of Pos to ℕ.

Pos→ℕ : Pos → ℕ
Pos→ℕ pos1     = suc zero
Pos→ℕ (x0 ps)  = doubleℕ (Pos→ℕ ps)
Pos→ℕ (x1 ps)  = suc (doubleℕ (Pos→ℕ ps))

-- Unary number induction on Pos.

posInd : {P : Pos → Type} → P pos1 → ((p : Pos) → P p → P (sucPos p)) → (p : Pos) → P p
posInd {P} h1 hs = f
  where
  H : (p : Pos) → P (x0 p) → P (x0 (sucPos p))
  H p hx0p  = hs (x1 p) (hs (x0 p) hx0p)

  f : (ps : Pos) → P ps
  f pos1     = h1
  f (x0 ps)  = posInd (hs pos1 h1) H ps
  f (x1 ps)  = hs (x0 ps) (posInd (hs pos1 h1) H ps)

-- Pos→ℕ is suc-morphism.

Pos→ℕsucPos : (p : Pos) → Pos→ℕ (sucPos p) ≡ suc (Pos→ℕ p)
Pos→ℕsucPos pos1    = refl
Pos→ℕsucPos (x0 p)  = refl
Pos→ℕsucPos (x1 p)  = λ i → doubleℕ (Pos→ℕsucPos p i)

caseNat : ∀ {ℓ} → {A : Type ℓ} → (a0 aS : A) → ℕ → A
caseNat a0 aS zero    = a0
caseNat a0 aS (suc n) = aS

-- zero is not in the image of Pos→ℕ.
znots : {n : ℕ} → ¬ (0 ≡ suc n)
znots eq = subst (caseNat ℕ ⊥) eq 0

zero≠Pos→ℕ : (p : Pos) → ¬ (zero ≡ Pos→ℕ p)
zero≠Pos→ℕ p  = posInd (λ prf → znots prf) hs p
  where
  hs : (p : Pos) → ¬ (zero ≡ Pos→ℕ p) → zero ≡ Pos→ℕ (sucPos p) → ⊥
  hs p neq ieq  = ⊥-rec (znots (ieq ∙ Pos→ℕsucPos p))

-- Conversion from ℕ to Pos.

ℕ→Pos : ℕ → Pos
ℕ→Pos zero           = pos1
ℕ→Pos (suc zero)     = pos1
ℕ→Pos (suc (suc n))  = sucPos (ℕ→Pos (suc n))

-- ℕ→Pos is a suc-morphism on { n | n ≥ 1 }.

ℕ→PosSuc : ∀ n → ¬ (zero ≡ n) → ℕ→Pos (suc n) ≡ sucPos (ℕ→Pos n)
ℕ→PosSuc zero neq     = ⊥-elim (neq refl)
ℕ→PosSuc (suc n) neq  = refl

-- Isomorphism, proven by unary number induction.

Pos→ℕ→Pos : (p : Pos) → ℕ→Pos (Pos→ℕ p) ≡ p
Pos→ℕ→Pos p  = posInd refl hs p
  where
  hs : (p : Pos) → ℕ→Pos (Pos→ℕ p) ≡ p → ℕ→Pos (Pos→ℕ (sucPos p)) ≡ sucPos p
  hs p hp  =
    ℕ→Pos (Pos→ℕ (sucPos p)) ≡⟨ ap ℕ→Pos (Pos→ℕsucPos p) ⟩
    ℕ→Pos (suc (Pos→ℕ p))    ≡⟨ ℕ→PosSuc (Pos→ℕ p) (zero≠Pos→ℕ p) ⟩
    sucPos (ℕ→Pos (Pos→ℕ p)) ≡⟨ ap sucPos hp ⟩
    sucPos p ∎

ℕ→Pos→ℕ : (n : ℕ) → Pos→ℕ (ℕ→Pos (suc n)) ≡ suc n
ℕ→Pos→ℕ zero     = refl
ℕ→Pos→ℕ (suc n)  =
  Pos→ℕ (sucPos (ℕ→Pos (suc n))) ≡⟨ Pos→ℕsucPos (ℕ→Pos (suc n)) ⟩
  suc (Pos→ℕ (ℕ→Pos (suc n)))    ≡⟨ ap suc (ℕ→Pos→ℕ n) ⟩
  suc (suc n) ∎

-- Binary numbers
data Bin : Type where
  bin0    : Bin
  binPos  : Pos → Bin

ℕ→Bin : ℕ → Bin
ℕ→Bin zero     = bin0
ℕ→Bin (suc n)  = binPos (ℕ→Pos (suc n))

Bin→ℕ : Bin → ℕ
Bin→ℕ bin0        = zero
Bin→ℕ (binPos x)  = Pos→ℕ x

ℕ→Bin→ℕ : (n : ℕ) → Bin→ℕ (ℕ→Bin n) ≡ n
ℕ→Bin→ℕ zero           = refl
ℕ→Bin→ℕ (suc zero)     = refl
ℕ→Bin→ℕ (suc (suc n))  =
    Pos→ℕ (sucPos (ℕ→Pos (suc n))) ≡⟨ Pos→ℕsucPos (ℕ→Pos (suc n)) ⟩
    suc (Pos→ℕ (ℕ→Pos (suc n)))    ≡⟨ ap suc (ℕ→Bin→ℕ (suc n)) ⟩
    suc (suc n) ∎

Bin→ℕ→Bin : (n : Bin) → ℕ→Bin (Bin→ℕ n) ≡ n
Bin→ℕ→Bin bin0  = refl
Bin→ℕ→Bin (binPos p)  = posInd refl (λ p _ → rem p) p
  where
  rem : (p : Pos) → ℕ→Bin (Pos→ℕ (sucPos p)) ≡ binPos (sucPos p)
  rem p  =
    ℕ→Bin (Pos→ℕ (sucPos p))       ≡⟨ ap ℕ→Bin (Pos→ℕsucPos p) ⟩
    binPos (ℕ→Pos (suc (Pos→ℕ p))) ≡⟨ ap binPos (ℕ→PosSuc (Pos→ℕ p) (zero≠Pos→ℕ p) ∙
                                                              (ap sucPos (Pos→ℕ→Pos p))) ⟩
    binPos (sucPos p) ∎

ℕ≃Bin : ℕ ≃ Bin
ℕ≃Bin  = isoToEquiv (iso ℕ→Bin Bin→ℕ Bin→ℕ→Bin ℕ→Bin→ℕ)

ℕ≡Bin : ℕ ≡ Bin
ℕ≡Bin  = ua ℕ≃Bin



T : Type → Type
T X = Σ _+_ ꞉ (X → X → X) , ((x y z : X) → x + (y + z) ≡ (x + y) + z)


TBin : T Bin
TBin = subst T ℕ≡Bin (_+_ , +-assoc)

_+Bin_ : Bin → Bin → Bin
_+Bin_  = pr₁ TBin

+Bin-assoc : (m n o : Bin) → m +Bin (n +Bin o) ≡ (m +Bin n) +Bin o
+Bin-assoc = pr₂ TBin
```


This is however not always what we want as _+Bin_ will translate its
input to unary numbers, add, and then translate back. Instead we want
to use efficient addition on binary numbers, but get the associativity
proof for free. So what we really want is to characterize the equality
of T-structured types, i.e. we want a proof that two types equipped
with T-structures are equal if there is a T-structure preserving
equivalence between them. This is the usual meaning of the *structure
identity principle* (SIP). This implies in particular that the type of
paths of monoids/groups/rings/R-modules/... is equivalent to the type
of monoid/group/ring/R-module/... preserving equivalences.

We formalize this and much more using a cubical version of the SIP in:

Internalizing Representation Independence with Univalence
Carlo Angiuli, Evan Cavallo, Anders Mörtberg, Max Zeuner
https://arxiv.org/abs/2009.05547

The binary numbers example with efficient addition is spelled out
in detail in Section 2.1.1 of:

https://www.doi.org/10.1017/S0956796821000034
(Can be downloaded from: https://staff.math.su.se/anders.mortberg/papers/cubicalagda2.pdf)


```



-- fast add
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

-- This amounts to proving that (x y : Bin) → x +B y ≡ ℕ→Bin (Bin→ℕ x + Bin→ℕ y)
+B≡+Bin : _+B_ ≡ _+Bin_
+B≡+Bin i x y = goal x y i
  where
  goal : (x y : Bin) → x +B y ≡ ℕ→Bin (Bin→ℕ x + Bin→ℕ y)
  goal x y =  (λ i → Bin→ℕ→Bin x (~ i) +B Bin→ℕ→Bin y (~ i))
           ∙  sym (ℕ→Bin-+B (Bin→ℕ x) (Bin→ℕ y))

+B-assoc : (m n o : Bin) → m +B (n +B o) ≡ (m +B n) +B o
+B-assoc m n o =  (λ i → +B≡+Bin i m (+B≡+Bin i n o))
               ∙  +Bin-assoc m n o
               ∙  (λ i → +B≡+Bin (~ i) (+B≡+Bin (~ i) m n) o)

```






Here's another cooler example involving matrices:

```agda
infixr 5 _∷_

data Vec (A : Type) : ℕ → Type where
  []  : Vec A zero
  _∷_ : ∀ {n} (x : A) (xs : Vec A n) → Vec A (suc n)

replicate : ∀ {n} {A : Type} → A → Vec A n
replicate {n = zero}  x = []
replicate {n = suc n} x = x ∷ replicate x

data Fin : ℕ → Type where
  zero : {n : ℕ} → Fin (suc n)
  suc  : {n : ℕ} (i : Fin n) → Fin (suc n)

¬Fin0 : ¬ Fin 0
¬Fin0 ()

_==_ : ∀ {n} → Fin n → Fin n → Bool
zero == zero   = true
zero == suc _  = false
suc _ == zero  = false
suc m == suc n = m == n

lookup : {A : Type} {n : ℕ} → Fin n → Vec A n → A
lookup zero    (x ∷ xs) = x
lookup (suc i) (x ∷ xs) = lookup i xs

FinVec→Vec : {A : Type} {n : ℕ} → (Fin n → A) → Vec A n
FinVec→Vec {n = zero}  xs = []
FinVec→Vec {n = suc _} xs = xs zero ∷ FinVec→Vec (λ x → xs (suc x))

Vec→FinVec : {A : Type} {n : ℕ} → Vec A n → (Fin n → A)
Vec→FinVec xs f = lookup f xs

Vec→FinVec→Vec : {A : Type} {n : ℕ} (xs : Vec A n) → FinVec→Vec (Vec→FinVec xs) ≡ xs
Vec→FinVec→Vec {n = zero}  [] = refl
Vec→FinVec→Vec {n = suc n} (x ∷ xs) i = x ∷ Vec→FinVec→Vec xs i

FinVec→Vec→FinVec : {A : Type} {n : ℕ} (xs : Fin n → A) → Vec→FinVec (FinVec→Vec xs) ≡ xs
FinVec→Vec→FinVec {n = zero} xs = funExt λ f → ⊥-rec (¬Fin0 f)
FinVec→Vec→FinVec {n = suc n} xs = funExt goal
  where
  goal : (f : Fin (suc n))
       → Vec→FinVec (xs zero ∷ FinVec→Vec (λ x → xs (suc x))) f ≡ xs f
  goal zero = refl
  goal (suc f) i = FinVec→Vec→FinVec (λ x → xs (suc x)) i f



VecMatrix : (A : Type) (m n : ℕ) → Type
VecMatrix A m n = Vec (Vec A n) m

FinMatrix : (A : Type) (m n : ℕ) → Type
FinMatrix A m n = Fin m → Fin n → A

FinMatrix→VecMatrix : {A : Type} {m n : ℕ} → FinMatrix A m n → VecMatrix A m n
FinMatrix→VecMatrix M = FinVec→Vec (λ fm → FinVec→Vec (λ fn → M fm fn))

VecMatrix→FinMatrix : {A : Type} {m n : ℕ} → VecMatrix A m n → FinMatrix A m n
VecMatrix→FinMatrix M fn fm = Vec→FinVec (Vec→FinVec M fn) fm

FinMatrix→VecMatrix→FinMatrix : {A : Type} {m n : ℕ} (M : FinMatrix A m n) → VecMatrix→FinMatrix (FinMatrix→VecMatrix M) ≡ M
FinMatrix→VecMatrix→FinMatrix {m = zero} M = funExt λ f → ⊥-rec (¬Fin0 f)
FinMatrix→VecMatrix→FinMatrix {m = suc m} {n = zero} M = funExt₂ λ _ f → ⊥-rec (¬Fin0 f)
FinMatrix→VecMatrix→FinMatrix {m = suc m} {n = suc n} M = funExt₂ goal
  where
  goal : (fm : Fin (suc m)) (fn : Fin (suc n)) →
         VecMatrix→FinMatrix (_ ∷ FinMatrix→VecMatrix (λ z → M (suc z))) fm fn ≡ M fm fn
  goal zero zero = refl
  goal zero (suc fn) i = FinVec→Vec→FinVec (λ z → M zero (suc z)) i fn
  goal (suc fm) fn i = FinMatrix→VecMatrix→FinMatrix (λ z → M (suc z)) i fm fn

VecMatrix→FinMatrix→VecMatrix : {A : Type} {m n : ℕ} (M : VecMatrix A m n) → FinMatrix→VecMatrix (VecMatrix→FinMatrix M) ≡ M
VecMatrix→FinMatrix→VecMatrix {m = zero} [] = refl
VecMatrix→FinMatrix→VecMatrix {m = suc m} (M ∷ MS) i = Vec→FinVec→Vec M i ∷ VecMatrix→FinMatrix→VecMatrix MS i

FinMatrixIsoVecMatrix : (A : Type) (m n : ℕ) → Iso (FinMatrix A m n) (VecMatrix A m n)
FinMatrixIsoVecMatrix A m n =
  iso FinMatrix→VecMatrix VecMatrix→FinMatrix VecMatrix→FinMatrix→VecMatrix FinMatrix→VecMatrix→FinMatrix

FinMatrix≃VecMatrix : (A : Type) (m n : ℕ) → FinMatrix A m n ≃ VecMatrix A m n
FinMatrix≃VecMatrix A m n = isoToEquiv (FinMatrixIsoVecMatrix A m n)

FinMatrix≡VecMatrix : (A : Type) (m n : ℕ) → FinMatrix A m n ≡ VecMatrix A m n
FinMatrix≡VecMatrix A m n = ua (FinMatrix≃VecMatrix A m n)




-- Example done using ℕ, but could easily be generalized
addFinMatrix :  {m n : ℕ} → FinMatrix ℕ m n → FinMatrix ℕ m n → FinMatrix ℕ m n
addFinMatrix M N i j = M i j + N i j

addVec : {m : ℕ} → Vec ℕ m → Vec ℕ m → Vec ℕ m
addVec [] [] = []
addVec (x ∷ xs) (y ∷ ys) = x + y ∷ addVec xs ys

addVecMatrix : {m n : ℕ} → VecMatrix ℕ m n → VecMatrix ℕ m n → VecMatrix ℕ m n
addVecMatrix [] [] = []
addVecMatrix (M ∷ MS) (N ∷ NS) = addVec M N ∷ addVecMatrix MS NS


-- TODO: the following computation does not use univalence...

M : FinMatrix ℕ 2 2
M i j = if i == j then 1 else 0

N : FinMatrix ℕ 2 2
N i j = if i == j then 0 else 1

-- This does not typecheck!
-- goal : addFinMatrix M N ≡ (λ _ _ → 1)
-- goal = refl

M' : VecMatrix ℕ 2 2
M' = (1 ∷ 0 ∷ []) ∷ (0 ∷ 1 ∷ []) ∷ []

N' : VecMatrix ℕ 2 2
N' = (0 ∷ 1 ∷ []) ∷ (1 ∷ 0 ∷ []) ∷ []

goal' : addVecMatrix M' N' ≡ (1 ∷ 1 ∷ []) ∷ (1 ∷ 1 ∷ []) ∷ []
goal' = refl

replaceGoal : {A B : Type} {x y : A} → (e : A ≃ B)
              (h : invEq e (equivFun e x) ≡ invEq e (equivFun e y)) → x ≡ y
replaceGoal e h = sym (retEq e _) ∙∙ h ∙∙ retEq e _

_ : addFinMatrix M N ≡ (λ _ _ → 1)
_ = replaceGoal (FinMatrix≃VecMatrix ℕ 2 2) refl



-- Can also transport proofs


addFinMatrixAssoc :  {m n : ℕ} → (M N K : FinMatrix ℕ m n)
                  → addFinMatrix M (addFinMatrix N K) ≡ addFinMatrix (addFinMatrix M N) K
addFinMatrixAssoc M N K i j k = +-assoc (M j k) (N j k) (K j k) i


-- Proving that addVecMatrix is associative is a pain by hand...

-- Proof that FinMatrix→VecMatrix is a group homorphism
FinMatrix→VecMatrixHomAdd : (m n : ℕ) (M N : FinMatrix ℕ m n)
  → FinMatrix→VecMatrix (addFinMatrix M N) ≡
    addVecMatrix (FinMatrix→VecMatrix M) (FinMatrix→VecMatrix N)
FinMatrix→VecMatrixHomAdd zero n M N = refl
FinMatrix→VecMatrixHomAdd (suc m) n M N =
  λ i → lem n (M zero) (N zero) i
      ∷ FinMatrix→VecMatrixHomAdd m n (λ i j → M (suc i) j) (λ i j → N (suc i) j) i
   where
   lem : (n : ℕ) (V W : Fin n → ℕ)
       → FinVec→Vec (λ j → V j + W j) ≡ addVec (FinVec→Vec V) (FinVec→Vec W)
   lem zero V W = refl
   lem (suc n) V W = λ i → V zero + W zero ∷ lem n (λ x → V (suc x)) (λ x → W (suc x)) i



```



