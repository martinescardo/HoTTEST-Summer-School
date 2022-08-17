# Lecture 9

Contents:

- More about homogeneous composition (`hcomp`)
- Cubical univalence (Glue types)
- The structure identity principle (SIP)

```agda
{-# OPTIONS --cubical #-}

module Lecture9-notes where

open import cubical-prelude
open import Lecture7-notes
open import Lecture8-notes hiding (compPath)

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

As we can see here the `hcomp` operation has a very natural geometric
motivation. The following YouTube video might be very helpful to
clarify this: https://www.youtube.com/watch?v=MVtlD22Y8SQ

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

Using this we can define `compPath` much slicker:

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
element corresponding to the interior of an open box:

```agda
hfill' : {A : Type ℓ}
         {φ : I}
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
hfill : {A : Type ℓ}
        {φ : I}
        (u : ∀ i → Partial φ A)
        (u0 : A [ φ ↦ u i0 ])
        (i : I) →
        A
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
course this is assumed as an axiom in Book HoTT. In Cubical Agda it is
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
paths to a base we attach equivalences to a type. One of the original
applications of Glue types was to give computational meaning to
transporting in a line of types constructed by `hcomp` in the universe
`Type`.

For us today the important point is that transporting along the path
constructed using `ua` applies the function underlying the
equivalence. This is easily proved using `transportRefl`:

```agda
uaβ : (e : A ≃ B) (x : A) → transport (ua e) x ≡ pr₁ e x
uaβ e x = transportRefl (equivFun e x)
```

Note that for concrete types this typically holds definitionally, but
for an arbitrary equivalence `e` between abstract types `A` and `B` we
have to prove it.

```agda
uaβℕ : (e : ℕ ≃ ℕ) (x : ℕ) → transport (ua e) x ≡ pr₁ e x
uaβℕ e x = refl
```

The fact that we have both `ua` and `uaβ` suffices to be able to prove
the standard formulation of univalence. For details see
Cubical.Foundations.Univalence in the agda/cubical library.

The standard way of constructing equivalences is to start with an
isomorphism and then improve it into an equivalence. The lemma in the
agda/cubical library that does this is

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

Note that we have already used this in the `winding` function in
Lecture 7.

One can do more fun things with `sucPath`. For example by composing it
with itself `n` times and then transporting we get a new addition
function `_+ℤ'_`. It is direct to prove `isEquiv (λ n → n +ℤ' m)` as
`_+ℤ'_` is defined by `transport`.

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

Combining `subst` and `ua` lets us transport any structure on `A` to
get a structure on an equivalent type `B`:

```agda
substEquiv : (S : Type → Type) (e : A ≃ B) → S A → S B
substEquiv S e = subst S (ua e)
```

In fact this induces an equivalence:

```agda
substEquiv≃ : (S : Type → Type) (e : A ≃ B) → S A ≃ S B
substEquiv≃ S e = (substEquiv S e) , (isEquivTransport (ap S (ua e)))
```

What this says is that any structure on types must be invariant under
equivalence. We can for example take `IsMonoid` for `S` and get that
any two monoid structures on equivalent types `A` and `B` are
themselves equivalent. This is a simple version of the *structure
identity principle* (SIP). There are various more high powered and
generalized versions which also work for *structured* types
(e.g. monoids, groups, etc.) together with their corresponding notions
of *structured* equivalences (e.g. monoid and group isomorphism,
etc.). We will look more at this later, but for now let's look at a
nice example where we can use `substEquiv` to transport functions and
their properties between equivalent types.

When programming and proving properties of programs there are usually
various tradeoffs between different data representations. Very often
one version is suitable for proofs while the other is more suitable
for efficient programming. The standard example of them is unary and
binary numbers. One way to define binary numbers in Agda is as:

```text
data Pos : Type where
  pos1  : Pos
  x0    : Pos → Pos
  x1    : Pos → Pos

data Bin : Type where
  bin0    : Bin
  binPos  : Pos → Bin
```

With some work one can prove that this is equivalent to unary numbers
(see the cubical-prelude for details):

```agda
ℕ≃Bin : ℕ ≃ Bin
ℕ≃Bin  = isoToEquiv (iso ℕ→Bin Bin→ℕ Bin→ℕ→Bin ℕ→Bin→ℕ)
```

We can now use `substEquiv` to transport addition on `ℕ` together with
the fact that it's associative over to `Bin`:

```agda
SemiGroup : Type → Type
SemiGroup X = Σ _+_ ꞉ (X → X → X) , ((x y z : X) → x + (y + z) ≡ (x + y) + z)

SemiGroupBin : SemiGroup Bin
SemiGroupBin = substEquiv SemiGroup ℕ≃Bin (_+_ , +-assoc)

_+Bin_ : Bin → Bin → Bin
_+Bin_  = pr₁ SemiGroupBin

+Bin-assoc : (m n o : Bin) → m +Bin (n +Bin o) ≡ (m +Bin n) +Bin o
+Bin-assoc = pr₂ SemiGroupBin
```

This is nice as it helps us avoid having to repeat work on `Bin` that
we have already done on `ℕ`. This is however not always what we want
as `_+Bin_` is not very efficient as an addition function on binary
numbers. In fact, it will translate its input to unary numbers, add
using unary addition, and then translate back. This is of course very
naive and what we instead want to do is to use efficient addition on
binary numbers, but get the associativity proof for free.

This can be achieved by first defining our fast addition `_+B_ : Bin →
Bin → Bin` and then prove that the map `ℕ→Bin : ℕ → Bin` maps `x + y :
ℕ` to `ℕ→Bin x +B ℕ→Bin y : Bin`.

```
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
```

Having done this it's now straightforward to prove that `_+B_` is
associative using the fact that `_+Bin_` is:

```agda
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
```

This kind of proofs quickly get tedious and it turns out we can
streamline them using a more high prowered version of the SIP.
Indeed, what we really want to do is to characterize the equality of
T-structured types, i.e. we want a proof that two types equipped with
T-structures are equal if there is a T-structure preserving
equivalence between them. In the semigroup example above `T` would
just be the structure of a magma (i.e. a type with a binary operation)
together with magma preserving equivalence so that we can transport
for example the fact that the magma is a semigroup over to the other
magma.

We formalize this and make it more convenient to use using a lot of
automation in the agda/cubical library. This is documented with
various more examples in:

Internalizing Representation Independence with Univalence
Carlo Angiuli, Evan Cavallo, Anders Mörtberg, Max Zeuner
https://dl.acm.org/doi/10.1145/3434293

The binary numbers example with efficient addition is spelled out in
detail in Section 2.1.1 of:

https://www.doi.org/10.1017/S0956796821000034
(Can be downloaded from: https://staff.math.su.se/anders.mortberg/papers/cubicalagda2.pdf)
