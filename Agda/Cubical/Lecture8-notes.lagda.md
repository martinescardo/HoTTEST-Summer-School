# Lecture 8

Contents:

- Set quotients
- Cubical transport and path induction
- Homogeneous composition (`hcomp`)

```agda
{-# OPTIONS --cubical #-}

module Lecture8-notes where

open import cubical-prelude
open import Lecture7-notes

private
  variable
    A B : Type ℓ
```

## Set quotients

Last time we saw some HITs that are useful for topology and homotopy
theory. Now we'll look at some HITs that are not very interesting from
a homotopical perspective, but still very useful for other purposes.
In particular we will look at how we can construct quotient types and
in order for the result to be a set we will also set truncate the
type. This kind of types has many applications in both computer
science and mathematics.

In general these are written as:

```text
data _/_ (A : Type ℓ) (R : A → A → Type ℓ') : Type (ℓ ⊔ ℓ') where
  [_] : A → A / R
  eq/ : (a b : A) → R a b → [ a ] ≡ [ b ]
  trunc : (a b : A / R) (p q : a ≡ b) → p ≡ q
```

The type of the `trunc` constructor can simply be written as:

```agda
data _/_ (A : Type ℓ) (R : A → A → Type ℓ') : Type (ℓ ⊔ ℓ') where
  [_] : A → A / R
  eq/ : (a b : A) → R a b → [ a ] ≡ [ b ]
  trunc : isSet (A / R)
```

The idea is that `[_]` injects elements of `A` into the quotient while
`eq/` ensures that elements that are related by `R` are sent to equal
elements. Finally we have to truncate the type to be a set in order
for this to be a set quotient. If we leave out the `trunc` constructor
quite weird things can happen, for example if one quotients the unit
type by the total relation then one obtains a type which is equivalent
to the circle! The `trunc` constructor is hence crucial to ensure that
the result is a set **even** if `A` is one already (so quotienting can
raise the truncation level).

Various sources require that `R` is proposition-valued, i.e. `R : A →
A → hProp`. However this is not necessary to define `_/_` as seen
above. There are however various important properties that are only
satisfied when one quotients by a prop-valued relation. The key
example being effectivity, i.e. that

```text
(a b : A) → [ a ] ≡ [ b ] → R a b
```

To prove this one first of all needs that `R` is prop-valued and the
proof then uses univalence for propositions (i.e., logically
equivalent propositions are equal, a.k.a. "propositional
extensionality").

Having the ability to define set quotients using `_/_` lets us do many
examples from mathematics and computer science. For example we can
define the integers as:

```agda
ℤ' : Type
ℤ' = (ℕ × ℕ) / rel
  where
  rel : ℕ × ℕ → ℕ × ℕ → Type
  rel (x₀ , y₀) (x₁ , y₁) = x₀ + y₁ ≡ x₁ + y₀
```

If you haven't seen this construction before see
https://en.wikipedia.org/wiki/Integer#Construction

Exercises: define `0`, `1`, `+`, `-`, `*`

Similarly we can define the rational numbers as a quotient of pairs of
a number and a nonzero number (and more generally we can define the
field of fractions of a commutative ring R using `_/_`). Both the
integers and rationals can of course be defined without using
quotients in type theory, but in the case of the rationals this has
some efficiency problems. Indeed, when defining the rationals not as a
quotient we need to do it as normalized fractions, that is, pairs of
coprime numbers. All operations, like addition and multiplication,
then have to ensure that the resulting fractions are normalized which
can become quite inefficient because of repeated GCD computations. A
more efficient way is to work with the equivalence classes of
not-necessarily-normalized fractions and then normalize whenever one
wants to. This can be done when defining the rationals using `_/_`.

Let us now look at a more computer science inspired example: finite
multisets. These can be represented as lists modulo permutations.
Defining these using `_/_` is a bit annoying, luckily there is an
easier way:

```agda
infixr 5 _∷_

data FMSet (A : Type ℓ) : Type ℓ where
  [] : FMSet A
  _∷_ : (x : A) → (xs : FMSet A) → FMSet A
  comm : (x y : A) (xs : FMSet A) → x ∷ y ∷ xs ≡ y ∷ x ∷ xs
  trunc : (xs ys : FMSet A) (p q : xs ≡ ys) → p ≡ q
```

Programming and proving with this is quite straightforward:

```agda
infixr 30 _++_

_++_ : (xs ys : FMSet A) → FMSet A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ xs ++ ys
comm x y xs i ++ ys = comm x y (xs ++ ys) i
trunc xs zs p q i j ++ ys =
  trunc (xs ++ ys) (zs ++ ys) (λ k → p k ++ ys) (λ k → q k ++ ys) i j

unitl-++ : (xs : FMSet A) → [] ++ xs ≡ xs
unitl-++ xs = refl

unitr-++ : (xs : FMSet A) → xs ++ [] ≡ xs
unitr-++ [] = refl
unitr-++ (x ∷ xs) = ap (x ∷_) (unitr-++ xs)
unitr-++ (comm x y xs i) j = comm x y (unitr-++ xs j) i
unitr-++ (trunc xs ys p q i j) k =
  trunc (unitr-++ xs k) (unitr-++ ys k)
        (λ l → unitr-++ (p l) k) (λ l → unitr-++ (q l) k) i j
```

Filling the goals for `comm` and `trunc` quickly gets tiresome and
when working with HITs like this it's very strongly recommended to
prove special lemmas for eliminating into propositions (which is the
case above as `FMSet` is a set, so its `≡`-type is a proposition). If
we do this the proof of `unitr-++` can be simplified to a one-liner:

```text
unitr-++ : (xs : FMSet A) → xs ++ [] ≡ xs
unitr-++ = ElimProp.f (trunc _ _) refl (λ x p → cong (_∷_ x) p)
```

We recommend the interested reader to look at the code in
Cubical.HITs.FiniteMultiset.Base and
Cubical.HITs.FiniteMultiset.Properties in agda/cubical to see how
these lemmas are stated and proved. This is a very common pattern when
working with set truncated HITs: first define the HIT, then prove
special purpose recursors and eliminators for eliminating into types
of different truncation levels. All definitions are then written using
these recursors and eliminators and one get very short proofs.

A more efficient version of finite multisets based on association
lists can be found in Cubical.HITs.AssocList.Base. It looks like this:

```agda
data AssocList (A : Type ℓ) : Type ℓ where
  ⟨⟩ : AssocList A
  ⟨_,_⟩∷_ : (a : A) (n : ℕ) (xs : AssocList A) → AssocList A
  per : (a b : A) (m n : ℕ) (xs : AssocList A)
      → ⟨ a , m ⟩∷ ⟨ b , n ⟩∷ xs ≡ ⟨ b , n ⟩∷ ⟨ a , m ⟩∷ xs
  agg : (a : A) (m n : ℕ) (xs : AssocList A)
      → ⟨ a , m ⟩∷ ⟨ a , n ⟩∷ xs ≡ ⟨ a , m + n ⟩∷ xs
  del : (a : A) (xs : AssocList A) → ⟨ a , 0 ⟩∷ xs ≡ xs
  trunc : (xs ys : AssocList A) (p q : xs ≡ ys) → p ≡ q
```

Programming and proving is more complicated with `AssocList` compared
to `FMSet`. This kind of example occurs a lot in programming and
mathematics: one representation is easier to work with, but not
efficient, while another is efficient but difficult to work with.
Next time we will see how we can use univalence and the structure
identity principle (SIP) to get the best of both worlds (if someone
can't wait they can look at https://dl.acm.org/doi/10.1145/3434293 for
more details).

It's sometimes easier to work directly with `_/_` instead of defining
special HITs as one can reuse lemmas for `_/_` instead of reproving
things. For example, general lemmas about eliminating into
propositions have already been proved for `_/_` so we do not have to
reprove them for our special purpose HIT. However on the other hand it
can sometimes be much easier to write the HIT directly (imagine
implementing `AssocList` using `_/_`...) and one also gets the benefit
that one can pattern-match directly with nice names for the
constructors (it might still be better to use the handcrafted
recursor/eliminator for the HIT to avoid having to give cases for path
construtors though).

## Cubical transport and path induction

While path types are great for reasoning about equality they don't let
us transport along paths between types or even compose paths.
Furthermore, as paths are not inductively defined we don't
automatically get an induction principle for them. In order to remedy
this Cubical Agda also has a built-in cubical transport operation and
homogeneous composition operation from which the induction principle
is derivable (and much more!).

The basic operation is called `transp` and we will soon explain it,
but let's first focus on the special case of cubical transport which
we used to define `winding` last time:

```agda
transport : A ≡ B → A → B
transport p a = transp (λ i → p i) i0 a
```

This is a more primitive operation than "transport" in Book HoTT as it
only lets us turn a path into a function. However, the transport of
HoTT can easily be proved from cubical transport and in order to avoid
a name clash we call it "subst":

```agda
subst : (B : A → Type ℓ') {x y : A} (p : x ≡ y) → B x → B y
subst B p pa = transport (λ i → B (p i)) pa
```

The `transp` operation is a generalized transport in the sense that it
lets us specify where the transport is the identity function (this is
why there is an `i0` in the definition of `transport` above). The
general type of `transp` is:

```text
transp : (A : I → Type ℓ) (r : I) (a : A i0) → A i1
```

There is an additional side condition which has to be satisfied for
Cubical Agda to typecheck `transp A r a`. This is that `A` has to be
"constant" on `r`. This means that `A` should be a constant function
whenever `r = i1` is satisfied. This side condition is vacuously true
when `r = i0`, so there is nothing to check when writing transport as
above. However, when `r` is equal to `i1` the `transp` function will
compute as the identity function.

```text
transp A i1 a == a
```

(Here `==` is definitional/judgmental equality)

Having this extra generality is useful for quite technical reasons,
for instance we can easily relate a term `a` with its transport over a
path `p`:

```agda
transportFill : (p : A ≡ B) (a : A) → PathP (λ i → p i) a (transport p a)
transportFill p a i = transp (λ j → p (i ∧ j)) (~ i) a
```

Another result that follows easily from `transp` is that transporting
in a constant family is the identity function (up to a path). Note
that this is *not* proved by `refl`. This is maybe not so surprising
as `transport` is not defined by pattern-matching on `p`.

```agda
transportRefl : (x : A) → transport refl x ≡ x
transportRefl {A = A} x i = transp (λ _ → A) i x
```

Having `transp` lets us prove many more useful lemmas like this. For
details see Cubical.Foundations.Transport in the agda/cubical library.

Using contractibility of singletons we can also define the `J`
eliminator for paths (a.k.a. path induction):

```agda
J : {x : A} (P : (y : A) → x ≡ y → Type ℓ'')
    (d : P x refl) {y : A} (p : x ≡ y) → P y p
J {x = x} P d p = subst (λ X → P (pr₁ X) (pr₂ X)) (isContrSingl x .pr₂ (_ , p)) d
```

Unfolded version:

```text
transport (λ i → P (p i) (λ j → p (i ∧ j))) d
```

So `J` is provable, but it doesn't satisfy the computation rule of
`refl` definitionally as `_≡_` is not inductively defined. See
exercises for how to prove it. Not having this hold definitionally is
almost never a problem in practice as the cubical primitives satisfy
many new definitional equalities (c.f. `ap`).

## Homogeneous composition (`hcomp`)

As we now have `J` we can define path concatenation and many more
things, however this is not the way to do things in Cubical Agda. One
of the key features of cubical type theory is that the `transp`
primitive reduces differently for different types formers (see CCHM
[1] or the Cubical Agda paper [2] for details). For paths it reduces
to another primitive operation called `hcomp`. This primitive is much
better suited for concatenating paths than `J` as it is much more
general. In particular, it lets us compose multiple higher dimensional
cubes directly. We will explain it by example.

In order to compose two paths we write:

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

To prove algebraic properties of this operation (in particular that
it's a groupoid) we need to talk about filling using the `hfill`
operation. There is no time for this today, but the interested reader
can consult Cubical.Foundations.GroupoidLaws and the documentation for
`hcomp`:
https://agda.readthedocs.io/en/v2.6.2.2/language/cubical.html#homogeneous-composition. The
following YouTube video might also be very helpful
https://www.youtube.com/watch?v=MVtlD22Y8SQ

Having `hcomp` as a primitive operation lets us prove many things very
directly. For instance, we can prove that any proposition is also a
set using a higher dimensional hcomp.

```agda
isProp→isSet : isProp A → isSet A
isProp→isSet h a b p q j i =
  hcomp (λ k → λ { (i = i0) → h a a k
                 ; (i = i1) → h a b k
                 ; (j = i0) → h a (p i) k
                 ; (j = i1) → h a (q i) k }) a
```

Geometric picture: start with a square with `a` everywhere as base,
then change its sides so that they connect `p` with `q` over `refl a`
and `refl b`.

This has some useful consequences:

```agda
isPropIsProp : isProp (isProp A)
isPropIsProp f g i a b = isProp→isSet f a b (f a b) (g a b) i

isPropIsSet : isProp (isSet A)
isPropIsSet h1 h2 i x y = isPropIsProp (h1 x y) (h2 x y) i
```

In order to really understand what the second argument to `hcomp` is
and how to use `hfill` one should read about partial elements and
cubical subtypes. We refer the interested reader to the Cubical Agda
documentation:

https://agda.readthedocs.io/en/v2.6.2.2/language/cubical.html#partial-elements

However, beginners often doesn't have to write `hcomp` to prove things
as the library provides many basic lemmas. This is especially true
when reasoning about sets. However, when reasoning about types that
have higher truncation level it's very convenient to be able to
construct squares and cubes directly and being able to use `hcomp` is
quite necessary (see exercise 12 on
[Exercises7](https://github.com/martinescardo/HoTTEST-Summer-School/blob/main/Agda/Cubical/Exercises7.lagda.md)).

References
==========

[1] https://arxiv.org/abs/1611.02108
[2] https://staff.math.su.se/anders.mortberg/papers/cubicalagda2.pdf
