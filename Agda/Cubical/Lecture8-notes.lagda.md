WARNING: these notes are currently very much work in progress!

# Lecture 8

Rough plan:

- Cubical Kan operations and path induction (mainly discuss transp,
  but at least mention hcomp, probably also show that we can prove J
  but emphasize that we don't use it very much)

- Set quotients and some examples of programming/proving with them
  (e.g. integers, rationals, polynomials, multisets...)

```agda
{-# OPTIONS --cubical #-}

module Lecture8-notes where

open import cubical-prelude
open import Lecture7-notes
```

# Transport and composition

**TODO:** Maybe move the stuff about contractible singletons here as well?

- Cubical transport
- Subst as a special case of cubical transport
- Path induction from subst
- Homogeneous composition (hcomp)
- Binary composition of paths as special case of hcomp

While path types are great for reasoning about equality they don't let
us transport along paths between types or even compose paths.
Furthermore, as paths are not inductively defined we don't
automatically get an induction principle for them. In order to remedy
this Cubical Agda also has a built-in (generalized) transport
operation and homogeneous composition operation from which the
induction principle (and much more!) is derivable.

The basic operation is called transp and we will soon explain it,
but let's first focus on the special case of cubical transport:

```agda
transport : A ≡ B → A → B
transport p a = transp (λ i → p i) i0 a
```

This is a more primitive operation than "transport" in HoTT as it
only lets us turn a path into a function. However, the transport of
HoTT can easily be proved from cubical transport and in order to
avoid a name clash we call it "subst":

```agda
subst : (B : A → Type ℓ') {x y : A} (p : x ≡ y) → B x → B y
subst B p pa = transport (λ i → B (p i)) pa
```

The transp operation is a generalized transport in the sense that
it lets us specify where the transport is the identity function.
The general type of transp is:

  transp : (A : I → Type ℓ) (r : I) (a : A i0) → A i1

There is an additional side condition which to be satisfied for
Cubical Agda to typecheck "transp A r a". This is that A has to be
"constant" on r. This means that A should be a constant function
whenever r = i1 is satisfied. This side condition is vacuously true
when r = i0, so there is nothing to check when writing transport as
above. However, when r is equal to i1 the transp function will
compute as the identity function.

  transp A i1 a = a

Having this extra generality is useful for quite technical reasons,
for instance we can easily relate a with its transport over p:

```agda
transportFill : (p : A ≡ B) (a : A) → PathP (λ i → p i) a (transport p a)
transportFill p a i = transp (λ j → p (i ∧ j)) (~ i) a
```

Another result that follows easily from transp is that transporting
in a constant family is the identity function (up to a path). Note
that this is *not* proved by refl. This is maybe not surprising as
transport is not defined by pattern-matching on p.

```agda
transportRefl : (x : A) → transport refl x ≡ x
transportRefl {A = A} x i = transp (λ _ → A) i x
```

Having transp lets us prove many more useful lemmas like this. For
details see:

  Cubical.Foundations.Transport



We can also define the J eliminator (a.k.a. path induction)

```agda
J : {x : A} (P : (z : A) → x ≡ z → Type ℓ'')
    (d : P x refl) {y : A} (p : x ≡ y) → P y p
J {x = x} P d p = subst (λ X → P (pr₁ X) (pr₂ X)) (isContrSingl x .pr₂ (_ , p)) d
```

Unfolded version:

transport (λ i → P (p i) (λ j → p (i ∧ j))) d

So J is provable, but it doesn't satisfy the computation rule of refl
definitionally as _≡_ is not inductively defined. See exercises for
how to prove it. Not having this hold definitionally is almost never a
problem in practice as the cubical primitives satisfy many new
definitional equalities (c.f. ap).

As we now have J we can define path concatenation and many more
things, however this is not the way to do things in Cubical Agda. One
of the key features of cubical type theory is that the transp
primitive reduces differently for different types formers (see CCHM or
the Cubical Agda paper for details). For paths it reduces to another
primitive operation called hcomp. This primitive is much better suited
for concatenating paths than J as it is much more general. In
particular, it lets us compose multiple higher dimensional cubes
directly. We will explain it by example.

In order to compose two paths we write:

```agda
compPath : {x y z : A} → x ≡ y → y ≡ z → x ≡ z
compPath {x = x} p q i = hcomp (λ j → λ { (i = i0) → x
                                        ; (i = i1) → q j })
                               (p i)
```

This is best understood with the following drawing:

    x             z
    ^             ^
    ¦             ¦
  x ¦             ¦ q j
    ¦             ¦
    x ----------> y
          p i

In the drawing the direction i goes left-to-right and j goes
bottom-to-top. As we are constructing a path from x to z along i we
have i : I in the context already and we put p i as bottom. The
direction j that we are doing the composition in is abstracted in
the first argument to hcomp.

These are related to lifting conditions for Kan cubical sets.

A more natural form of composition of paths in Cubical Agda is
ternary composition:

         x             w
         ^             ^
         ¦             ¦
 p (~ j) ¦             ¦ r j
         ¦             ¦
         y ----------> z
               q i

This is written p ∙∙ q ∙∙ r in the agda/cubical library (∙ is "\.")
and implemented by:

```agda
_∙∙_∙∙_ : {x y z w : A} → x ≡ y → y ≡ z → z ≡ w → x ≡ w
(p ∙∙ q ∙∙ r) i = hcomp (λ j → λ { (i = i0) → p (~ j)
                                 ; (i = i1) → r j })
                        (q i)
```

Note that we can easily define mixfix operators with many arguments
in Agda.

Using this we can define compPath much slicker:

_∙_ : {x y z : A} → x ≡ y → y ≡ z → x ≡ z
p ∙ q = refl ∙∙ p ∙∙ q

To prove algebraic properties of this operation (in particular that
it's a groupoid) we need to talk about filling using the hfill
operation. There is no time for this today, but the interested
reader can consult

   Cubical.Foundations.GroupoidLaws

Having hcomp as a primitive operation lets us prove many things
very directly. For instance, we can prove that any proposition is
also a set using a higher dimensional hcomp.

```agda
isProp→isSet : isProp A → isSet A
isProp→isSet h a b p q j i =
  hcomp (λ k → λ { (i = i0) → h a a k
                 ; (i = i1) → h a b k
                 ; (j = i0) → h a (p i) k
                 ; (j = i1) → h a (q i) k }) a
```

Geometric picture: start with a square with a everywhere as base,
then change its sides so that they connect p with q over refl_a and
refl_b.

```agda
isPropIsProp : isProp (isProp A)
isPropIsProp f g i a b = isProp→isSet f a b (f a b) (g a b) i

isPropIsSet : isProp (isSet A)
isPropIsSet h1 h2 i x y = isPropIsProp (h1 x y) (h2 x y) i
```

In order to understand what the second argument to hcomp is one
should read about partial elements. We refer the interested reader
to the Cubical Agda documentation:

https://agda.readthedocs.io/en/v2.6.1.3/language/cubical.html#partial-elements

However, for beginners one doesn't need to write hcomp to prove
thing as the library provide many basic lemmas. In particular, the
library provides equational reasoning combinators as in regular
Agda which let us write things like:

inverseUniqueness : (r : R) → isProp (Σ[ r' ∈ R ] r · r' ≡ 1r)
inverseUniqueness r (r' , rr'≡1) (r'' , rr''≡1) = Σ≡Prop (λ _ → is-set _ _) path
 where
 path : r' ≡ r''
 path = r'             ≡⟨ sym (·Rid _) ⟩
        r' · 1r        ≡⟨ ap (r' ·_) (sym rr''≡1) ⟩
        r' · (r · r'') ≡⟨ ·Assoc _ _ _ ⟩
        (r' · r) · r'' ≡⟨ ap (_· r'') (·-comm _ _) ⟩
        (r · r') · r'' ≡⟨ ap (_· r'') rr'≡1 ⟩
        1r · r''       ≡⟨ ·Lid _ ⟩
        r''            ∎

