# Lecture 7: Cubical Agda

Contents:

- The interval and Path/PathP types
- Cubical higher inductive types

## Some introductory pointers for further reading

Documentation of the Cubical Agda mode can be found
[here](https://agda.readthedocs.io/en/v2.6.2.2/language/cubical.html).

These lectures about Cubical Agda will be inspired by my material from
the [2020 EPIT school on HoTT](https://github.com/HoTT/EPIT-2020/tree/main/04-cubical-type-theory).

For students interested in a more in depth introduction to cubical
type theory see [my lecture notes for the 2019 HoTT school](https://www.cambridge.org/core/journals/mathematical-structures-in-computer-science/article/cubical-methods-in-homotopy-type-theory-and-univalent-foundations/ECB3FE6B4A0B19AED2D3A2D785C38AF9).
Those notes contain a lot more background and motivation to cubical
methods in HoTT and an extensive list of references for those that
want to read more background material.

If one wants a library to work with when doing Cubical Agda there is
the [agda/cubical](https://github.com/agda/cubical/) library that I
started developing with Andrea Vezzosi (the implementor of Cubical
Agda) in 2018 and which has now over 70 contributors. It contains a
variety of things, including data structures, algebra, synthetic
homotopy and cohomology theory, etc..

For a slower-paced introduction to mathematics in Cubical Agda, there
is the more recent [1lab](https://1lab.dev/). Although meant to be
read on the web, it also doubles as a community-maintained library of
formalized mathematics, most notably category theory.

# Cubical Agda

To make Agda cubical simply add the following option:

```agda
{-# OPTIONS --cubical #-}

module Lecture7-notes where
```

We also have a small cubical prelude which sets things up to work
nicely and which provides whatever we might need for the lectures.

```agda
open import cubical-prelude
```

The key idea in cubical type theories like Cubical Agda is to not have
equality be inductively defined as in Book HoTT, but rather we assume
that there is a primitive interval and define equality literally as
paths, i.e. as functions out of the interval. By iterating these paths
we get squares, cubes, hypercubes, ..., making the type theory
inherently cubical.

# The interval and path types

The interval is a primitive concept in Cubical Agda. It's written `I`.
It has two endpoints:

```text
  i0 : I
  i1 : I
```

These stand for "interval 0" and "interval 1".

We can apply a function out of the interval to an endpoint just
like we would with any Agda function:

```agda
apply0 : (A : Type ℓ) (p : I → A) → A
apply0 A p = p i0
```

The equality type `_≡_` is not inductively defined in Cubical Agda,
instead it's a builtin primitive notion defined using the interval. An
element of `x ≡ y` consists of a function `p : I → A` such that `p i0`
is definitionally `x` and `p i1` is definitionally `y`. The check that
the endpoints are correct when we provide a `p : I → A` is
automatically performed by Agda during typechecking, so introducing an
element of `x ≡ y` is done just like how we introduce elements of
`I → A` but Agda will check the side conditions.

We can hence write paths using λ-abstraction:

```agda
mypath : {A : Type ℓ} (x : A) → x ≡ x
mypath x = λ i → x
```

As explained above Agda checks that whatever we written as definition
matches the path that we have provided (so the endpoints have to be
correct). In this case everything is fine and mypath can be thought of
as a proof reflexivity. Let's give it a nicer name and more implicit
arguments:

```agda
refl : {A : Type ℓ} {x : A} → x ≡ x
refl {x = x} = λ i → x
```

The notation `{x = x}` lets us access the implicit argument `x` (the
`x` in the LHS of `x = x`) and rename it to `x` (the `x` in the RHS
`x = x`) in the body of `refl`. We could just as well have written:

```text
refl : {A : Type ℓ} {x : A} → x ≡ x
refl {x = y} = λ i → y
```

Note that we cannot pattern-match on interval variables as `I` is not
inductively defined. Try uncommenting and typing `C-c C-c` in the hole:

```text
oops : {A : Type} → I → A
oops r = {!r!}
```

It quickly gets tiring to write `{A : Type ℓ}` everywhere, so let's
assume that we have some types (in fact, we've already assumed that
`ℓ` is a `Level` in the cubical-prelude):

```agda
private
  variable
    A B : Type ℓ
```

This will make `A` and `B` elements of different universes (all
arguments is maximally generalized) and all definitions that use them
will have them as implicit arguments.

We can now implement some basic operations on `_≡_`. Let's start with
`ap`:

```agda
ap : (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
ap f p i = f (p i)
```

Note that the definition differs from the Book HoTT definition in that
it is not defined by path induction or pattern-matching on `p`, but
rather it's just a direct definition as a composition of functions.
Agda treats `p : x ≡ y` like any function, so we can apply it to `i`
to get an element of `A` which at `i0` is `x` and at `i1` is `y`. By
applying `f` to this element we hence get an element of `B` which at
`i0` is `f x` and at `i1` is `f y`.

As this is just function composition it satisfies lots of nice
definitional equalities, see the exercises. Some of these are not
satisfied by the Book HoTT definition of `ap`.

In Book HoTT function extensionality is proved as a consequence of
univalence using a rather ingenious proof due to Voevodsky, but in
cubical systems it has a much more direct proof. As paths are just
functions we can get it by swapping the arguments to `p`:

```agda
funExt : {f g : A → B} (p : (x : A) → f x ≡ g x) → f ≡ g
funExt p i x = p x i
```

To see that this has the correct type, note that when `i` is `i0` we
have `p x i0 = f x` and when `i` is `i1` we have `p x i1 = g x`, so by
η for function types we have a path `f ≡ g` as desired.

The interval has additional operations:

```text
Minimum:     _∧_ : I → I → I             (corresponds to min(i,j))
Maximum:     _∨_ : I → I → I             (corresponds to max(i,j))
Symmetry:     ~_ : I → I                 (corresponds to 1 - i)
```

These satisfy the equations of a De Morgan algebra (i.e. a
distributive lattice (_∧_ , _∨_ , i0 , i1) with an "De Morgan"
involution ~). This just means that we have the following kinds of
equations definitionally:

```text
i0 ∨ i    = i
i  ∨ i1   = i1
i  ∨ j    = j ∨ i
i0 ∧ i    = i0
i1 ∧ i    = i
i  ∧ j    = j ∧ i
~ (~ i)   = i
i0        = ~ i1
~ (i ∨ j) = ~ i ∧ ~ j
~ (i ∧ j) = ~ i ∨ ~ j
```

However, we do not have `i ∨ ~ i = i1` and `i ∧ ~ i = i0`. The reason
is that I represents an abstract interval, so we if we think of it as
the real interval [0,1] ⊂ ℝ we clearly don't always have
"max(i,1-i) = 1" or "min(i,1-i) = 0)" for all i ∈ [0,1].

These operations on `I` are very useful as they let us define even
more things directly. For example symmetry of paths is easily defined
using `~_`.

```agda
sym : {x y : A} → x ≡ y → y ≡ x
sym p i = p (~ i)
```

Remark: this has been called `⁻¹` and `!` in the previous
lectures. Here we stick to `sym` for the cubical version following the
agda/cubical notation.

The operations `_∧_` and `_∨_` are called *connections* and let us
build higher dimensional cubes from lower dimensional ones, for
example if we have a path `p : x ≡ y` then

```text
  sq i j = p (i ∧ j)
```

is a square (as we've parametrized by `i` and `j`) with the following
boundary:

```text
   sq i0 j = p (i0 ∧ j) = p i0 = x
   sq i1 j = p (i1 ∧ j) = p j
   sq i i0 = p (i ∧ i0) = p i0 = x
   sq i i1 = p (i ∧ i1) = p i
```

If we draw this we get:

```text
             p
       x --------> y
       ^           ^
       ¦           ¦
  refl ¦     sq    ¦ p
       ¦           ¦
       ¦           ¦
       x --------> x
           refl
```

Being able to make this square directly is very useful. It for
example let's prove that singletons are contractible (a.k.a. based
path induction).

We define the type of singletons as follows

```agda
singl : {A : Type ℓ} (a : A) → Type ℓ
singl {A = A} a = Σ x ꞉ A , a ≡ x
```

To show that this type is contractible we need to provide a center
of contraction and the fact that any element of it is path-equal to
the center

```agda
isContrSingl : (x : A) → isContr (singl x)
isContrSingl x = ctr , prf
  where
  -- The center is just a pair with x and refl
  ctr : singl x
  ctr = x , refl

  -- We then need to prove that ctr is equal to any element s : singl x.
  -- This is an equality in a Σ-type, so the first component is a path
  -- and the second is a path over the path we pick as first argument,
  -- i.e. the second component is a square. In fact, we need a square
  -- relating refl and pax over a path between refl and pax, so we can
  -- use an _∧_ connection.
  prf : (s : singl x) → ctr ≡ s
  prf (y , pax) i = (pax i) , λ j → pax (i ∧ j)
```

As we saw in the second component of prf we often need squares when
proving things. In fact, `pax (i ∧ j)` is a path relating `refl` to
`pax` *over* another path `λ j → x ≡ pax j`. This notion of path over
a path is very useful when working in Book HoTT as we've seen in the
previous lectures, this is also the case when working cubically. In
Cubical Agda path-overs are a primitive notion called `PathP` ("Path
over a Path"). In general `PathP A x y` has

```text
   A : I → Type ℓ
   x : A i0
   y : A i1
```

So PathP lets us natively define heteorgeneous paths, i.e. paths
where the endpoints are in different types. This allows us to
specify the type of the second component of `prf`:

```agda
prf' : (x : A) (s : singl x) → (x , refl) ≡ s
prf' x (y , pax) i = (pax i) , λ j → goal i j
  where
  goal : PathP (λ j → x ≡ pax j) refl pax
  goal i j = pax (i ∧ j)
```

Just like `_×_` is a special case of Σ-types we have that `_≡_` is a
special case of PathP. In fact, `x ≡ y` is just short for
`PathP (λ _ → A) x y`:

```agda
reflP : {x : A} → PathP (λ _ → A) x x
reflP = refl
```

Working directly with paths and equalities makes many proofs from Book
HoTT very short:

```agda
isContrΠ : {B : A → Type ℓ} (h : (x : A) → isContr (B x))
         → isContr ((x : A) → B x)
isContrΠ h = (λ x → pr₁ (h x)) , (λ f i x → pr₂ (h x) (f x) i)
```

# Cubical higher inductive types

We have seen various HITs earlier in the course. These were added
axiomatically to Agda by postulating their existence together with
suitable elimination/induction principles. In Cubical Agda they are
instead added just like any inductive data type, but with path
constructors. This is made possible by the fact that paths in Cubical
Agda are just fancy functions.

## The circle

We can define the circle as the following simple data declaration:

```agda
data S¹ : Type₀ where
  base : S¹
  loop : base ≡ base
```

We can write functions on `S¹` using pattern-matching:

```agda
double : S¹ → S¹
double base = base
double (loop i) = (loop ∙ loop) i
```

Note that loop takes an `i : I` argument. This is not very surprising
as it's a path of type `base ≡ base`, but it's an important difference
to Book HoTT where we instead would have to state the equation using
`ap`. Having the native notion of equality be heterogeneous makes it
possible to quite directly define a general schema for a large class
of HITs and use it in the implementation of a system like Cubical Agda.

Let's use univalence to compute some winding numbers on the
circle. We first define a family of types over the circle with
fibers being the integers.

```agda
helix : S¹ → Type₀
helix base     = ℤ
helix (loop i) = sucPath i
```

Here univalence is baked into `sucPath : ℤ ≡ ℤ`. The loopspace of the
circle is then defined as

```agda
ΩS¹ : Type₀
ΩS¹ = base ≡ base
```

and we can then define a function computing how many times we've
looped around the circle by:

```agda
winding : ΩS¹ → ℤ
winding p = transp (λ i → helix (p i)) i0 (pos 0)
```

Here `transp` is a cubical transport function. We'll talk about it in
more detail in the next lecture, but for now we can observe that it
reduces as expected:

```agda
_ : winding (λ i → double ((loop ∙ loop) i)) ≡ pos 4
_ = refl
```

This would not reduce definitionally in Book HoTT as univalence is an
axiom. Having things compute definitionally makes it possible to
substantially simplify many proofs from Book HoTT in Cubical Agda.

We can in fact prove that `winding` is an equivalence, this is very
similar to the Book HoTT proof and uses the encode-decode method. For
details about how this proof looks in Cubical Agda see the
Cubical.HITs.S1.Base file in the agda/cubical library.

## The torus

We can define the torus as:

```agda
data Torus : Type₀ where
  point : Torus
  line1 : point ≡ point
  line2 : point ≡ point
  square : PathP (λ i → line1 i ≡ line1 i) line2 line2
```

The square corresponds to the usual folding diagram from topology
(where `p` is short for `point`):

```text
             line1
        p ----------> p
        ^             ^
        ¦             ¦
  line2 ¦             ¦ line2
        ¦             ¦
        p ----------> p
             line1
```

Proving that it is equivalent to two circles is pretty much trivial as
we have definitional computation rules for all constructors, including
higher ones:

```agda
t2c : Torus → S¹ × S¹
t2c point        = (base , base)
t2c (line1 i)    = (loop i , base)
t2c (line2 j)    = (base , loop j)
t2c (square i j) = (loop i , loop j)

c2t : S¹ × S¹ → Torus
c2t (base   , base)   = point
c2t (loop i , base)   = line1 i
c2t (base   , loop j) = line2 j
c2t (loop i , loop j) = square i j

c2t-t2c : (t : Torus) → c2t (t2c t) ≡ t
c2t-t2c point        = refl
c2t-t2c (line1 _)    = refl
c2t-t2c (line2 _)    = refl
c2t-t2c (square _ _) = refl

t2c-c2t : (p : S¹ × S¹) → t2c (c2t p) ≡ p
t2c-c2t (base   , base)   = refl
t2c-c2t (base   , loop _) = refl
t2c-c2t (loop _ , base)   = refl
t2c-c2t (loop _ , loop _) = refl
```

Using univalence we get the following equality:

```agda
Torus≡S¹×S¹ : Torus ≡ S¹ × S¹
Torus≡S¹×S¹ = isoToPath (iso t2c c2t t2c-c2t c2t-t2c)
```

We can also directly compute winding numbers on the torus

```agda
windingTorus : point ≡ point → ℤ × ℤ
windingTorus l = ( winding (λ i → pr₁ (t2c (l i)))
                 , winding (λ i → pr₂ (t2c (l i))))

_ : windingTorus (line1 ∙ sym line2) ≡ (pos 1 , negsuc 0)
_ = refl
```

# Bonus content if there is time

## Interval

```agda
data Interval : Type₀ where
  zero : Interval
  one  : Interval
  seg  : zero ≡ one
```

## Suspension

```agda
data Susp (A : Type ℓ) : Type ℓ where
  north : Susp A
  south : Susp A
  merid : (a : A) → north ≡ south
```

We can define Dan's Circle2 as the suspension of Bool, or we can do it directly as:

```agda
data Circle2 : Type₀ where
  north : Circle2
  south : Circle2
  west  : north ≡ south
  east  : north ≡ south
```

## Pushouts

```agda
data Pushout {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
             (f : A → B) (g : A → C) : Type (ℓ ⊔ ℓ' ⊔ ℓ'') where
  inl : B → Pushout f g
  inr : C → Pushout f g
  push : (a : A) → inl (f a) ≡ inr (g a)
```

## Relation quotient

```agda
data _/ₜ_ {ℓ ℓ'} (A : Type ℓ) (R : A → A → Type ℓ') : Type (ℓ ⊔ ℓ') where
  [_] : (a : A) → A /ₜ R
  eq/ : (a b : A) → (r : R a b) → [ a ] ≡ [ b ]
```

## Propositional truncation

```agda
data ∥_∥₋₁ {ℓ} (A : Type ℓ) : Type ℓ where
  ∣_∣₋₁ : A → ∥ A ∥₋₁
  squash₁ : (x y : ∥ A ∥₋₁) → x ≡ y
```
