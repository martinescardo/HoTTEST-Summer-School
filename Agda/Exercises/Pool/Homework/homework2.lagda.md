# Week 2 - Homework Sheet

Please complete Part II of this week's Lab Sheet before moving on to these exercises.

## Section 1: Identity Type

```agda
{-# OPTIONS --without-K --safe #-}

module Pool.Homework.homework2 where

open import prelude hiding (id ; _∘_)
```

### Exercise 1.1

Recall the definitions in `trans`, `sym` and especially `ap` from the
[introduction](../introduction.lagda.md).

We could define "double `ap`" like so:

```agda
ap² : {A : Type} (f : A → A) {x y : A} → x ≡ y → f (f x) ≡ f (f y)
ap² f e = {!!}
```

For example, this would help us prove the following without pattern matching:

```agda
double-not-eq : {a b : Bool} → a ≡ b → not (not a) ≡ not (not b)
double-not-eq e = ap² not e
```

**Define** "double `ap`" *without* using pattern matching.

### Exercise 1.2

We have seen that `ap` allows us to "transport" an equality along a function.

We will now see how we can "transport" equalities along types; in our example,
we use the type for Vectors.

```agda
transport-vec-A : {A : Type} {n m : ℕ} → n ≡ m
                → Vector A n → Vector A m
transport-vec-A e v = {!!}
```

**Complete** the above function.

## Section 2: Laws for `map`

Recall that we defined `map` as follows:
```agda
map : {A B : Type} → (A → B) → List A → List B
map f []        = []
map f (x :: xs) = f x :: map f xs
```

In Haskell, `map` is supposed to satisfy, for every list `xs`, two laws:

 1. `map id xs = xs` (where `id` the identity function);
 1. `map (g . f) xs = map g (map f xs)` (where `.` is function composition).

But checking these laws is left to a pen-and-paper check by the programmer.

In Agda, we can both *state* and *prove* these laws.

We first define function composition and the identity function.

```agda
id : {A : Type} → A → A
id = λ x → x

_∘_ : {A B C : Type} → (g : B → C) → (f : A → B)→ A → C
g ∘ f = λ x → g (f x)
```

Tip: Use `\comp` to type `∘`.

### Exercise 2.1

The first `map` law can now be written in Agda as
```agda
map-law1 : {A : Type} (xs : List A) → map id xs ≡ xs
map-law1 xs = {!!}
```

**Define** this function. (Hint: An induction hypothesis comes in helpful).

### Exercise 2.2

A partial statement of the second `map` law is the following:
```agda
map-law2 : {A B C : Type} (g : {!!}) (f : {!!}) (xs : List A)
         → {!!} ≡ {!!}
map-law2 g f xs = {!!}
```

**Complete** the holes in `map-law2 : ...`, i.e. write down the types of `g` and
`f`, and translate the second `map` law `map (g ∘ f) xs = map g (map f xs)` to
Agda.


### Exercise 2.3

Now **complete** the proof of `map-law2`.

## Section 3: Filtering lists

**Define** a function `and` that takes a list of Booleans and computes the
conjunction of all the Booleans in it:

### Exercise 3.1

```agda
and : List Bool → Bool
and bs = {!!}
```

For example, `and true false` should equal to `false`

```agda
and-example1 : and (true :: false :: []) ≡ false
and-example1 = {! refl false !}
 -- make sure that your code is correct by checking
 -- that the equality in this type is definitional.
 -- The proof should be just `refl false`.
```

```agda
and-example2 : and [] ≡ true
and-example2 = {! refl true!}
 -- make sure that your code is correct by checking
 -- that the equality in this type is definitional.
 -- The proof should be just `refl true`.
```

### Exercise 3.2

**Define** a function `for-all` that takes a list of element of some type `A`
together with a predicate `p : A → Bool`, and computes the Boolean truth value
denoting if *everything* in the list satisfy the predicate `p`. You should be
able to this just by composing `map` and your implementation of `and`.

```agda
for-all : {A : Type} → (A → Bool) → List A → Bool
for-all = {!!}
```

Next, we will define a function `filter` that filters out a subset of a list of
elements that satisfy a certain predicate. You have probably worked with a
function like this in Haskell before.

### Exercise 3.3

```agda
filter : {A : Type} → (A → Bool) → List A → List A
filter = {!!}
```

`filter p xs` should give you the sublist of `xs` consisting of elements that
satisfy `p`.

### Exercise 3.4

You have probably worked with similar functions in Haskell before. The nice
thing about working in Agda is that, we can actually write down *specifications*
of such functions.

Using your `for-all`, **define** a function that expresses: *for every predicate
`p` and every list `xs`, everything in `filter p xs` satisfies the predicate
`p`*. Call this type `filter-soundness`.

```agda
filter-soundness : {A : Type} → Type
filter-soundness {A} = {!!}
```

Note that the type of the function here is `Type`. This means that you are not
writing an inhabitant of a type but you are *writing a type*, i.e. you are not
asked to *prove* filter soundness, but rather to *state* it.
