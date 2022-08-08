# Week 7 - Cubical Agda Exercises

## Standard disclaimer:

**The exercises are designed to increase in difficulty so that we can cater to
our large and diverse audience. This also means that it is *perfectly fine* if
you don't manage to do all exercises: some of them are definitely a bit hard for
beginners and there are likely too many exercises! You *may* wish to come back
to them later when you have learned more.**

Having said that, here we go!

In case you haven't done the other Agda exercises:
This is a markdown file with Agda code, which means that it displays nicely on
GitHub, but at the same time you can load this file in Agda and fill the holes
to solve exercises.

**When solving the problems,
please make a copy of this file to work in, so that it doesn't get overwritten
(in case we update the exercises through `git`)!**


```agda
{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Exercises7 where

open import cubical-prelude
open import Lecture7-notes
```

```agda
private
  variable
    A : Type ℓ
    B : A → Type ℓ
```

## Part I: Generalizing to dependent functions

### Exercise 1 (★)

State and prove funExt for dependent functions `f g : (x : A) → B x`

### Exercise 2 (★)

Generalize the type of ap to dependent function `f : (x : A) → B x`
(hint: the result should be a `PathP`)


## Part II: Some facts about (homotopy) propositions and sets

The first three homotopy levels `isContr`, `isProp` and `isSet`
are defined in `cubical-prelude` in the usual way
(only using path types of course).

### Exercise 3 (★)

State and prove that inhabited propositions are contractible

### Exercise 4 (★★)

We could have stated isProp as follows:

```agda
isProp' : Type ℓ → Type ℓ
isProp' A = (x y : A) → isContr (x ≡ y)
```

Prove that isProp' A implies isProp A and vice versa.
Hint: for one direction you need path composition `_·_`, which one?


### Exercise 5 (★)

Prove

```agda
isPropΠ : (h : (x : A) → isProp (B x)) → isProp ((x : A) → B x)
isPropΠ = {!!}
```

### Exercise 6 (★)

Prove the inverse of `funExt` (sometimes called `happly`):

```agda
funExt⁻ : {f g : (x : A) → B x} → f ≡ g → ((x : A) → f x ≡ g x)
funExt⁻  = {!!}
```

### Exercise 7 (★★)

Use funExt⁻ to prove isSetΠ:

```agda
isSetΠ : (h : (x : A) → isSet (B x)) → isSet ((x : A) → B x)
isSetΠ = {!!}
```

### Exercise 8 (★★★): alternative contractibility of singletons

We could have defined the type of singletons as follows

```agda
singl' : {A : Type ℓ} (a : A) → Type ℓ
singl' {A = A} a = Σ x ꞉ A , x ≡ a
```

Prove the corresponding version of contractibility of singetons for
`singl'` (hint: use a suitable combinations of connections and `~_`)

```agda
isContrSingl' : (x : A) → isContr (singl' x)
isContrSingl' x = {!!}
```

## Part III: Equality in Σ-types
### Exercise 9 (★★)

Having the primitive notion of equality be heterogeneous is an
easily overlooked, but very important, strength of cubical type
theory. This allows us to work directly with equality in Σ-types
without using transport.

Fill the following holes (some of them are easier than you might think):

```agda
module _ {A : Type ℓ} {B : A → Type ℓ'} {x y : Σ A B} where

  ΣPathP : Σ p ꞉ pr₁ x ≡ pr₁ y , PathP (λ i → B (p i)) (pr₂ x) (pr₂ y)
         → x ≡ y
  ΣPathP = {!!}

  PathPΣ : x ≡ y
         → Σ p ꞉ pr₁ x ≡ pr₁ y , PathP (λ i → B (p i)) (pr₂ x) (pr₂ y)
  PathPΣ = {!!}

  ΣPathP-PathPΣ : ∀ p → PathPΣ (ΣPathP p) ≡ p
  ΣPathP-PathPΣ = {!!}

  PathPΣ-ΣPathP : ∀ p → ΣPathP (PathPΣ p) ≡ p
  PathPΣ-ΣPathP = {!!}
```

If one looks carefully the proof of prf in Lecture 7 uses ΣPathP
inlined, in fact this is used all over the place when working
cubically and simplifies many proofs which in Book HoTT requires long
complicated reasoning about transport.


## Part III: Some HITs

Now we want prove some identity of HITs analogous to `Torus ≡ S¹ × S¹`
Hint: you can just `isoToPath` in all of them.

### Exercise 10 (★★★)

Prove the following facts about suspensions:

```agda

suspUnitChar : Susp Unit ≡ Interval
suspUnitChar = {!!}

suspBoolChar : Susp Bool ≡ S¹
suspBoolChar = {!!}

```


### Exercise 11 (★★★)

Define suspension using the Pushout HIT and prove that it's equal to Susp.
