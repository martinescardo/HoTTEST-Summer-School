
Martin Escardo.
Notes originally written for the module "Advanced Functional Programming"
at the School of Computer Science of the University of Birmingham, UK.


<!--
```agda
{-# OPTIONS --without-K --safe #-}

module Maybe where

open import general-notation
open import products
open import identity-type
```
-->
# The `Maybe` type constructor

```agda

data Maybe (X : Type) : Type where
  nothing : Maybe X
  just    : X → Maybe X
```

## Elimination principle

```agda
Maybe-elim : {X : Type} (A : Maybe X → Type)
           → A nothing
           → ((x : X) → A (just x))
           → (m : Maybe X) → A m
Maybe-elim A a f nothing  = a
Maybe-elim A a f (just x) = f x
```
In terms of functional programming, this says that using an element `a : A nothing` and a dependent function `f : (x : X) → A (just x)`, we can define a dependent function of type `(m : Maybe X) → A m`, by cases on whether `m` is `nothing` or `just x`.

In terms of logic, the elimination principle says that in order to prove that "for all `m : Maybe X`, the proposition `A m` holds" it is enough to prove that `A nothing` holds and that for all `x : X`, the proposition `A (just x)` holds.

## Non-dependent version

It is a special case of the dependent version:
```agda
Maybe-nondep-elim : {X A : Type}
                  → A
                  → (X → A)
                  → Maybe X → A
Maybe-nondep-elim {X} {A} = Maybe-elim (λ _ → A)
```

## Isomorphism with a Basic MLTT type

We now show that there is an [isomorphism](isomorphisms.lagda.md) of the type `Maybe X` with a type in basic Martin-Löf Type Theory, so that, strictly speaking, we don't need to include `Maybe` in our repertoire of Agda definitions. Nevertheless, in practice, it is convenient to include it.
```agda
open import unit-type
open import binary-sums
open import isomorphisms

Maybe-isomorphism : (X : Type) → Maybe X ≅ 𝟙 ∔ X
Maybe-isomorphism X = record { bijection = f ; bijectivity = f-is-bijection }
 where
  f : Maybe X → 𝟙 ∔ X
  f nothing  = inl ⋆
  f (just x) = inr x

  g : 𝟙 ∔ X → Maybe X
  g (inl ⋆) = nothing
  g (inr x) = just x

  gf : g ∘ f ∼ id
  gf nothing  = refl nothing
  gf (just x) = refl (just x)

  fg : f ∘ g ∼ id
  fg (inl ⋆) = refl (inl ⋆)
  fg (inr x) = refl (inr x)

  f-is-bijection : is-bijection f
  f-is-bijection = record { inverse = g ; η = gf ; ε = fg}
```
