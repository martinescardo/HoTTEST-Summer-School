
Martin Escardo.
Notes originally written for the module "Advanced Functional Programming"
at the School of Computer Science of the University of Birmingham, UK.


<!--
```agda
{-# OPTIONS --without-K --safe #-}

module Agda-Lecture-Notes.Bool-functions where

open import Agda-Lecture-Notes.prelude
```
-->
# The booleans

The booleans are isomorphic to a Basic MLTT type:

```agda
open import Agda-Lecture-Notes.isomorphisms

Bool-isomorphism : Bool ≅ 𝟙 ∔ 𝟙
Bool-isomorphism = record { bijection = f ; bijectivity = f-is-bijection }
 where
  f : Bool → 𝟙 ∔ 𝟙
  f false = inl ⋆
  f true  = inr ⋆

  g : 𝟙 ∔ 𝟙 → Bool
  g (inl ⋆) = false
  g (inr ⋆) = true

  gf : g ∘ f ∼ id
  gf true  = refl true
  gf false = refl false

  fg : f ∘ g ∼ id
  fg (inl ⋆) = refl (inl ⋆)
  fg (inr ⋆) = refl (inr ⋆)

  f-is-bijection : is-bijection f
  f-is-bijection = record { inverse = g ; η = gf ; ε = fg }
```
