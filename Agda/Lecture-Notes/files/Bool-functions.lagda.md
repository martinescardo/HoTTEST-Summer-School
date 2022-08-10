
[Martin Escardo](Https://www.Cs.Bham.Ac.Uk/~mhe/).
Notes originally written for the module *Advanced Functional Programming* of the [University of Birmingham](https://www.birmingham.ac.uk/index.aspx), UK.


<!--
```agda
{-# OPTIONS --without-K --safe #-}

module Bool-functions where

open import prelude
```
-->
# The booleans

The booleans are isomorphic to a Basic MLTT type:

```agda
open import isomorphisms

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

[Go back to the table of contents](https://martinescardo.github.io/HoTTEST-Summer-School/)
