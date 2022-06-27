
Martin Escardo.
Notes originally written for the module "Advanced Functional Programming"
at the School of Computer Science of the University of Birmingham, UK.


<!--
```agda
{-# OPTIONS --without-K --safe #-}

module binary-sums-as-sums where

open import prelude
```
-->

## Binary sums as a special case of arbitrary sums

Using the binary type `𝟚`, binary sums can be seen as a special case of arbitrary sums as follows:
```agda
open import binary-type

_∔'_ : Type → Type → Type
A₀ ∔' A₁ = Σ n ꞉ 𝟚 , A n
 where
  A : 𝟚 → Type
  A 𝟎 = A₀
  A 𝟏 = A₁
```

To justify this claim, we establish an isomorphism.
```agda
open import isomorphisms

binary-sum-isomorphism : (A₀ A₁ : Type) → A₀ ∔ A₁ ≅ A₀ ∔' A₁
binary-sum-isomorphism A₀ A₁ = record { bijection = f ; bijectivity = f-is-bijection }
 where
  f : A₀ ∔ A₁ → A₀ ∔' A₁
  f (inl x₀) = 𝟎 , x₀
  f (inr x₁) = 𝟏 , x₁

  g : A₀ ∔' A₁ → A₀ ∔ A₁
  g (𝟎 , x₀) = inl x₀
  g (𝟏 , x₁) = inr x₁

  gf : g ∘ f ∼ id
  gf (inl x₀) = refl (inl x₀)
  gf (inr x₁) = refl (inr x₁)

  fg : f ∘ g ∼ id
  fg (𝟎 , x₀) = refl (𝟎 , x₀)
  fg (𝟏 , x₁) = refl (𝟏 , x₁)

  f-is-bijection : is-bijection f
  f-is-bijection = record { inverse = g ; η = gf ; ε = fg }
```
