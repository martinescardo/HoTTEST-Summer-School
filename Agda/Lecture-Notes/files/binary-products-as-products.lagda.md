
[Martin Escardo](Https://www.Cs.Bham.Ac.Uk/~mhe/).
Notes originally written for the module *Advanced Functional Programming* of the [University of Birmingham](https://www.birmingham.ac.uk/index.aspx), UK.


<!--
```agda
{-# OPTIONS --without-K --safe #-}

module binary-products-as-products where

open import prelude
```
-->

## Binary products as a special case of arbitrary products

Using the [binary type](binary-type.lagda.md) `𝟚`, binary products can be seen as a special case of arbitrary products as follows:
```agda
open import binary-type

_×'_ : Type → Type → Type
A₀ ×' A₁ = Π n ꞉ 𝟚 , A n
 where
  A : 𝟚 → Type
  A 𝟎 = A₀
  A 𝟏 = A₁

infixr 2 _×'_
```
We could have written the type `Π n ꞉ 𝟚 , A n` as simply `(n : 𝟚) → A n`, but we wanted to emphasize that binary products `_×_` are special cases of arbitrary products `Π`.

To justify this claim, we establish an [isomorphism](isomorphisms.lagda.md). But we need to assume [function extensionality](function-extensionality.lagda.md) for this purpose.
```agda
open import isomorphisms
open import function-extensionality

binary-product-isomorphism : FunExt → (A₀ A₁ : Type) → A₀ × A₁ ≅ A₀ ×' A₁
binary-product-isomorphism funext A₀ A₁ = record { bijection = f ; bijectivity = f-is-bijection }
 where
  f : A₀ × A₁ → A₀ ×' A₁
  f (x₀ , x₁) 𝟎 = x₀
  f (x₀ , x₁) 𝟏 = x₁

  g : A₀ ×' A₁ → A₀ × A₁
  g h = h 𝟎 , h 𝟏

  gf : g ∘ f ∼ id
  gf (x₀ , x₁) = refl (x₀ , x₁)

  fg : f ∘ g ∼ id
  fg h = γ
   where
    p : f (g h) ∼ h
    p 𝟎 = refl (h 𝟎)
    p 𝟏 = refl (h 𝟏)

    γ : f (g h) ≡ h
    γ = funext p

  f-is-bijection : is-bijection f
  f-is-bijection = record { inverse = g ; η = gf ; ε = fg }
```
Notice that the above argument, in Agda, not only *shows* that the types are indeed isomorphic, but also explains *how* and *why* they are isomorphic. Thus, logical arguments coded in Agda are useful not only to get confidence in correctness, but also to gain understanding.

[Go back to the table of contents](https://martinescardo.github.io/HoTTEST-Summer-School/)
