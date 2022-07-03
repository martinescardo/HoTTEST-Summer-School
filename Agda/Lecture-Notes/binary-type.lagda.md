
[Martin Escardo](Https://www.Cs.Bham.Ac.Uk/~mhe/).
Notes originally written for the module *Advanced Functional Programming* of the [University of Birmingham](https://www.birmingham.ac.uk/index.aspx), UK.


<!--
```agda
{-# OPTIONS --without-K --safe #-}

module binary-type where

open import general-notation
```
-->
# The binary type 𝟚

This type can be defined to be `𝟙 ∔ 𝟙` using [binary sums](binary-sums.lagda.md), but we give a direct definition which will allow us to discuss some relationships between the various type formers of Basic MLTT.

```agda
data 𝟚 : Type where
 𝟎 𝟏 : 𝟚
```
This type is not only [isomorphic to `𝟙 ∔ 𝟙`](isomorphisms.lagda.md) but also to the type [`Bool`](Bool.lagda.md) of booleans.
Its elimination principle is as follows:
```agda
𝟚-elim : {A : 𝟚 → Type}
       → A 𝟎
       → A 𝟏
       → (x : 𝟚) → A x
𝟚-elim x₀ x₁ 𝟎 = x₀
𝟚-elim x₀ x₁ 𝟏 = x₁
```
In logical terms, this says that it order to show that a property `A` of elements of the binary type `𝟚` holds for all elements of the type `𝟚`, it is enough to show that it holds for `𝟎` and for `𝟏`. The non-dependent version of the eliminator is the following:
```agda
𝟚-nondep-elim : {A : Type}
              → A
              → A
              → 𝟚 → A
𝟚-nondep-elim {A} = 𝟚-elim {λ _ → A}
```
Notice that the non-dependent version is like `if-then-else`, if we think of one of the elements of `A` as `true` and the other as `false.

The dependent version generalizes the *type* of the non-dependent
version, with the same definition of the function.

[Go back to the table of contents](https://martinescardo.github.io/HoTTEST-Summer-School/)
