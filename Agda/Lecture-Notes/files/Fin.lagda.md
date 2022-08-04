
[Martin Escardo](Https://www.Cs.Bham.Ac.Uk/~mhe/).
Notes originally written for the module *Advanced Functional Programming* of the [University of Birmingham](https://www.birmingham.ac.uk/index.aspx), UK.


<!--
```agda
{-# OPTIONS --without-K --safe #-}

module Fin where

open import general-notation
open import natural-numbers-type
```
-->
# Finite types

We now define a type `Fin n` which has exactly `n` elements, where `n : ℕ` is a natural number.

```agda
open import natural-numbers-type public

data Fin : ℕ → Type where
 zero : {n : ℕ} → Fin (suc n)
 suc  : {n : ℕ} → Fin n → Fin (suc n)
```
Examples:
```agda
private
 x₀ x₁ x₂ : Fin 3
 x₀ = zero
 x₁ = suc zero
 x₂ = suc (suc zero)

 y₀ y₁ y₂ : Fin 3
 y₀ = zero {2}
 y₁ = suc {2} (zero {1})
 y₂ = suc {2} (suc {1} (zero {0}))
```
And these are all the elements of `Fin 3`. Notice that `Fin 0` is empty:
```agda

open import empty-type public

Fin-0-is-empty : is-empty (Fin 0)
Fin-0-is-empty ()
```
Here `()` is a pseudo-pattern that tells that there is no constructor for the type.
```agda
Fin-suc-is-nonempty : {n : ℕ} → ¬ is-empty (Fin (suc n))
Fin-suc-is-nonempty f = f zero
```

## Elimination principle

```agda
Fin-elim : (A : {n : ℕ} → Fin n → Type)
         → ({n : ℕ} → A {suc n} zero)
         → ({n : ℕ} (k : Fin n) → A k → A (suc k))
         → {n : ℕ} (k : Fin n) → A k
Fin-elim A a f = h
 where
  h : {n : ℕ} (k : Fin n) → A k
  h zero    = a
  h (suc k) = f k (h k)
```
So this again looks like [primitive recursion](natural-numbers-type.lagda.md). And it gives an induction principle for `Fin`.

## Every element of `Fin n` can be regarded as an element of `ℕ`

```agda
ι : {n : ℕ} → Fin n → ℕ
ι zero    = zero
ι (suc x) = suc (ι x)
```

[Go back to the table of contents](https://martinescardo.github.io/HoTTEST-Summer-School/)
