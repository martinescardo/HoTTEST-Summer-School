
[Martin Escardo](Https://www.Cs.Bham.Ac.Uk/~mhe/).
Notes originally written for the module *Advanced Functional Programming* of the [University of Birmingham](https://www.birmingham.ac.uk/index.aspx), UK.


<!--
```agda
{-# OPTIONS --without-K --safe #-}

module Vector where

open import general-notation
open import natural-numbers-type
```
-->
# Vectors

This type has already been briefly discussed in the [introduction](introduction.lagda.md).
```agda
open import natural-numbers-type

data Vector (A : Type) : ℕ → Type where
 []   : Vector A 0
 _::_ : {n : ℕ} → A → Vector A n → Vector A (suc n)

infixr 10 _::_
```

## Elimination principle

```agda
Vector-elim : {X : Type} (A : (n : ℕ) → Vector X n → Type)
            → A 0 []
            → ((x : X) (n : ℕ) (xs : Vector X n) → A n xs → A (suc n) (x :: xs))
            → (n : ℕ) (xs : Vector X n) → A n xs
Vector-elim {X} A a f = h
 where
  h : (n : ℕ) (xs : Vector X n) → A n xs
  h 0       []        = a
  h (suc n) (x :: xs) = f x n xs (h n xs)
```
It is better, in practice, to make the parameter `n` implicit, because it can be inferred from the type of `xs`, and so we get less clutter:
```agda
Vector-elim' : {X : Type} (A : {n : ℕ} → Vector X n → Type)
             → A []
             → ((x : X) {n : ℕ} (xs : Vector X n) → A xs → A (x :: xs))
             → {n : ℕ} (xs : Vector X n) → A xs
Vector-elim' {X} A a f = h
 where
  h : {n : ℕ} (xs : Vector X n) → A xs
  h []        = a
  h (x :: xs) = f x xs (h xs)
```
Again, the non-dependent version gives a fold function for vectors:
```agda
Vector-nondep-elim' : {X A : Type}
                    → A
                    → (X → {n : ℕ} → Vector X n → A → A)
                    → {n : ℕ} → Vector X n → A
Vector-nondep-elim' {X} {A} = Vector-elim' {X} (λ {_} _ → A)
```

## Induction on vectors

As for lists, it is given by the proposition-as-types reading of the type of `Vector-elim`.

[Go back to the table of contents](https://martinescardo.github.io/HoTTEST-Summer-School/)
