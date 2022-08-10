
[Martin Escardo](Https://www.Cs.Bham.Ac.Uk/~mhe/).
Notes originally written for the module *Advanced Functional Programming* of the [University of Birmingham](https://www.birmingham.ac.uk/index.aspx), UK.


<!--
```agda
{-# OPTIONS --without-K --safe #-}

module List where

open import general-notation
```
-->
# Lists

This type has already been briefly discussed in the introduction.
```agda
data List (A : Type) : Type where
 []   : List A
 _::_ : A → List A → List A

infixr 10 _::_
```

## Elimination principle

```agda
List-elim : {X : Type} (A : List X → Type)
          → A []
          → ((x : X) (xs : List X) → A xs → A (x :: xs))
          → (xs : List X) → A xs
List-elim {X} A a f = h
 where
  h : (xs : List X) → A xs
  h []        = a
  h (x :: xs) = f x xs (h xs)
```
Notice that the definition of `h` is the same as that of the usual `fold` function for lists, if you know this, but the type is more general. In fact, the `fold` function is just the non-dependent version of the eliminator
```agda
List-nondep-elim : {X A : Type}
                 → A
                 → (X → List X → A → A)
                 → List X → A
List-nondep-elim {X} {A} a f = List-elim {X} (λ _ → A) a f
```

## Induction on lists

In terms of logic, the elimination principle gives an induction principle for proving properties of lists.

[Go back to the table of contents](https://martinescardo.github.io/HoTTEST-Summer-School/)
