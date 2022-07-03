
[Martin Escardo](Https://www.Cs.Bham.Ac.Uk/~mhe/).
Notes originally written for the module *Advanced Functional Programming* of the [University of Birmingham](https://www.birmingham.ac.uk/index.aspx), UK.


<!--
```agda
{-# OPTIONS --without-K --safe #-}

module binary-sums where

open import general-notation
```
-->

# The binary-sum type former `_∔_`

This is the same as (or, more precisely, [isomorphic](isomorphisms.lagda.md) to) the `Either` type defined earlier (you can try this as an exercise). The notation in type theory is `_+_`, but we want to reserve this for addition of natural numbers, and hence we use the same symbol with a dot on top:
```agda
data _∔_ (A B : Type) : Type where
 inl : A → A ∔ B
 inr : B → A ∔ B

infixr 20 _∔_
```

The type `A ∔ B` is called the coproduct of `A` and `B`, or the sum of `A` and `B`, or the disjoint union of `A` and `B`. The elements of `A ∔ B` are of the form `inl x` with `x : A` and `inr y` with `y : B`.

In terms of computation, we use the type `A ∔ B` when we want to put the two types together into a single type. It is also possible to write `A ∔ A`, in which case we will have two copies of the type `A`, so that now every element `x` of `A` has two different incarnations `inl a` and `inr a` in the type `A ∔ A`. For example, the [unit type](unit-type.lagda.md) `𝟙` has exactly one element, namely `⋆ : 𝟙`, and hence the type `𝟙 ∔ 𝟙` has precisely two elements, namely  `inl ⋆` and `inr ⋆`.

## Logical disjunction ("or")

In terms of logic, we use the type `A ∔ B` to express "A or B". This is because in order for "A or B" to hold, at least one of A and B must hold. The type `A → A ∔ B` of the function `inl` is interpreted as saying that if A holds then so does "A or B", and similarly, the type of B → A ∔ B of the function `inr` says that if B holds then so does "A or B". In other words, if `x : A` is a proof of `A`, then `inl x : A + B` is a proof of `A or B`, and if `y : B` is a proof of B, them `inr y : A + B` is a proof of "A or B". Here when we said "proof" we meant "program" after the propositions-as-types and proofs-as-programs paradigm.

## Logical disjunction in HoTT/UF

In HoTT/UF it useful to have an alternative disjunction operation `A ∨ B` defined to be `∥ A ∔ B ∥` where `∥_∥` is a certain *propositional truncation* operation.

## Elimination principle

Now suppose we want to define a dependent function `(z : A ∔ B) → C z`. How can we do that? If we have two functions `f : (x : A) → C (inl x)` and `g : (y : B) → C (inr y)`, then, given `z : A ∔ B`, we can inspect whether `z` is of the form `inl x` with `x : A` or of the form `inr y` with `y : B`, and the respectively apply `f` or `g` to get an element of `C z`. This procedure is called the *elimination* principle for the type former `_∔_` and can be written in Agda as follows:

```agda
∔-elim : {A B : Type} (C : A ∔ B → Type)
       → ((x : A) → C (inl x))
       → ((y : B) → C (inr y))
       → (z : A ∔ B) → C z
∔-elim C f g (inl x) = f x
∔-elim C f g (inr y) = g y
```
So the eliminator amounts to simply definition by cases. In terms of logic, it says that in order to show that "for all z : A ∔ B we have that C z holds" it is enough to show two things: (1) "for all x : A it is the case that C (inl x) holds", and (2) "forall y : B it is the case that C (inr y) holds". This is not only sufficient, but also necessary:
```agda
open import binary-products

∔-split : {A B : Type} (C : A ∔ B → Type)
        → ((z : A ∔ B) → C z)
        → ((x : A) → C (inl x)) × ((y : B) → C (inr y))
∔-split {A} {B} C h = f , g
 where
  f : (x : A) → C (inl x)
  f x = h (inl x)

  g : (y : B) → C (inr y)
  g y = h (inr y)
```

There is also a version of the eliminator in which `C` doesn't depend on `z : A ∔ B` and is always the same:
```agda
∔-nondep-elim : {A B C : Type}
              → (A → C)
              → (B → C)
              → (A ∔ B → C)
∔-nondep-elim {A} {B} {C} = ∔-elim (λ z → C)
```
In terms of logic, this means that in order to show that "A or B implies C", it is enough to show that both "A implies C" and "B implies C". This also can be inverted:
```agda
∔-nondep-split : {A B C : Type}
               → (A ∔ B → C)
               → (A → C) × (B → C)
∔-nondep-split {A} {B} {C} = ∔-split (λ z → C)
```
In terms of logic, this means that if `A or B implies C` then both `A implies C` and `B implies C`.

## Alternative definition of `_∔_`

There is [another way to define binary sums](binary-sums-as-sums.lagda.md) as a special case of `Σ`.

[Go back to the table of contents](https://martinescardo.github.io/HoTTEST-Summer-School/)
