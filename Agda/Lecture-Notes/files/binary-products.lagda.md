
[Martin Escardo](Https://www.Cs.Bham.Ac.Uk/~mhe/).
Notes originally written for the module *Advanced Functional Programming* of the [University of Birmingham](https://www.birmingham.ac.uk/index.aspx), UK.


<!--
```agda
{-# OPTIONS --without-K --safe #-}

module binary-products where

open import general-notation
```
-->
# The cartesian-product type former `_×_`

As [discussed before](sums.lagda.md), the cartesian product `A × B` is simply `Σ {A} (λ x → B)` which means that for `(x , y) : A × B` the type of `y` is always `B`, independently of what `x` is. Using our special syntax for `Σ` this can be defined as follows in Agda:
```agda
open import sums public

_×_ : Type → Type → Type
A × B = Σ x ꞉ A , B

infixr 2 _×_
```
So the elements of `A × B` are of the form `(x , y)` with `x : A` and `y : B`.

## Logical conjunction ("and")

The logical interpretation of `A × B` is "A and B". This is because in order to show that the proposition "A and B" holds, we have to show that each of A and B holds. To show that A holds we exhibit an element `x` of A, and to show that B holds we exhibit an element `y` of B, and so to show that "A and B" holds we exhibit a pair `(x , y)` with `x : A` and `b : B`

## Logical equivalence

We now can define bi-implication, or logical equivalence, as follows:
```agda
_⇔_ : Type → Type → Type
A ⇔ B = (A → B) × (B → A)

infix -2 _⇔_
```
The symbol `⇔` is often pronounced "if and only if".

We use the first and second projections to extract the left-to-right implication and the right-to-left implication:
```agda
lr-implication : {A B : Type} → (A ⇔ B) → (A → B)
lr-implication = pr₁

rl-implication : {A B : Type} → (A ⇔ B) → (B → A)
rl-implication = pr₂
```

## Alternative definition of `_×_`

There is [another way to define binary products](binary-products-as-products.lagda.md) as a special case of `Π` rather than `Σ`.

[Go back to the table of contents](https://martinescardo.github.io/HoTTEST-Summer-School/)
