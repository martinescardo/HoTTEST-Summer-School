
[Martin Escardo](Https://www.Cs.Bham.Ac.Uk/~mhe/).
Notes originally written for the module *Advanced Functional Programming* of the [University of Birmingham](https://www.birmingham.ac.uk/index.aspx), UK.


<!--
```agda
{-# OPTIONS --without-K --safe #-}

module sums where

open import general-notation
```
-->
# The sum type former `Σ`

Very often in computation we work with the type of pairs `(x , y)` with `x : A` and `y : B` where `A` and `B` are types. We will write `A × B` for the type of such pairs, and call it the [*cartesian product*](https://en.wikipedia.org/wiki/Cartesian_product). We will define this type as a particular case of a more general type, whose elements are again of the form `(x , y)` but with the difference that `x : A` and `y : B x` where `A : Type` and `B : A → Type`. The difference amounts to the fact that the type of the second component `y` depends on the first element `x`. The default notation for this type will be `Σ {A} B`, or simply `Σ B` when `A` can be inferred from the context, but we will also introduce the more common sum notation `Σ x ꞉ A , B x`. This type is also called the [disjoint union](https://en.wikipedia.org/wiki/Disjoint_union) of the type family `B : A → Type`.

## Examples

A simple example is the type `Σ xs ꞉ List X , Vector X (length xs)` with `X : Type`. An element of this type is a pair `(xs , ys)` where `xs` is a list and `ys` is a vector of the same length as `xs`.

Another example, which iterates the `Σ` type construction, is `Σ x : ℕ , Σ y : ℕ , Σ z : ℕ , x ≡ y * z`. An element of this type is now a quadruple `(x , (y , (z , p)))` where `x y z : ℕ` and `p : x ≡ y * z`. That is, the fourth component ensures that `x y z : ℕ` are allowed in the tuple if, and only if, `x ≡ y * z`. We will see more interesting examples shortly.

## Definition

The `Σ` type can be defined in Agda using a `data` declaration as follows:
<!--
```agda
module _ where
 private
```
-->
```agda
  data Σ {A : Type } (B : A → Type) : Type  where
   _,_ : (x : A) (y : B x) → Σ {A} B

  pr₁ : {A : Type} {B : A → Type} → Σ B → A
  pr₁ (x , y) = x

  pr₂ : {A : Type} {B : A → Type} → (z : Σ B) → B (pr₁ z)
  pr₂ (x , y) = y
  ```
Notice that the type of `pr₂` is dependent and uses `pr₁` to express the dependency.

However, for a number of reasons to be explained later, we prefer to define it using a [record](https://agda.readthedocs.io/en/latest/language/record-types.html) definition:

```agda
record Σ {A : Type } (B : A → Type) : Type  where
 constructor
  _,_
 field
  pr₁ : A
  pr₂ : B pr₁
```

Here we automatically get the projections with the same types and definitions as above and hence we don't need to provide them. In order for the projections `pr₁` and `pr₂` to be visible outside the scope of the record, we `open` the record. Moreover, we open it `public` so that when other files import this one, these two projections will be visible in the other files. The "constructor" allows to form an element of this type. Because "," is not a reserved symbol in Agda, we can use it as a binary operator to write `x , y`. However, following mathematical tradition, we will write brackets around that, to get `(x , y)`, even if this is not necessary. We also declare a fixity and precedence for this operator.

```agda
open Σ public
infixr 0 _,_
```
Because we make `_,_` right associative, we can write `(x , y , z , p)` rather than `(x , (y , (z , p)))` as we did above.

We also use a syntax declaration, [as we did](products.lagda.md) for dependent function types using Π, to get the more traditional type-theoretical notation.
```agda
Sigma : (A : Type) (B : A → Type) → Type
Sigma A B = Σ {A} B

syntax Sigma A (λ x → b) = Σ x ꞉ A , b

infix -1 Sigma
```

## Elimination principle

We now define and discuss the elimination principle.
```agda
Σ-elim : {A : Type } {B : A → Type} {C : (Σ x ꞉ A , B x) → Type}
       → ((x : A) (y : B x) → C (x , y))
       → (z : Σ x ꞉ A , B x) → C z
Σ-elim f (x , y) = f x y
```
So the elimination principle for `Σ` is what was called `curry` in functional programming. The logical interpretation for this principle is that in order to show that "for all z : Σ x ꞉ A , B x) we have that C z holds", it is enough to show that "for all x : A and y : B x we have that C (x , y) holds". This condition is not only sufficient but also [necessary](https://en.wikipedia.org/wiki/Necessity_and_sufficiency):
```agda
Σ-uncurry : {A : Type } {B : A → Type} {C : (Σ x ꞉ A , B x) → Type}
          → ((z : Σ x ꞉ A , B x) → C z)
          → (x : A) (y : B x) → C (x , y)
Σ-uncurry g x y = g (x , y)
```

## Existential quantification

Regarding logic, the `Σ` type is used to interpret the existential quantifier `∃`. The logical proposition `∃ x : X, A x`,  that is, "there exists x : X such that A x", is interpreted as the type `Σ x ꞉ X , A x`. The reason is that to show that `∃ x : X, A x` we have to exhibit an example `x : X` and  show that `x` satisfies the condition `A x` with some `y : A x`, in a pair `(x , y)`.

For example, the type `Σ x : ℕ , Σ y : ℕ , Σ z : ℕ , x ≡ y * z` can be interpreted as saying that "there are natural numbers x, y, and z such that x = y * z", which is true as witnessed by the element `(6,2,3,refl 6)` of that type. But there are many other witnesses of this type, of course, such as `(10,5,2,refl 10)`.

It is important to notice that it is possible to write types that correspond to false logical statements, and hence are empty. For example, consider `Σ x : ℕ , x ≡ x + 1`. There is no natural number that is its own successor, of course, and so this type is empty. While this type is empty, the type `¬ (Σ x : ℕ , x ≡ x + 1)` has an element, as we will see, which witnesses the fact that "there doesn't exist a natural number `x` such that `x = x + 1`".

## Existential quantification in HoTT/UF

In HoTT/UF it useful to have an alternative existential quantifier `∃ x : X , A x` defined to be `∥ Σ x : X , A x ∥` where `∥_∥` is a certain *propositional truncation* operation.

[Go back to the table of contents](https://martinescardo.github.io/HoTTEST-Summer-School/)
