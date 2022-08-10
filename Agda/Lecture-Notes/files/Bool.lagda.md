
[Martin Escardo](Https://www.Cs.Bham.Ac.Uk/~mhe/).
Notes originally written for the module *Advanced Functional Programming* of the [University of Birmingham](https://www.birmingham.ac.uk/index.aspx), UK.


<!--
```agda
{-# OPTIONS --without-K --safe #-}

module Bool where

open import general-notation
open import natural-numbers-type
```
-->
# The booleans

We discuss the elimination principle for the booleans. The booleans
are defined by constructors `true` and `false`:
```agda
data Bool : Type where
 true false : Bool
```
## `if-then-else`

The non-dependent eliminator of the type of booleans amounts to `if-then-else`
```agda
if_then_else_ : {A : Type} → Bool → A → A → A
if true  then x else y = x
if false then x else y = y
```
In general, the non-dependent elimination principle of a type explains how to "get out of the type", whereas the constructors tell us how to "get into the type".

## Dependent `if-then-else`

Notice that both `x` (the `then` branch) and `y` (the `else` branch) have the same type, name `A`. Using dependent type, we can have different types in the dependent version of the eliminator. We make the type `A` depend on the boolean condition of the `if-then-else`. This means that now we will have `A : Bool → Type` instead of `A : Bool`. This is a function that given a boolean `b : Bool`, returns a type `A b`. Functions whose return value is a type are also called *type families*. Also `A b` is called a *dependent type*. It depends on the value of the boolean `b`. Here is an example, which we make private to this module.
```agda
private
 open import natural-numbers-type
 A-example : Bool → Type
 A-example true  = ℕ
 A-example false = Bool
```
Using this idea, we have the following dependently-typed version of `if_then_else_`, which now has four explicit arguments. We make `A` explicit this time, because Agda can hardly ever infer it.
```agda
dependent-on_if_then_else_ : (A : Bool → Type) → (b : Bool) → A true → A false → A b
dependent-on A if true  then x else y = x
dependent-on A if false then x else y = y
```
Notice that the return type `A b` depends on the second argument `b` of the function.
Notice also that `x : A true` and `y : A false`.
```agda
private
 example₀ : (b : Bool) → A-example b
 example₀ b = dependent-on A-example if b then 3 else true
```
This works because `3 : A-example true` and `true : A-example false`. So the dependent version of `if-then-else` allows the `then` and `else` branches have different types, which depend on the type of the condition.

## The official definition of the eliminator of the type of booleans

Traditionally the argument of the type we want to eliminate (the booleans in our case) is written last:
```agda
Bool-elim : (A : Bool → Type)
          → A true
          → A false
          → (b : Bool) → A b
Bool-elim A x y true  = x
Bool-elim A x y false = y
```
The type of `Bool-elim` says that if we provide elements of the type `A true` and `A false`, we get a function `(b : Bool) → A b`.

The non-dependent version is a particular case of the dependent version, by considering the constant type family `λ _ → A` for a given `A : Type`. This time we make the first argument `A` implicit:
```agda
Bool-nondep-elim : {A : Type}
                 → A
                 → A
                 → Bool → A
Bool-nondep-elim {A} = Bool-elim (λ _ → A)
```
This produces a function `Bool → A` from two given elements of the type `A`.

## Logical reading of the eliminator

The *conclusion* of `Bool-elim` is `(b : Bool) → A b`, which under *propositions as types* has the logical reading "for all `b : Bool`, the proposition `A b` holds". The *hypotheses* `A true` and `A false` are all is needed to reach this conclusion.

Thus the logical reading of `Bool-elim` is:

 * In order to prove that "for all `b : Bool`, the proposition `A b` holds"

it is enough to prove that

 * the proposition `A true` holds, and

 * the proposition `A false` holds,

which should be intuitively clear.

## Examples of proofs using the eliminator

First define
```agda
not : Bool → Bool
not true  = false
not false = true
```
Then we can prove that `not` can be expressed using `if-then-else`:
```agda
open import identity-type
not-defined-with-if : (b : Bool) → not b ≡ if b then false else true
not-defined-with-if true  = refl false
not-defined-with-if false = refl true
```
Using the eliminator, this can be proved as follows:
```agda
not-defined-with-if₀ : (b : Bool) → not b ≡ if b then false else true
not-defined-with-if₀ = Bool-elim A x y
 where
  A : Bool → Type
  A b = not b ≡ if b then false else true

  x : A true
  x = refl false

  y : A false
  y = refl true
```
Of course, we can "in-line" the definitions of the `where` clause:
```agda
not-defined-with-if₁ : (b : Bool) → not b ≡ if b then false else true
not-defined-with-if₁ = Bool-elim
                        (λ b → not b ≡ if b then false else true)
                        (refl false)
                        (refl true)
```
This is shorter but probably less readable. The following is even shorter, using the fact that Agda can infer the property `A : Bool → Type` we want to prove automatically. We use `_` to tell Agda "please figure out yourself what this argument in the function has to be":
```agda
not-defined-with-if₂ : (b : Bool) → not b ≡ if b then false else true
not-defined-with-if₂ = Bool-elim _ (refl false) (refl true)
```
In situations where we try to use `_` but Agda can't determine that there is a *unique* answer to what `_` should be, the colour yellow is used to indicate this in the syntax highlighting, accompanied by an error message. To give another example, we first define the notion of an [involution](https://en.wikipedia.org/wiki/Involution_(mathematics)), or involutive function:
```agda
is-involution : {X : Type} → (X → X) → Type
is-involution {X} f = (x : X) → f (f x) ≡ x
```
For example, list reversal is an involution. Another example is boolean negation:
```agda
not-is-involution : is-involution not
not-is-involution = Bool-elim _ (refl true) (refl false)
```
A proof without mentioning `is-involution` and without using the eliminator is also possible, of course:
```agda
not-is-involution' : (b : Bool) → not (not b) ≡ b
not-is-involution' true  = refl true
not-is-involution' false = refl false
```
Very often we will give definitions by pattern-matching as above instead of
`Bool-elim`. But the concept of eliminator for a type remains useful, and it is what `MLTT` (Martin-Löf Type Theory), the foundation of our programming language Agda, uses to define types. Types are defined by formation rules, construtors, eliminators, and equations explaining how the constructors interact with the eliminators. Pattern-matching can be considered as "syntax sugar" for definitions using eliminators. Usually definitions using pattern matching are more readable than definitions using eliminators, but they are equivalent to definitions using eliminators.

Notice that in the definition of `is-involution` we needed to explicitly indicate the implicit argument `X` using curly brackets. Agda allows the notation `∀` in order to be able to omit the type `X`, provided it can be inferred automaticaly, which it can in our situation:
```agda
is-involution' : {X : Type} → (X → X) → Type
is-involution' f = ∀ x → f (f x) ≡ x
```

## Some useful functions

```agda
_&&_ : Bool → Bool → Bool
true  && y = y
false && y = false

_||_ : Bool → Bool → Bool
true  || y = true
false || y = y

infixr 20 _||_
infixr 30 _&&_
```

[Go back to the table of contents](https://martinescardo.github.io/HoTTEST-Summer-School/)
