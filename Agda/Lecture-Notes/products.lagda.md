
[Martin Escardo](Https://www.Cs.Bham.Ac.Uk/~mhe/).
Notes originally written for the module *Advanced Functional Programming* of the [University of Birmingham](https://www.birmingham.ac.uk/index.aspx), UK.


<!--
```agda
{-# OPTIONS --without-K --safe #-}

module products where

open import general-notation
```
-->

# Products

We discuss function types of the form `A → B` (called non-dependent function types) and of the form `(x : A) → B x` (called dependent function types). The latter are also called *products* in type theory and this terminology comes from mathematics.

## The identity function

To *introduce* functions, we use `λ`-abstractions. For example, the identity function can be defined as follows:
<!--
The following trick allows us to check the correctness of alternative definitions without name clashes:
```agda
module _ where
 private
```
-->
```agda
  id : {A : Type} → A → A
  id = λ x → x
```

But of course this function can be equivalently written as follows, which we take as our official definition:
```agda
id : {A : Type} → A → A
id x = x
```

## Logical implication

A logical implication `A → B` is represented by the function type `A → B`, and it is a happy coincidence that both use the same notation.

In terms of logic, the identity function implements the tautology "`A` implies `A`" when we understand the type `A` as a logical proposition. In general, most things we define in Agda have a dual interpretation type/proposition or program/proof, like this example.

The *elimination* principle for function types is given by function application, which is built-in in Agda, but we can explicitly (re)define it. We do with the arguments swapped here:
```agda
modus-ponens : {A B : Type} → A → (A → B) → B
modus-ponens a f = f a
```
[Modus ponens](https://en.wikipedia.org/wiki/Modus_ponens) is the rule logic that says that if the proposition `A` holds and `A` implies `B`, then `B` also holds. The above definition gives a computational realization of this.

## Dependent functions

As already discussed, a dependent function type `(x : A) → B x`, with `A : Type` and `B : A → Type`, is that of functions with input `x` in the type `A` and output in the type `B x`. It is called "dependent" because the output *type* `B x` depends on the input *element* `x : A`.

## Universal quantification

The logical interpretation of `(x : A) → B x` is "for all x : A, B x".
This is because in order to show that this universal quantification holds, we have to show that `B x` holds for each given `x:A`. The input is the given `x : A`, and the output is a justification of `B x`. We will see some concrete examples shortly.

## Dependent function composition

Composition can be defined for "non-dependent functions", as in usual mathematics, and, more generally, with dependent functions. With non-dependent functions, it has the following type and definition:
<!--
```agda
module _ where
 private
```
-->
```agda
  _∘_ : {A B C : Type} → (B → C) → (A → B) → (A → C)
  g ∘ f = λ x → g (f x)
```

In terms of computation, this means "first do f and then do g". For this reason the function composition `g ∘ f` is often read "`g` after `f`". In terms of logic, this implements "If B implies C and also A implies B, then A implies C".

With dependent types, it has the following more general type but the same definition, which is the one we adopt:

```agda
_∘_ : {A B : Type} {C : B → Type}
    → ((y : B) → C y)
    → (f : A → B)
    → (x : A) → C (f x)
g ∘ f = λ x → g (f x)
```

Its computational interpretation is the same, "first do f and then do g", but its logical understanding changes: "If it is the case that for all y : B we have that C y holds, and we have a function f : A → B, then it is also the case that for all x : A, we have that C (f x) holds".

## `Π` notation

We have mentioned in the [propositions as types table](curry-howard.lagda) that the official notation in MLTT for the dependent function type uses `Π`, the Greek letter Pi, for *product*. We can, if we want, introduce the same notation in Agda, using a `syntax` declaration:
```agda
Pi : (A : Type) (B : A → Type) → Type
Pi A B = (x : A) → B x

syntax Pi A (λ x → b) = Π x ꞉ A , b
```
**Important.** We are using the alternative symbol `꞉` (typed "`\:4`" in the emacs mode for Agda), which is different from the reserved symbol "`:`". We will use the same alternative symbol when we define syntax for the sum type `Σ`.

Notice that, for some reason, Agda has this kind of definition backwards. The end result of this is that now `(x : A) → B x` can be written as `Π x ꞉ A , B x` in Agda as in type theory. (If you happen to know a bit of maths, you may be familiar with the [cartesian product of a family of sets](https://en.wikipedia.org/wiki/Cartesian_product#Infinite_Cartesian_products), and this is the reason the letter `Π` is used.)

[Go back to the table of contents](https://martinescardo.github.io/HoTTEST-Summer-School/)
