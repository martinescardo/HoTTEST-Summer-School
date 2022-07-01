
Martin Escardo.
Notes originally written for the module "Advanced Functional Programming"
at the School of Computer Science of the University of Birmingham, UK.


<!--
```agda
{-# OPTIONS --without-K --safe #-}

module function-extensionality where

open import general-notation
```
-->

# Function extensionality

Recall that we defined pointwise equality `f ∼ g` of functions in the [identity type handout](identity-type.lagda.md).
The principle of function extensionality says that pointwise equal functions are equal and is given by the following type `FunExt`:
```agda
open import identity-type

FunExt = {A : Type} {B : A → Type} {f g : (x : A) → B x} → f ∼ g → f ≡ g
```
Unfortunately, this principle is not provable or disprovable in Agda or MLTT (we say that it is [independent](https://en.wikipedia.org/wiki/Independence_(mathematical_logic))).
But it is provable in [Cubical Agda](https://agda.readthedocs.io/en/latest/language/cubical.html), which is based on Cubical Type Theory and is outside the scope of these lecture notes. Sometimes we will use function extensionality as an explicit assumption.
