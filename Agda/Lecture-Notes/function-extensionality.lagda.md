
[Martin Escardo](Https://www.Cs.Bham.Ac.Uk/~mhe/).
Notes originally written for the module [Advanced Functional Programmin](https://program-and-modules-handbook.bham.ac.uk/webhandbooks/WebHandbooks-control-servlet?Action=getModuleDetailsList"Advanced Functional Programming"pgSubj=06"Advanced Functional Programming"pgCrse=35309"Advanced Functional Programming"searchTerm=002024)
at the [School of Computer Science](https://www.birmingham.ac.uk/schools/computer-science/index.aspx) of the [University of Birmingham](https://www.birmingham.ac.uk/index.aspx), UK.


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

[Go back to the table of contents](https://martinescardo.github.io/HoTTEST-Summer-School/)
