
Martin Escardo.
Notes originally written for the module "Advanced Functional Programming"
at the School of Computer Science of the University of Birmingham, UK.


<!--
```agda
{-# OPTIONS --without-K --safe #-}

module unit-type where

open import general-notation
```
-->
## The unit type 𝟙

We now redefine the unit type as a record:
```agda
record 𝟙 : Type where
 constructor
  ⋆

open 𝟙 public
```
In logical terms, we can interpret `𝟙` as "true", because we can always exhibit an element of it, namely `⋆`.
Its elimination principle is as follows:
```agda
𝟙-elim : {A : 𝟙 → Type}
       → A ⋆
       → (x : 𝟙) → A x
𝟙-elim a ⋆ = a
```
In logical terms, this says that it order to prove that a property `A` of elements of the unit type `𝟙` holds for all elements of the type `𝟙`, it is enough to prove that it holds for the element `⋆`. The non-dependent version says that if A holds, then "true implies A".
```agda
𝟙-nondep-elim : {A : Type}
              → A
              → 𝟙 → A
𝟙-nondep-elim {A} = 𝟙-elim {λ _ → A}
```
