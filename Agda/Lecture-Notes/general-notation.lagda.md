
Martin Escardo.
Notes originally written for the module "Advanced Functional Programming"
at the School of Computer Science of the University of Birmingham, UK.


# General notation

The option `--without-K` will be explained later (it concerns the identity type). The option `--safe` disables experimental features of Agda that may make it *inconsistent*, that is, allow to prove false statements such as `0 = 1`.

```agda
{-# OPTIONS --without-K --safe #-}
```

Any Agda file is a module with the same name as the file.

```agda
module general-notation where
```

Agda calls types `sets` by default, but we prefer to refer to them by their traditional name.

```agda
Type  = Set
Type₁ = Set₁
```
The following functions allow us to extract the type of an element of a type, and the domain and codomain of a function. We don't need them very often, but they are handy when Agda can't infer types from the context, or simply when the names of the types in question are not available in the scope of a definition:
```agda
type-of : {X : Type} → X → Type
type-of {X} x = X

domain : {X Y : Type} → (X → Y) → Type
domain {X} {Y} f = X

codomain : {X Y : Type} → (X → Y) → Type
codomain {X} {Y} f = Y

_$_ : {A B : Type} → (A → B) → A → B
f $ x = f x

infixr 0 _$_
```
