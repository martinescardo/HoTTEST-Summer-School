
[Martin Escardo](Https://www.Cs.Bham.Ac.Uk/~mhe/).
Notes originally written for the module *Advanced Functional Programming* of the [University of Birmingham](https://www.birmingham.ac.uk/index.aspx), UK.

<!--
```agda
{-# OPTIONS --cubical-compatible --safe #-}

module introduction where
```

**Warning for maintainers of the lecture notes**. This module should not be imported from any module other than natural-numbers-type.lagda.md. The reason the import is needed there is that the pragma {-# BUILTIN NATURAL ℕ #-} cannot be used in two modules, but the build of these lecture notes requires importing all files.

-->
# Introduction to Agda

Everything defined and briefly discussed in this introduction will be redefined and discussed in more detail in other handouts.

## Initial examples of types in Agda

<!--
In Agda, types are called sets by default. For the purposes of HoTT/UF, we prefer to stick to "Type".
```agda
Type = Set
```
-->

Here are some examples of types:


```agda
data Bool : Type where
 true false : Bool

data ℕ : Type where
 zero : ℕ
 suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

data List (A : Type) : Type where
 []   : List A
 _::_ : A → List A → List A

infixr 10 _::_
```

The pragma `BUILTIN NATURAL` is to get syntax sugar to be able to write 0,1,2,3,... rather than the more verbose

 * zero
 * suc zero
 * suc (suc zero)
 * suc (suc (suc zero))
 * ⋯

We pronounce `suc` as "successor".

## Examples of definitions using the above types

```agda
not : Bool → Bool
not true  = false
not false = true

_&&_ : Bool → Bool → Bool
true  && y = y
false && y = false

_||_ : Bool → Bool → Bool
true  || y = true
false || y = y

infixr 20 _||_
infixr 30 _&&_

if_then_else_ : {A : Type} → Bool → A → A → A
if true  then x else y = x
if false then x else y = y

_+_ : ℕ → ℕ → ℕ
zero  + y = y
suc x + y = suc (x + y)

_*_ : ℕ → ℕ → ℕ
zero  * y = 0
suc x * y = x * y + y

infixr 20 _+_
infixr 30 _*_

sample-list₀ : List ℕ
sample-list₀ = 1 :: 2 :: 3 :: []

sample-list₁ : List Bool
sample-list₁ = true || false && true :: false :: true :: true :: []

length : {A : Type} → List A → ℕ
length []        = 0
length (x :: xs) = 1 + length xs

_++_ : {A : Type} → List A → List A → List A
[]        ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

infixr 20 _++_
```

## More sophisticated examples of types in Agda

Sometimes we may wish to consider lists over a type `A` of a given length `n : ℕ`. The elements of this type, written `Vector A n`, are called *vectors*, and the type can be defined as follows:

```agda
data Vector (A : Type) : ℕ → Type where
 []   : Vector A 0
 _::_ : {n : ℕ} → A → Vector A n → Vector A (suc n)
```
This is called a *dependent type* because it is a type that depends on *elements* `n` of another type, namely `ℕ`.

In Agda, we can't define the `head` and `tail` functions on lists, because they are undefined for the empty list, and functions must be total in Agda. Vectors solve this problem:

```agda
head : {A : Type} {n : ℕ} → Vector A (suc n) → A
head (x :: xs) = x

tail : {A : Type} {n : ℕ} → Vector A (suc n) → Vector A n
tail (x :: xs) = xs
```
Agda accepts the above definitions because it knows that the input vector has at least one element, and hence does have a head and a tail. Here is another example.

Dependent types are pervasive in Agda.

## The empty type and the unit type

A type with no elements can be defined as follows:
```agda
data 𝟘 : Type where
```
We will also need the type with precisely one element, which we define as follows:
```agda
data 𝟙 : Type where
 ⋆ : 𝟙
```

Here is an example of a dependent type defined using the above types:
```agda
_≣_ : ℕ → ℕ → Type
0     ≣ 0     = 𝟙
0     ≣ suc y = 𝟘
suc x ≣ 0     = 𝟘
suc x ≣ suc y = x ≣ y

infix 0 _≣_
```
The idea of the above definition is that `x ≣ y` is a type which either has precisely one element, if `x` and `y` are the same natural number, or else is empty, if `x` and `y` are different.
The following definition says that for any natural number `x` we can find an element of the type `x ≣ x`.
```agda
ℕ-refl : (x : ℕ) → x ≣ x
ℕ-refl 0       = ⋆
ℕ-refl (suc x) = ℕ-refl x
```
## The identity type former `_≡_`

It is possible to generalize the above definition
for any type in place of that of natural numbers as follows:
```agda
data _≡_ {A : Type} : A → A → Type where
 refl : (x : A) → x ≡ x

infix 0 _≡_
```
Here are some functions we can define with the identity type:
```agda
trans : {A : Type} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans (refl x) (refl x) = refl x

sym : {A : Type} {x y : A} → x ≡ y → y ≡ x
sym (refl x) = refl x

ap : {A B : Type} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
ap f (refl x) = refl (f x)
```

The identity type is a little bit subtle and there is a lot to say about it.
For the moment, let's convince ourselves that we can convert back and forth between the types `x ≡ y` and `x ≣ y`, in the case that `A` is the type of natural numbers, as follows:

```agda
back : (x y : ℕ) → x ≡ y → x ≣ y
back x x (refl x) = ℕ-refl x

forth : (x y : ℕ) → x ≣ y → x ≡ y
forth 0       0       ⋆ = refl 0
forth (suc x) (suc y) p = I
 where
  IH : x ≡ y
  IH = forth x y p

  I : suc x ≡ suc y
  I = ap suc IH
```

## Propositions as types

The [CurryHoward interpretation of logic](https://en.wikipedia.org/wiki/Curry%E2%80%93Howard_correspondence), after [Haskell Curry](https://en.wikipedia.org/wiki/Haskell_Curry) and [William Howard](https://en.wikipedia.org/wiki/William_Alvin_Howard), interprets logical statements, also known as propositions, as *types*. [Per Martin-Löf](https://en.wikipedia.org/wiki/Per_Martin-L%C3%B6f) extended this interpretation of propositions as types with equality, by introducing the identity type discussed above.

An incomplete table of the CurryHoward--Martin-Löf interpretation of logical propositions is the following:

| Proposition  | Type                                  |
| -          | ---                                   |
| A implies B  | function type A → B                   |
| ∀ x : A, B x | dependent function type (x : A) → B x |
| equality     | identity type `_≡_`                   |

This was enough for our examples above.

For more complex examples of reasoning about programs, we need to complete the following table:

| Logic        | English                    | Type          |
| -          | ---                        | ---           |
| ¬ A          | not A                      | ?             |
| A ∧ B        | A and B                    | ?             |
| A ∨ B        | A or B                     | ?             |
| A → B        | A implies B                | A → B         |
| ∀ x : A, B x | for all x:A, B x           | (x : A) → B x |
| ∃ x : A, B x | there is x:A such that B x | ?             |
| x = y        | x equals y                 | x ≡ y         |

This will be the subject of future handouts.

## Agda manual

Please study the [Agda manual](https://agda.readthedocs.io/en/latest/) as a complement to these lecture notes.

[Go back to the table of contents](https://martinescardo.github.io/HoTTEST-Summer-School/)
