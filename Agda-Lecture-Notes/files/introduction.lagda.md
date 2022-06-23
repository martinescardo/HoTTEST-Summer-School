--
Martin Escardo
Notes originally written for the module "Advanced Functional Programming"
at the School of Computer Science of the University of Birmingham, UK.
--

<!--
```agda
{-# OPTIONS --without-K --safe #-}

module introduction where
```
-->
# Introduction to Advanced Functional Programming

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

## Examples definitions using the above types in Agda

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

map : {A B : Type} → (A → B) → List A → List B
map f []        = []
map f (x :: xs) = f x :: map f xs

[_] : {A : Type} → A → List A
[ x ] = x :: []

reverse : {A : Type} → List A → List A
reverse []        = []
reverse (x :: xs) = reverse xs ++ [ x ]

rev-append : {A : Type} → List A → List A → List A
rev-append []        ys = ys
rev-append (x :: xs) ys = rev-append xs (x :: ys)

rev : {A : Type} → List A → List A
rev xs = rev-append xs []
```

The function `reverse` is slow for large lists as it runs in quadratic
time, but the function `rev` is much faster as it runs in linear
time. Although the algorithm for `reverse` is simple and clear, that
for `rev` is slightly more complicated, and so perhaps we would like
to make sure that we didn't make a mistake, by proving that `reverse
xs` and `rev xs` are equal. We will do that later.

## More sophisticated examples of types in Agda

Sometimes we may wish to consider lists over a type `A` of a given length `n : ℕ`. The elements of this type, written `Vector A n`, are called *vectors*, and the type can be defined as follows:

```agda
data Vector (A : Type) : ℕ → Type where
 []   : Vector A 0
 _::_ : {n : ℕ} → A → Vector A n → Vector A (suc n)
```
This is called a *dependent type* because it is a type that depends on *elements* `n` of another type, namely `ℕ`.

In Agda, we can't define the `head` and `tail` functions on lists, because types don't have
`undefined` elements like in Haskell, which would be needed for the head and tail of the empty list. Vectors solve this problem:

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

The [Curry--Howard interpretation of logic](https://en.wikipedia.org/wiki/Curry%E2%80%93Howard_correspondence), after [Haskell Curry](https://en.wikipedia.org/wiki/Haskell_Curry) and [William Howard](https://en.wikipedia.org/wiki/William_Alvin_Howard), interprets logical statements, also known as propositions, as *types*. [Per Martin-Löf](https://en.wikipedia.org/wiki/Per_Martin-L%C3%B6f) extended this interpretation of propositions as types with equality, by introducing the identity type discussed above.

An incomplete table of the Curry--Howard--Martin-Löf interpretation of logical propositions is the following:

| Proposition  | Type                                  |
| ---          | ---                                   |
| A implies B  | function type A → B                   |
| ∀ x : A, B x | dependent function type (x : A) → B x |
| equality     | identity type `_≡_`                   |

This fragment of logic was enough for us to be able to write the correctness of `rev` as the type

> `{A : Type} (xs : List A) → rev xs ≡ reverse xs`

which we can read as

> for any type `A` and any list `xs`, we have that `rev xs = reverse xs`,

or, using logical symbolism,

> `∀ A : Type, ∀ xs : List A, rev xs = reverse xs`.

For more complex examples of reasoning about programs, we need to complete the following table:

| Logic        | English                    | Type          |
| ---          | ---                        | ---           |
| ¬ A          | not A                      | ?             |
| A ∧ B        | A and B                    | ?             |
| A ∨ B        | A or B                     | ?             |
| A → B        | A implies B                | A → B         |
| ∀ x : A, B x | for all x:A, B x           | (x : A) → B x |
| ∃ x : A, B x | there is x:A such that B x | ?             |
| x = y        | x equals y                 | x ≡ y         |

This will be the subject of future handouts.

## Proofs as (functional) programs

Notice that we didn't write a *proof*, in the usual mathematical sense, of the statement

> for any type `A` and any list `xs`, we have that `rev xs = reverse xs`.

We instead wrote a *program* of type

> {A : Type} (xs : List A) → rev xs ≡ reverse xs

This is precisely the point of "propositions as types": proofs become functional programs. You may not know a lot (or even anything) about proofs, but you certainly know a lot about functional programming. The interpretation of logical statements as types allows you to apply your expertise as a functional programmer to write (rigorous) proofs checked by the computer.

> If your Agda program compiles without errors, your proof, written as a program, is correct!

The computer checks your proof for you. A proof is nothing but a functional program.

## Is Agda unique in being able to express both programs and logical statements?

No, for example, there are also [Coq](https://coq.inria.fr/) and [Lean](https://leanprover.github.io/) among many others.

## Agda manual

Please study the [Agda manual](https://agda.readthedocs.io/en/latest/) as a complement to these lecture notes.
