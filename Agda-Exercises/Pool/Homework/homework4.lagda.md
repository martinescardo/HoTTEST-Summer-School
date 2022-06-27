# Week 4 - Homework Sheet

**Please finish the lab sheet before moving on to these exercises.**

```agda
{-# OPTIONS --without-K --safe #-}
module Pool.Homework.homework4 where

open import prelude
open import List-functions hiding (++-assoc)
```

## Part I: Commutativity of addition of natural numbers

We wish to prove the commutativity of `_+_` on the natural numbers.

The following proof skeleton has been provided for you, using
[notation for equational reasoning](https://git.cs.bham.ac.uk/mhe/afp-learning/-/blob/main/files/LectureNotes/files/identity-type.lagda.md#notation-for-equality-reasoning).

```agda
+-comm : (x y : ℕ) → x + y ≡ y + x
+-comm 0       0       = {!!}
+-comm 0       (suc y) = {!!}
+-comm (suc x) 0       = {!!}
+-comm (suc x) (suc y)
 = suc (x + suc y)     ≡⟨ {!!} ⟩
   suc (suc (y + x))   ≡⟨ {!!} ⟩
   suc (suc x + y)     ≡⟨ {!!} ⟩
   suc (y + suc x)     ∎
```

**Fill** the holes of our proof that `_+_` is commutative.

## Part II: Prefixes of lists

In this part we will study two ways of expressing that a list is prefix of
another list.

This will be similar to how we had two ways of expressing less-than-or-equal
`≤` on natural numbers, as seen in the Lab Sheet for Week 4. In particular,
you will notice how to the structure of the proofs below mirror the structure
of the proofs in this week's Lab Sheet.

The first definition is an inductive one.

```agda
data _≼_ {X : Type} : List X → List X → Type where
 []-is-prefix : (xs : List X) → [] ≼ xs
 ::-is-prefix : (x : X) (xs ys : List X)
              → xs ≼ ys → (x :: xs) ≼ (x :: ys)
```

It says:
1. that the empty list is a prefix of any list;
1. if `xs` is a prefix of `ys`, then `x :: xs` is a prefix of `x :: ys`.

The second item says that you can extend prefixes by adding the same element at
the start.

The second definition uses a `Σ`-type.

```agda
_≼'_ : {X : Type} → List X → List X → Type
_≼'_ {X} xs ys = Σ zs ꞉ List X , xs ++ zs ≡ ys
```

It says that `xs` is a prefix of `ys` if we have another list `zs` such that
`xs ++ zs ≡ ys`. In other words, `xs` can be extended to `ys.`

### Examples

Here are some examples of prefixes of lists.

```agda
≼'-example₀ : [] ≼' (1 :: 2 :: [ 3 ])
≼'-example₀ = ((1 :: 2 :: [ 3 ]) , refl (1 :: 2 :: [ 3 ]))

≼'-example₁ : [ 1 ] ≼' (1 :: [ 2 ])
≼'-example₁ = ([ 2 ] , refl (1 :: [ 2 ]))

≼'-example₂ : (7 :: [ 3 ]) ≼' (7 :: 3 :: 4 :: [ 9 ])
≼'-example₂ = ((4 :: [ 9 ]) , refl (7 :: 3 :: 4 :: [ 9 ]))
```

For comparison, here are some examples using `≼` instead of `≼'`.

```agda
≼-example₀ : [] ≼ (1 :: 2 :: [ 3 ])
≼-example₀ = []-is-prefix (1 :: 2 :: [ 3 ])

≼-example₁ : [ 1 ] ≼ (1 :: [ 2 ])
≼-example₁ = ::-is-prefix 1 [] [ 2 ]
                          ([]-is-prefix [ 2 ])

≼-example₂ : (7 :: [ 3 ]) ≼ (7 :: 3 :: 4 :: [ 9 ])
≼-example₂ = ::-is-prefix 7 [ 3 ] (3 :: 4 :: [ 9 ])
                          (::-is-prefix 3 [] (4 :: [ 9 ])
                                          ([]-is-prefix (4 :: [ 9 ])))
```

Notice how we build up the proofs by consecutive uses of `::-is-prefix`,
finishing with `[]-is-prefix`. This reflects the inductive definition of `≼`.

We will prove that `x ≼ y` and `x ≼' y` are logically equivalent, but first we
include a useful exercise on associativity.

### Exercise 2.1

**Prove** that concatenation of lists, `++`, is associative.

```agda
++-assoc : {X : Type} (xs ys zs : List X)
         → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc = {!!}
```

### Exercise 2.2

**Complete** the holes in the equational reasoning below to prove that `≼'` is
transitive.

```agda
≼'-is-transitive : {X : Type} (xs ys zs : List X)
                 → xs ≼' ys → ys ≼' zs → xs ≼' zs
≼'-is-transitive xs ys zs (l , e) (l' , e') = ((l ++ l') , e'')
 where
  e'' : xs ++ l ++ l' ≡ zs
  e'' = xs ++ (l ++ l') ≡⟨ {!!} ⟩
        (xs ++ l) ++ l' ≡⟨ {!!} ⟩
        ys ++ l'        ≡⟨ {!!} ⟩
        zs              ∎
```

### Exercise 2.3

**Prove** the following about `≼`.

```agda
≼-++ : {X : Type} (xs ys : List X) → xs ≼ (xs ++ ys)
≼-++ [] ys        = {!!}
≼-++ (x :: xs) ys = {!!}
```

### Exercise 2.4

**Complete** the function below, showing that we can go from `≼'` to `≼`.

*Hint*: Use `≼-++`.

```agda
≼-unprime : {X : Type} (xs ys : List X) → xs ≼' ys → xs ≼ ys
≼-unprime = {!!}
```

### Exercise 2.5

**Prove** the following facts about `≼'`.

```agda
≼'-[] : {X : Type} (xs : List X) → [] ≼' xs
≼'-[] = {!!}

≼'-cons : {X : Type} (x : X) (xs ys : List X)
        → xs ≼' ys
        → (x :: xs) ≼' (x :: ys)
≼'-cons x xs ys (zs , e) = {!!}
```

Note that these amount to the constructors of `≼`.

### Exercise 2.6

**Complete** the function below, showing that we can go from `≼` to `≼'`.

*Hint*: Use `≼'-[]` and `≼'-cons`.

```agda
≼-prime : {X : Type} (xs ys : List X) → xs ≼ ys → xs ≼' ys
≼-prime = {!!}
```

### Exercise 2.7

Using the functions `≼-unprime` and `≼-prime`, and the fact that `≼'` is
transitive, **prove** that `≼` is transitive too.

```agda
≼-is-transitive : {X : Type} (xs ys zs : List X)
                → xs ≼ ys → ys ≼ zs → xs ≼ zs
≼-is-transitive = {!!}
```
