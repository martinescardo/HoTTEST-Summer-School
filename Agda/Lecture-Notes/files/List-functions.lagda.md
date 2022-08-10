
[Martin Escardo](Https://www.Cs.Bham.Ac.Uk/~mhe/).
Notes originally written for the module *Advanced Functional Programming* of the [University of Birmingham](https://www.birmingham.ac.uk/index.aspx), UK.


<!--
```agda
{-# OPTIONS --without-K --safe #-}

module List-functions where

open import prelude
```
-->
# Some functions on lists

## Length, concatenation, map and singleton lists

```agda
open import List
open import natural-numbers-type

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
```

## Properties of list concatenation

```agda
[]-left-neutral : {X : Type} (xs : List X) → [] ++ xs ≡ xs
[]-left-neutral = refl

[]-right-neutral : {X : Type} (xs : List X) → xs ++ [] ≡ xs
[]-right-neutral []        = refl []
[]-right-neutral (x :: xs) =
   (x :: xs) ++ [] ≡⟨ refl _ ⟩
   x :: (xs ++ []) ≡⟨ ap (x ::_) ([]-right-neutral xs) ⟩
   x :: xs         ∎

++-assoc : {A : Type} (xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc []        ys zs = refl (ys ++ zs)
++-assoc (x :: xs) ys zs =
   ((x :: xs) ++ ys) ++ zs ≡⟨ refl _ ⟩
   x :: ((xs ++ ys) ++ zs) ≡⟨ ap (x ::_) (++-assoc xs ys zs) ⟩
   x :: (xs ++ (ys ++ zs)) ≡⟨ refl _ ⟩
   (x :: xs) ++ ys ++ zs   ∎
```

Short proofs:
```agda
[]-right-neutral' : {X : Type} (xs : List X) → xs ++ [] ≡ xs
[]-right-neutral' []        = refl []
[]-right-neutral' (x :: xs) = ap (x ::_) ([]-right-neutral' xs)

++-assoc' : {A : Type} (xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc' []        ys zs = refl (ys ++ zs)
++-assoc' (x :: xs) ys zs = ap (x ::_) (++-assoc' xs ys zs)
```

## List reversal

First an obvious, but slow reversal algorithm:
```agda
reverse : {A : Type} → List A → List A
reverse []        = []
reverse (x :: xs) = reverse xs ++ [ x ]
```
This is quadratic time. To get a linear-time algorithm, we use the following auxiliary function:
```agda
rev-append : {A : Type} → List A → List A → List A
rev-append []        ys = ys
rev-append (x :: xs) ys = rev-append xs (x :: ys)
```
The intended behaviour of `rev-append` is that `rev-append xs ys = reverse xs ++ ys`.
Using this fact, the linear time algorithm is the following:
```agda
rev : {A : Type} → List A → List A
rev xs = rev-append xs []
```
We now want to show that `rev` and `reverse` behave in the same way. To do this, we first show that the auxiliary function does behave as intended:
```agda
rev-append-behaviour : {A : Type} (xs ys : List A)
                     → rev-append xs ys ≡ reverse xs ++ ys
rev-append-behaviour []        ys = refl ys
rev-append-behaviour (x :: xs) ys =
   rev-append (x :: xs) ys     ≡⟨ refl _ ⟩
   rev-append xs (x :: ys)     ≡⟨ rev-append-behaviour xs (x :: ys) ⟩
   reverse xs ++ (x :: ys)     ≡⟨ refl _ ⟩
   reverse xs ++ ([ x ] ++ ys) ≡⟨ sym (++-assoc (reverse xs) [ x ] ys) ⟩
   (reverse xs ++ [ x ]) ++ ys ≡⟨ refl _ ⟩
   reverse (x :: xs) ++ ys     ∎
```
We state this as follows in Agda:
```agda
rev-correct : {A : Type} (xs : List A) → rev xs ≡ reverse xs
rev-correct xs =
   rev xs           ≡⟨ refl _ ⟩
   rev-append xs [] ≡⟨ rev-append-behaviour xs [] ⟩
   reverse xs ++ [] ≡⟨ []-right-neutral (reverse xs) ⟩
   reverse xs       ∎
```

[Go back to the table of contents](https://martinescardo.github.io/HoTTEST-Summer-School/)
