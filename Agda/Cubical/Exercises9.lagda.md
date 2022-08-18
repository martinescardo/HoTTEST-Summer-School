# Week 9 - Cubical Agda Exercises

## Standard disclaimer:

**The exercises are designed to increase in difficulty so that we can cater to
our large and diverse audience. This also means that it is *perfectly fine* if
you don't manage to do all exercises: some of them are definitely a bit hard for
beginners and there are likely too many exercises! You *may* wish to come back
to them later when you have learned more.**

Having said that, here we go!

In case you haven't done the other Agda exercises:
This is a markdown file with Agda code, which means that it displays nicely on
GitHub, but at the same time you can load this file in Agda and fill the holes
to solve exercises.

**When solving the problems,
please make a copy of this file to work in, so that it doesn't get overwritten
(in case we update the exercises through `git`)!**


```agda
{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Exercises9 where

open import cubical-prelude
open import Lecture7-notes
open import Lecture8-notes
open import Lecture9-notes
open import Solutions7 hiding (rUnit)
open import Solutions8
open import Lecture9-live using (SemiGroupℕ)
```

## Part I: More hcomps

### Exercise 1 (★★)
### (a)
Show the left cancellation law for path composition using an hcomp.
Hint: one hcomp should suffice. Use `comp-filler` and connections

```agda
lUnit : {A : Type ℓ} {x y : A} (p : x ≡ y) → refl ∙ p ≡ p
lUnit = {!!}

```
### (b)
Try to mimic the construction of lUnit for rUnit (i.e. redefine it)
in such a way that `rUnit refl ≡ lUnit refl` holds by `refl`.
Hint: use (almost) the exact same hcomp.

```agda
rUnit : {A : Type ℓ} {x y : A} (p : x ≡ y) → p ∙ refl ≡ p
rUnit = {!!}

-- uncomment to see if it type-checks

{-
rUnit≡lUnit : ∀ {ℓ} {A : Type ℓ} {x : A} → rUnit (refl {x = x}) ≡ lUnit refl
rUnit≡lUnit = refl
-}

```


### Exercise 2 (★★)
Show the associativity law for path composition
Hint: one hcomp should suffice. This one can be done without connections
  (but you might need comp-filler in more than one place)

```agda
assoc : {A : Type ℓ} {x y z w : A} (p : x ≡ y) (q : y ≡ z) (r : z ≡ w)
  → p ∙ (q ∙ r) ≡ (p ∙ q) ∙ r
assoc = {!!}

```

### Exercise 3 (Master class in connections) (🌶)
The goal of this exercise is to give a cubical proof of the Eckmann-Hilton argument,
which says that path composition for higher loops is commutative

(a) While we cannot get `p ∙ q ≡ q ∙ p` as a one-liner, we can get a
one-liner showing that the identiy holds up to some annoying
coherences.  Try to understand the following statement (and why it's
well-typed). After that, fill the holes

Hint: each hole will need a `∨` or a `∧`

```agda
pre-EH : {A : Type ℓ} {x : A} (p q : refl {x = x} ≡ refl)
  → ap (λ x → x ∙ refl) p ∙ ap (λ x → refl ∙ x) q
   ≡ ap (λ x → refl ∙ x) q ∙ ap (λ x → x ∙ refl) p
pre-EH {x = x} p q i = (λ j → p {!!} ∙ q {!!})
                     ∙ (λ j → p {!!} ∙ q {!!})

```
(b) If we manage to cancel out all of the annoying aps, we get Eckmann-Hilton:
For paths (p q : refl ≡ refl), we have p ∙ q ≡ q ∙ p. Try to prove this, using the above lemma.

Hint: Use the pre-EH as the bottom of an hcomp (one should be enough).
For the sides, use lUnit and rUnit wherever they're needed. Note that this will only work out smoothly if
you've solved Exercise 1 (b).

```agda
Eckmann-Hilton : {A : Type ℓ} {x : A} (p q : refl {x = x} ≡ refl) → p ∙ q ≡ q ∙ p
Eckmann-Hilton = {!!}

```
# Part 2: Binary numbers as a HIT
Here is another HIT describing binary numbers. The idea is that a binary number is a list of booleans, modulo trailing zeros.

For instance, `true ∷ true ∷ true ∷ []` is the binary number 110 ...
... and so is `true ∷ true ∷ false ∷ false ∷ false ∷ []`

(!) Note that we're interpreting 110 as 1·2⁰ + 1·2¹ + 0·2² here.

```agda
0B = false
1B = true

data ListBin : Type where
  []    : ListBin
  _∷_   : (x : Bool) (xs : ListBin) → ListBin
  drop0 : 0B ∷ [] ≡ []

-- 1 as a binary number
1LB : ListBin
1LB = 1B ∷ []
```
### Exercise 4 (★)
Define the successor function on ListBin
```agda

sucListBin : ListBin → ListBin
sucListBin = {!!}

```
### Exercise 5 (★★)
Define an addition `+LB` on ListBin and prove that `x +LB [] ≡ x`
Do this by mutual induction! Make sure the three cases for the right unit law hold by refl.
```agda

_+LB_ : ListBin → ListBin → ListBin
rUnit+LB : (x : ListBin) → x +LB [] ≡ x
x +LB y = {!!}
rUnit+LB = {!!}

```
(c) Prove that sucListBin is left distributive over `+LB`
Hint: If you pattern match deep enough, there should be a lot of refls...
```agda

sucListBinDistrL : (x y : ListBin) → sucListBin (x +LB y) ≡ (sucListBin x +LB y)
sucListBinDistrL = {!!}
```

### Exercise 6 (★)
Define a map `LB→ℕ : ListBin → ℕ` and show that it preserves addition

```agda
ℕ→ListBin : ℕ → ListBin
ℕ→ListBin = {!!}

ℕ→ListBin-pres+ : (x y : ℕ) → ℕ→ListBin (x + y) ≡ (ℕ→ListBin x +LB ℕ→ListBin y)
ℕ→ListBin-pres+ = {!!}

```

### Exercise 7 (★★★)
Show that `ℕ ≃ ListBin`.

```agda

ListBin→ℕ : ListBin → ℕ
ListBin→ℕ = {!!}

ListBin→ℕ→ListBin : (x : ListBin) → ℕ→ListBin (ListBin→ℕ x) ≡ x
ListBin→ℕ→ListBin = {!!}

ℕ→ListBin→ℕ : (x : ℕ) → ListBin→ℕ (ℕ→ListBin x) ≡ x
ℕ→ListBin→ℕ = {!!}

ℕ≃ListBin : ℕ ≃ ListBin
ℕ≃ListBin = {!!}

```
# Part 3: The SIP
### Exericise 8 (★★)
Show that, using an SIP inspired argument, if `(A , _+A_)` is a semigroup and `(B , _+B_)` is some other type with a composition satisfying:

(i) `e : A ≃ B`

(ii) `((x y : A) → e (x +A y) ≡ e x +B e y`

then `(B , _+B_)` defines a semigroup.

Conclude that `(ListBin , _+LB_)` is a semigroup

For inspiration, see Lecture9-notes
```agda

SemiGroupListBin : SemiGroup ListBin
SemiGroupListBin = {!!}
