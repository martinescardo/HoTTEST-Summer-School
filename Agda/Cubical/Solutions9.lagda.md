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

module Solutions9 where

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
lUnit {x = x} {y = y} p i j =
  hcomp (λ k → λ {(i = i0) → comp-filler refl p k j
                 ; (i = i1) → p (k ∧ j)
                 ; (j = i0) → x
                 ; (j = i1) → p k})
        x


```
### (b)
Try to mimic the construction of lUnit for rUnit (i.e. redefine it)
in such a way that `rUnit refl ≡ lUnit refl` holds by `refl`.
Hint: use (almost) the exact same hcomp.

```agda
rUnit : {A : Type ℓ} {x y : A} (p : x ≡ y) → p ∙ refl ≡ p
rUnit {x = x} {y = y} p i j =
  hcomp (λ k → λ {(i = i0) → comp-filler p refl k j
                 ; (i = i1) → p j
                 ; (j = i0) → x
                 ; (j = i1) → y})
        (p j)

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
assoc {x = x} {y = y} p q r i j =
  hcomp (λ k → λ {(i = i0) → (p ∙ comp-filler q r k) j
                 ; (i = i1) → comp-filler (p ∙ q) r k j
                 ; (j = i0) → x
                 ; (j = i1) → r k})
        ((p ∙ q) j)

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
pre-EH {x = x} p q i = (λ j → p (~ i ∧ j) ∙ q (i ∧ j))
                     ∙ (λ j → p (~ i ∨ j) ∙ q (i ∨ j))

```
(b) If we manage to cancel out all of the annoying aps, we get Eckmann-Hilton:
For paths (p q : refl ≡ refl), we have p ∙ q ≡ q ∙ p. Try to prove this, using the above lemma.

Hint: Use the pre-EH as the bottom of an hcomp (one should be enough).
For the sides, use lUnit and rUnit wherever they're needed. Note that this will only work out smoothly if
you've solved Exercise 1 (b).

```agda
Eckmann-Hilton : {A : Type ℓ} {x : A} (p q : refl {x = x} ≡ refl) → p ∙ q ≡ q ∙ p
Eckmann-Hilton {x = x} p q k i =
  hcomp (λ r → λ {(i = i0) → rUnit (refl {x = x}) r
                 ; (i = i1) → rUnit (refl {x = x}) r
                 ; (k = i0) → ((λ j → rUnit (p j) r) ∙ (λ j → lUnit (q j) r)) i
                 ; (k = i1) → ((λ j → lUnit (q j) r) ∙ (λ j → rUnit (p j) r)) i})
        (pre-EH p q k i)

```
# # Part 2: Binary numbers as a HIT
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
sucListBin [] = 1LB
sucListBin (true ∷ xs) = false ∷ sucListBin xs
sucListBin (false ∷ xs) = 1B ∷ xs
sucListBin (drop0 i) = 1LB

```
### Exercise 5 (★★)
Define an addition `+LB` on ListBin and prove that `x +LB [] ≡ x`
Do this by mutual induction! Make sure the three cases for the right unit law hold by refl.
```agda

_+LB_ : ListBin → ListBin → ListBin
rUnit+LB : (x : ListBin) → x +LB [] ≡ x
[] +LB y = y
(x ∷ xs) +LB [] = x ∷ xs
(true ∷ xs) +LB (true ∷ ys) = false ∷ sucListBin (xs +LB ys)
(true ∷ xs) +LB (false ∷ ys) = true ∷ (xs +LB ys)
(false ∷ xs) +LB (y ∷ ys) = y ∷ (xs +LB ys)
(true ∷ xs) +LB drop0 i = true ∷ (rUnit+LB xs i)
(false ∷ xs) +LB drop0 i = false ∷ (rUnit+LB xs i)
drop0 i +LB [] = drop0 i
drop0 i +LB (y ∷ ys) = y ∷ ys
drop0 i +LB drop0 j = drop0 (j ∧ i)
rUnit+LB [] = refl
rUnit+LB (x ∷ x₁) = refl
rUnit+LB (drop0 i) = refl

```
(c) Prove that sucListBin is left distributive over `+LB`
Hint: If you pattern match deep enough, there should be a lot of refls...
```agda

sucListBinDistrL : (x y : ListBin) → sucListBin (x +LB y) ≡ (sucListBin x +LB y)
sucListBinDistrL [] [] = refl
sucListBinDistrL [] (true ∷ y) = refl
sucListBinDistrL [] (false ∷ y) = refl
sucListBinDistrL [] (drop0 i) = refl
sucListBinDistrL (true ∷ xs) [] = refl
sucListBinDistrL (false ∷ xs) [] = refl
sucListBinDistrL (true ∷ xs) (true ∷ y) = ap (1B ∷_) (sucListBinDistrL xs y)
sucListBinDistrL (true ∷ xs) (false ∷ y) = ap (0B ∷_) (sucListBinDistrL xs y)
sucListBinDistrL (false ∷ xs) (true ∷ y) = refl
sucListBinDistrL (false ∷ xs) (false ∷ y) = refl
sucListBinDistrL (true ∷ []) (drop0 i)  = refl
sucListBinDistrL (true ∷ (true ∷ xs)) (drop0 i) = refl
sucListBinDistrL (true ∷ (false ∷ xs)) (drop0 i) = refl
sucListBinDistrL (true ∷ drop0 i) (drop0 j) = refl
sucListBinDistrL (false ∷ xs) (drop0 i) = refl
sucListBinDistrL (drop0 i) [] = refl
sucListBinDistrL (drop0 i) (true ∷ y) = refl
sucListBinDistrL (drop0 i) (false ∷ y) = refl
sucListBinDistrL (drop0 i) (drop0 j) = refl
```

### Exercise 6 (★)
Define a map `LB→ℕ : ListBin → ℕ` and show that it preserves addition

```agda
ℕ→ListBin : ℕ → ListBin
ℕ→ListBin zero = []
ℕ→ListBin (suc x) = sucListBin (ℕ→ListBin x)

ℕ→ListBin-pres+ : (x y : ℕ) → ℕ→ListBin (x + y) ≡ (ℕ→ListBin x +LB ℕ→ListBin y)
ℕ→ListBin-pres+ zero y = refl
ℕ→ListBin-pres+ (suc x) zero =
  ap sucListBin (ap ℕ→ListBin (+-comm x zero))
  ∙ sym (rUnit+LB (sucListBin (ℕ→ListBin x)))
ℕ→ListBin-pres+ (suc x) (suc y) =
  ap sucListBin (ℕ→ListBin-pres+ x (suc y))
   ∙ sucListBinDistrL (ℕ→ListBin x) (sucListBin (ℕ→ListBin y))

```

### Exercise 7 (★★★)
Show that `ℕ ≃ ListBin`.

```agda

-- useful lemma
move4 : (x y z w : ℕ) → (x + y) + (z + w) ≡ (x + z) + (y + w)
move4 x y z w =
  (x + y) + (z + w)   ≡⟨ +-assoc (x + y) z w ⟩
  ((x + y) + z) + w   ≡⟨ ap (_+ w) (sym (+-assoc x y z)
                      ∙ ap (x +_) (+-comm y z)
                      ∙ (+-assoc x z y)) ⟩
  ((x + z) + y) + w   ≡⟨ sym (+-assoc (x + z) y w) ⟩
  ((x + z) + (y + w)) ∎

ListBin→ℕ : ListBin → ℕ
ListBin→ℕ [] = 0
ListBin→ℕ (true ∷ xs) = suc (2 · ListBin→ℕ xs)
ListBin→ℕ (false ∷ xs) = 2 · ListBin→ℕ xs
ListBin→ℕ (drop0 i) = 0

ListBin→ℕ-suc : (x : ListBin) → ListBin→ℕ (sucListBin x) ≡ suc (ListBin→ℕ x)
ListBin→ℕ-suc [] = refl
ListBin→ℕ-suc (true ∷ xs) =
   ap (λ x → x + x) (ListBin→ℕ-suc xs)
 ∙ ap suc (sym (+-suc (ListBin→ℕ xs) (ListBin→ℕ xs)))
ListBin→ℕ-suc (false ∷ xs) = refl
ListBin→ℕ-suc (drop0 i) = refl

x+x-charac : (xs : ListBin) → (xs +LB xs) ≡ (false ∷ xs)
x+x-charac [] = sym drop0
x+x-charac (true ∷ xs) = ap (false ∷_) (ap sucListBin (x+x-charac xs))
x+x-charac (false ∷ xs) = ap (false ∷_) (x+x-charac xs)
x+x-charac (drop0 i) j =
  hcomp (λ k → λ {(i = i0) → false ∷ drop0 (~ j ∨ ~ k)
                 ; (i = i1) → drop0 (~ j)
                 ; (j = i0) → drop0 i
                 ; (j = i1) → false ∷ drop0 (i ∨ ~ k)})
        (drop0 (~ j ∧ i))

suc-x+x-charac : (xs : ListBin) → sucListBin (xs +LB xs) ≡ (true ∷ xs)
suc-x+x-charac xs = ap sucListBin (x+x-charac xs)

ListBin→ℕ→ListBin : (x : ListBin) → ℕ→ListBin (ListBin→ℕ x) ≡ x
ListBin→ℕ→ListBin [] = refl
ListBin→ℕ→ListBin (true ∷ xs) =
    ap sucListBin (ℕ→ListBin-pres+ (ListBin→ℕ xs) (ListBin→ℕ xs)
                ∙ ap (λ x → x +LB x) (ListBin→ℕ→ListBin xs))
  ∙ suc-x+x-charac xs
ListBin→ℕ→ListBin (false ∷ xs) =
    (ℕ→ListBin-pres+ (ListBin→ℕ xs) (ListBin→ℕ xs)
  ∙ (ap (λ x → x +LB x) (ListBin→ℕ→ListBin xs)))
  ∙ x+x-charac xs
ListBin→ℕ→ListBin (drop0 i) = help i
  where
  lem : (refl ∙ refl) ∙ sym drop0 ≡ sym drop0
  lem = ap (_∙ sym drop0) (rUnit refl) ∙  lUnit (sym drop0)

  help : PathP (λ i → [] ≡ drop0 i) ((refl ∙ refl) ∙ sym drop0) refl
  help i j = hcomp (λ k → λ {(i = i0) → lem (~ k) j
                            ; (i = i1) → []
                            ; (j = i0) → []
                            ; (j = i1) → drop0 i})
                   (drop0 (i ∨ ~ j))

ℕ→ListBin→ℕ : (x : ℕ) → ListBin→ℕ (ℕ→ListBin x) ≡ x
ℕ→ListBin→ℕ zero = refl
ℕ→ListBin→ℕ (suc x) =
    ListBin→ℕ-suc (ℕ→ListBin x)
  ∙ ap suc (ℕ→ListBin→ℕ x)

ℕ≃ListBin : ℕ ≃ ListBin
ℕ≃ListBin = isoToEquiv (iso  ℕ→ListBin ListBin→ℕ ListBin→ℕ→ListBin ℕ→ListBin→ℕ)

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


module _ {A B : Type} (SA : SemiGroup A) (e : A ≃ B)
  (_+B_ : B → B → B)
  (hom : (x y : A) → pr₁ e (pr₁ SA x y) ≡ ((pr₁ e x) +B pr₁ e y))
  where
  f = pr₁ e
  f⁻ = invEq e

  _+A_ = pr₁ SA

  SemiGroupSIPAux : SemiGroup B
  SemiGroupSIPAux = substEquiv SemiGroup e SA

  _+B'_ = pr₁ SemiGroupSIPAux

  +B'≡+B : (x y : B) → x +B' y ≡ (x +B y)
  +B'≡+B x y =
    (x +B' y)                                          ≡⟨ transportRefl (f (f⁻ (transport refl x)
                                                                        +A (f⁻ (transport refl y)))) ⟩
    f (f⁻ (transport refl x) +A f⁻ (transport refl y)) ≡⟨ (λ i → f (f⁻ (transportRefl x i)
                                                         +A f⁻ (transportRefl y i))) ⟩
    f (f⁻ x +A f⁻ y)                                   ≡⟨ hom (f⁻ x) (f⁻ y) ⟩
    (f (f⁻ x) +B f (f⁻ y))                             ≡⟨ (λ i → secEq e x i +B secEq e y i) ⟩
    x +B y ∎

  assoc+B : ∀ m n o → m +B (n +B o) ≡ (m +B n) +B o
  assoc+B m n o =
     (m +B (n +B o))          ≡⟨ (λ i → +B'≡+B m (+B'≡+B n o (~ i)) (~ i)) ⟩
     (m +B' (n +B' o))        ≡⟨ pr₂ SemiGroupSIPAux m n o ⟩
     ((m +B' n) +B' o)        ≡⟨ (λ i → +B'≡+B (+B'≡+B m n i) o i) ⟩
     ((m +B n) +B o) ∎

  inducedSemiGroup : SemiGroup B
  inducedSemiGroup = _+B_ , assoc+B

SemiGroupListBin : SemiGroup ListBin
SemiGroupListBin = inducedSemiGroup SemiGroupℕ ℕ≃ListBin _+LB_ ℕ→ListBin-pres+
