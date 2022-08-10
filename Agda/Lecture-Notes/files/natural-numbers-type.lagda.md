
[Martin Escardo](Https://www.Cs.Bham.Ac.Uk/~mhe/).
Notes originally written for the module *Advanced Functional Programming* of the [University of Birmingham](https://www.birmingham.ac.uk/index.aspx), UK.


<!--
```agda
{-# OPTIONS --without-K --safe #-}

module natural-numbers-type where

open import introduction using (ℕ ; zero ; suc) public
open import general-notation
```
-->
# The type `ℕ` of natural numbers

[Recall](introduction.lagda.md) that we defined the type of natural numbers inductively as follows:

```notagda
data ℕ : Type where
 zero : ℕ
 suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}
```

## Elimination principle

The elimination principle for all type formers follow the same pattern: they tell us how to define dependent functions *out* of the given type. In the case of natural numbers, the eliminator gives [primitive recursion](https://encyclopediaofmath.org/wiki/Primitive_recursion). Given a base case `a : A 0` and a step function `f : (k : ℕ) → A k → A (suc k)`, we get a function `h : (n : ℕ) → A n` defined by primitive recursion as follows:
```agda
ℕ-elim : {A : ℕ → Type}
       → A 0
       → ((k : ℕ) → A k → A (suc k))
       → (n : ℕ) → A n
ℕ-elim {A} a f = h
 where
  h : (n : ℕ) → A n
  h 0       = a
  h (suc n) = f n (h n)
```
In usual accounts of primitive recursion outside type theory, one encounters the following particular case of primitive recursion, which is the non-dependent version of the above.
```agda

ℕ-nondep-elim : {A : Type}
              → A
              → (ℕ → A → A)
              → ℕ → A
ℕ-nondep-elim {A} = ℕ-elim {λ _ → A}
```
Notice that this is like `fold` for lists, if you know about this.
There is a further restricted version, which is usually called iteration:
```agda
ℕ-iteration : {A : Type}
            → A
            → (A → A)
            → ℕ → A
ℕ-iteration a f = ℕ-nondep-elim a (λ k x → f x)
```
Intuitively, `ℕ-iteration a f n = f (f (f (⋯ f a)))` where we apply `n` times the function `f` to the element `a`, which sometimes is written `fⁿ(a)` in the literature.

## The induction principle for ℕ

In logical terms, one can see immediately what the type of `ℕ-elim` is: it is simply the [principle of induction on natural numbers](https://en.wikipedia.org/wiki/Mathematical_induction), which says that in order to show that a property `A` holds for all natural numbers, it is enough to show that `A 0` holds (this is called the base case), and that if `A k` holds then so does `A (suc k)` (this is called the induction step). In Agda, in practice, we don't explicitly use this induction principle, but instead write definition recursively, just as we defined the above function `h` recursively.

## Addition and multiplication

As an **exercise**, you may try to define the following functions using some version of the above eliminators instead of using pattern matching and recursion:

```agda
_+_ : ℕ → ℕ → ℕ
0     + y = y
suc x + y = suc (x + y)

_*_ : ℕ → ℕ → ℕ
0     * y = 0
suc x * y = x * y + y

infixr 20 _+_
infixr 30 _*_
```

[Go back to the table of contents](https://martinescardo.github.io/HoTTEST-Summer-School/)
