
[Martin Escardo](Https://www.Cs.Bham.Ac.Uk/~mhe/).
Notes originally written for the module *Advanced Functional Programming* of the [University of Birmingham](https://www.birmingham.ac.uk/index.aspx), UK.


<!--
```agda
{-# OPTIONS --without-K --safe #-}

module identity-type where

open import general-notation
```
-->
# The identity type former `_≡_`

The original and main terminology for the following type is *identity type*, but sometimes it is also called the *equality type*. Sometimes this is also called *propositional equality*, but we will avoid this terminology as it sometimes leads to confusion.
```agda
data _≡_ {A : Type} : A → A → Type where
 refl : (x : A) → x ≡ x

infix 0 _≡_

{-# BUILTIN EQUALITY _≡_ #-}
```

## Elimination principle

The elimination principle for this type, also called `J` in the literature, is defined as follows:
```agda
≡-elim : {X : Type} (A : (x y : X) → x ≡ y → Type)
       → ((x : X) → A x x (refl x))
       → (x y : X) (p : x ≡ y) → A x y p
≡-elim A f x x (refl x) = f x
```
This says that in order to show that `A x y p` holds for all `x y : X` and `p : x ≡ y`, it is enough to show that `A x x (refl x)` holds for all `x : X`.
In the literature, this elimination principle is called `J`. Again, we are not going to use it explicitly, because we can use definitions by pattern matching on `refl`, just as we did for defining it.

We also have the non-dependent version of the eliminator:
```agda
≡-nondep-elim : {X : Type} (A : X → X → Type)
              → ((x : X) → A x x)
              → (x y : X) → x ≡ y → A x y
≡-nondep-elim A = ≡-elim (λ x y _ → A x y)
```
A property of two variables like `A` above is referred to as a *relation*. The assumption `(x : X) → A x x` says that the relation is reflexive. Then the non-dependent version of the principle says that the reflexive relation given by the identity type `_≡_` can always be mapped to any reflexive relation, or we may say that `_≡_` is the smallest reflexive relation on the type `X`.

## Fundamental constructions with the identity type

As an exercise, you may try to rewrite the following definitions to use `≡-nondep-elim` instead of pattern matching on `refl`:
```agda
trans : {A : Type} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans p (refl y) = p

sym : {A : Type} {x y : A} → x ≡ y → y ≡ x
sym (refl x) = refl x

ap : {A B : Type} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
ap f (refl x) = refl (f x)

ap₂ : {A B C : Type} (f : A → B → C) {x x' : A} {y y' : B}
    → x ≡ x' → y ≡ y' → f x y ≡ f x' y'
ap₂ f (refl x) (refl y) = refl (f x y)

transport : {X : Type} (A : X → Type)
          → {x y : X} → x ≡ y → A x → A y
transport A (refl x) a = a
```
We have already seen the first three. In the literature, `ap` is often called `cong`. In logical terms, the last one, often called `subst` in the literature, says that if `x` is equal `y` and `A x` holds, then so does `A y`. That is, we can substitute equals for equals in logical statements.

## HoTT/UF notation

```agda
_∙_ : {A : Type} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
_∙_ = trans

infixl 7 _∙_

_⁻¹ : {A : Type} {x y : A} → x ≡ y → y ≡ x
_⁻¹ = sym

infix  40 _⁻¹

```


## Pointwise equality of functions

It is often convenient to work with *pointwise equality* of functions, defined as follows:
```agda
_∼_ : {A : Type} {B : A → Type} → ((x : A) → B x) → ((x : A) → B x) → Type
f ∼ g = ∀ x → f x ≡ g x

infix 0 _∼_
```

Unfortunately, it is not provable or disprovable in Agda that pointwise equal functions are equal, that is, that `f ∼ g` implies `f ≡ g` (but it is provable in [Cubical Agda](https://agda.readthedocs.io/en/latest/language/cubical.html), which is outside the scope of these lecture notes). This principle is very useful and is called [function extensionality](function-extensionality.lagda.md).

## Notation for equality reasoning

When writing `trans p q` we lose type information of the
identifications `p : x ≡ y` and `q : y ≡ z`, which makes some definitions using `trans` hard to read. We now
introduce notation to be able to write e.g.

   > `x ≡⟨ p ⟩`

   > `y ≡⟨ q ⟩`

   > `z ≡⟨ r ⟩`

   > `t ∎`

rather than the more unreadable `trans p (trans q r) : x ≡ t`.

```agda
_≡⟨_⟩_ : {X : Type} (x : X) {y z : X} → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ p ⟩ q = trans p q

_∎ : {X : Type} (x : X) → x ≡ x
x ∎ = refl x

infixr  0 _≡⟨_⟩_
infix   1 _∎
```
We'll see examples of uses of this in other handouts.

[Go back to the table of contents](https://martinescardo.github.io/HoTTEST-Summer-School/)
