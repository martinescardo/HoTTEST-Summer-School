
[Martin Escardo](Https://www.Cs.Bham.Ac.Uk/~mhe/).
Notes originally written for the module *Advanced Functional Programming* of the [University of Birmingham](https://www.birmingham.ac.uk/index.aspx), UK.


<!--
```agda
{-# OPTIONS --without-K --safe #-}

module negation where

open import general-notation
open import prelude
```
-->
# Reasoning with negation

[Recall that](empty-type.lagda.md) we defined the negation `¬ A` of a type `A` to be the function type `A → 𝟘`,
and that we also wrote `is-empty A` as a synonym of `¬ A`.

## Emptiness of the empty type

We have the following two proofs of "not false" or "the empty type is empty":
```agda
not-false : ¬ 𝟘
not-false = 𝟘-elim

not-false' : ¬ 𝟘
not-false' = id
```
A lot of things about negation don't depend on the fact that the target type of the function type is `𝟘`. We will begin by proving some things about negation by generalizing `𝟘` to any type `R` of "results".

## Implication from disjunction and negation

If `¬ A` or `B`, then `A implies B`:
```agda
implication-from-disjunction-and-negation : {A B : Type} → ¬ A ∔ B → (A → B)
implication-from-disjunction-and-negation (inl f) a = 𝟘-elim (f a)
implication-from-disjunction-and-negation (inr b) a = b
```


## Contrapositives

If `A` implies `B`, then `B → R` implies `A → R`:
```agda
arrow-contravariance : {A B R : Type}
                     → (A → B)
                     → (B → R) → (A → R)
arrow-contravariance f g = g ∘ f
```
A particular case of interest is the following. The [contrapositive](https://en.wikipedia.org/wiki/Contraposition) of an implication `A → B` is the implication `¬ B → ¬ A`:
```agda
contrapositive : {A B : Type} → (A → B) → (¬ B → ¬ A)
contrapositive {A} {B} = arrow-contravariance {A} {B} {𝟘}
```
This can also be read as "if we have a function A → B and B is empty, then also A must be empty".

## Double and triple negations

We now introduce notation for double and triple negation, to reduce the number of needed brackets:

```agda
¬¬_ ¬¬¬_ : Type → Type
¬¬  A = ¬(¬ A)
¬¬¬ A = ¬(¬¬ A)
```
We have that `A` implies `¬¬ A`. This is called double negation introduction. More generally, we have the following:
```agda
dni : (A R : Type) → A → ((A → R) → R)
dni A R a u = u a

¬¬-intro : {A : Type} → A → ¬¬ A
¬¬-intro {A} = dni A 𝟘
```
We don't always have `¬¬ A → A` in proofs-as-programs. This has to do with *computability theory*. But sometimes we do. For example, if we know that `A ∔ ¬ A` then `¬¬A → A` follows:
<!--
```agda
private -- because it is defined elsewhere, and it is here for illustration only
```
-->
```agda
 ¬¬-elim : {A : Type} → A ∔ ¬ A → ¬¬ A → A
 ¬¬-elim (inl x) f = x
 ¬¬-elim (inr g) f = 𝟘-elim (f g)
```
For more details, see the lecture notes on [decidability](decidability.lagda.md), where we discuss `¬¬-elim` again.
But three negations always imply one, and conversely:
```agda
three-negations-imply-one : {A : Type} → ¬¬¬ A → ¬ A
three-negations-imply-one = contrapositive ¬¬-intro

one-negation-implies-three : {A : Type} → ¬ A → ¬¬¬ A
one-negation-implies-three = ¬¬-intro
```

## Negation of the identity type

It is useful to introduce a notation for the negation of the [identity type](identity-type.lagda.md):
```agda
_≢_ : {X : Type} → X → X → Type
x ≢ y = ¬ (x ≡ y)

≢-sym : {X : Type} {x y : X} → x ≢ y → y ≢ x
≢-sym = contrapositive sym

false-is-not-true : false ≢ true
false-is-not-true ()

true-is-not-false : true ≢ false
true-is-not-false ()
```
The following is more interesting:
```agda
not-false-is-true : (x : Bool) → x ≢ false → x ≡ true
not-false-is-true true  f = refl true
not-false-is-true false f = 𝟘-elim (f (refl false))

not-true-is-false : (x : Bool) → x ≢ true → x ≡ false
not-true-is-false true  f = 𝟘-elim (f (refl true))
not-true-is-false false f = refl false
```

## Disjointness of binary sums

We now show something that is intuitively the case:
```agda
inl-is-not-inr : {X Y : Type} {x : X} {y : Y} → inl x ≢ inr y
inl-is-not-inr ()
```
Agda just knows it.

## Disjunctions and negation

If  `A or B` holds and `B` is false, then `A` must hold:
```agda
right-fails-gives-left-holds : {A B : Type} → A ∔ B → ¬ B → A
right-fails-gives-left-holds (inl a) f = a
right-fails-gives-left-holds (inr b) f = 𝟘-elim (f b)

left-fails-gives-right-holds : {A B : Type} → A ∔ B → ¬ A → B
left-fails-gives-right-holds (inl a) f = 𝟘-elim (f a)
left-fails-gives-right-holds (inr b) f = b
```

## Negation of the existential quantifier:

If there is no `x : X` with `A x`, then for all `x : X` not `A x`:
```agda
not-exists-implies-forall-not : {X : Type} {A : X → Type}
                              → ¬ (Σ x ꞉ X , A x)
                              → (x : X) → ¬ A x
not-exists-implies-forall-not f x a = f (x , a)
```
The converse also holds:
```agda
forall-not-implies-not-exists : {X : Type} {A : X → Type}
                              → ((x : X) → ¬ A x)
                              → ¬ (Σ x ꞉ X , A x)
forall-not-implies-not-exists g (x , a) = g x a
```
Notice how these are particular cases of [`curry` and `uncurry`](https://en.wikipedia.org/wiki/Currying).

## Implication truth table

Here is a proof of the implication truth-table:
```agda
open import empty-type
open import unit-type

implication-truth-table : ((𝟘 → 𝟘) ⇔ 𝟙)
                        × ((𝟘 → 𝟙) ⇔ 𝟙)
                        × ((𝟙 → 𝟘) ⇔ 𝟘)
                        × ((𝟙 → 𝟙) ⇔ 𝟙)
implication-truth-table = ((λ _ → ⋆)   , (λ _ → id)) ,
                          ((λ _ → ⋆)   , (λ _ _ → ⋆)) ,
                          ((λ f → f ⋆) , (λ ⋆ _ → ⋆)) ,
                          ((λ _ → ⋆)   , (λ _ _ → ⋆))
```

[Go back to the table of contents](https://martinescardo.github.io/HoTTEST-Summer-School/)
