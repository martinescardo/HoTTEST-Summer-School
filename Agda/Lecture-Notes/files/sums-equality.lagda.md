
[Martin Escardo](Https://www.Cs.Bham.Ac.Uk/~mhe/).
Notes originally written for the module *Advanced Functional Programming* of the [University of Birmingham](https://www.birmingham.ac.uk/index.aspx), UK.


<!--
```agda
{-# OPTIONS --without-K --safe #-}

module sums-equality where

open import general-notation
open import sums
open import binary-products
open import identity-type
```
-->
# Equality in `Σ` types

The material here is rather subtle.

## Equality in binary products

Equality in binary product types behaves as expected:

```agda
module _ {X A : Type} {(x , a) (y , b) : X × A} where

 from-×-≡ : (x , a) ≡ (y , b)
          → (x ≡ y) × (a ≡ b)
 from-×-≡ (refl (x , a)) = (refl x , refl a)

 to-×-≡ : (x ≡ y) × (a ≡ b)
        → (x , a) ≡ (y , b)
 to-×-≡ (refl x , refl a) = refl (x , a)

 ×-≡ : (x , a) ≡ (y , b) ⇔ (x ≡ y) × (a ≡ b)
 ×-≡ = from-×-≡ , to-×-≡
```

## Equality in `Σ` types

Equality in `Σ` types is much less intuitive.

Firstly, if we have a type `X`, a family `A : X → Type`, and pairs `(x , a)` and `(y , b)` in the type `Σ
A`, it is the case that if `(x , a) ≡ (y , b)` then `x ≡ y`, just as in the case of binary products:

```agda
Σ-≡-fst : {X : Type} {A : X → Type} {(x , a) (y , b) : Σ A}
        → (x , a) ≡ (y , b) → x ≡ y
Σ-≡-fst (refl (x , a)) = refl x
```

However, we don't have that `(x , a) ≡ (y , b)` implies `a ≡ b`. It is not that this is false, but instead that it doesn't even type-check. In fact we have

  * `a : A x`
  * `b : A y`

and the types `A x` and `A y` are not necessarily the *same*. But
equality is only defined for elements of the same type. Notice that `x
≡ y` doesn't say that `x` and `y` are the *same*. It only says that
there is an *identification* between them. And the distinction between
sameness and identification is important.

We can use the function `transport` (defined in the module
[identity-type](identity-type.lagda))

```agda-repetition
    transport : {X : Type} (A : X → Type)
              → {x y : X} → x ≡ y → A x → A y
    transport A (refl x) a = a
```

to solve this problem:

```agda
Σ-≡-snd : {X : Type} {A : X → Type} {(x , a) (y , b) : Σ A}
        → (e : (x , a) ≡ (y , b))
        → transport A (Σ-≡-fst e) a ≡ b
Σ-≡-snd (refl (x , a)) = refl a
```

We can pack these two functions into a single one as follows:

```agda
from-Σ-≡ : {X : Type} {A : X → Type} {(x , a) (y , b) : Σ A}
         → (x , a) ≡ (y , b)
         → Σ e ꞉ x ≡ y , transport A e a ≡ b
from-Σ-≡ (refl (x , a)) = (refl x , refl a)
```
This says that from `(x , a) ≡ (y , b)` we can get some `e : x ≡ y` such that `transport A e a ≡ b`.


The converse also holds:
```agda
to-Σ-≡ : {X : Type} {A : X → Type} {(x , a) (y , b) : Σ A}
       → (Σ e ꞉ x ≡ y , transport A e a ≡ b)
       → (x , a) ≡ (y , b)
to-Σ-≡ (refl x , refl a) = refl (x , a)
```

So the functions `from-Σ-≡` and `to-Σ-≡` give a complete characterization of equality in `Σ` types.

```agda
Σ-≡ : {X : Type} {A : X → Type} {(x , a) (y , b) : Σ A}
    → (x , a) ≡ (y , b) ⇔ (Σ e ꞉ x ≡ y , transport A e a ≡ b)
Σ-≡ = from-Σ-≡ , to-Σ-≡
```

*Exercise.* The function `from-Σ-≡` is actually an isomorphism with
 inverse `to-Σ-≡`, so that we actually get the stronger result

   > `((x , a) ≡ (y , b)) ≅ (Σ e ꞉ x ≡ y , transport A e a ≡ b)`.

## Dependent version of `ap`

Recall the function `ap` defined in the module
[identity-type](identity-type.lagda):

```agda-repetition
    ap : {A B : Type} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
    ap f (refl x) = refl (f x)
```

A similar phenomenon as for `Σ` happens with dependent functions `f : (x : X) → A x`. We can't conclude that if `x ≡ y` then `f x ≡ f y`, because, again, the equality in the conclusion doesn't type check, as `f x` and `f y` belong to the types `A x` and `A y`, which are not the same in general, even if `x` and `y` are identified.

But again we can use `transport` to solve this problem:
```agda
apd : {X : Type} {A : X → Type} (f : (x : X) → A x) {x y : X}
      (e : x ≡ y) → transport A e (f x) ≡ f y
apd f (refl x) = refl (f x)
```

[Go back to the table of contents](https://martinescardo.github.io/HoTTEST-Summer-School/)
