--
Martin Escardo
Notes originally written for the module "Advanced Functional Programming"
at the School of Computer Science of the University of Birmingham, UK.
--

<!--
```agda
{-# OPTIONS --without-K --safe #-}

module searchability where

open import prelude
open import negation
open import decidability
```
-->
# Examples of searchable sets

Recall that we defined exhaustibly searchable types in the module [decidability](decidability.lagda.md). Let's adopt a shorter name for the purposes of this module.
```agda
is-searchable = is-exhaustively-searchable
```

## `𝟘` is searchable

```agda
𝟘-is-searchable : is-searchable 𝟘
𝟘-is-searchable A δ = inr (λ (x , a) → x)
```

## `𝟙` is searchable

```agda
𝟙-is-searchable : is-searchable 𝟙
𝟙-is-searchable A d = I (d ⋆)
 where
  I : A ⋆ ∔ ¬ A ⋆ → is-decidable (Σ x ꞉ 𝟙 , A x)
  I (inl a) = inl (⋆ , a)
  I (inr u) = inr (λ (⋆ , a) → u a)
```

## Searchable types are closed under `_∔_`

```agda
∔-is-searchable : {X Y : Type}
                → is-searchable X
                → is-searchable Y
                → is-searchable (X ∔ Y)
∔-is-searchable {X} {Y} c d A δ = II
 where
  I : is-decidable (Σ x ꞉ X , A (inl x))
    → is-decidable (Σ y ꞉ Y , A (inr y))
    → is-decidable (Σ z ꞉ X ∔ Y , A z)
  I (inl (x , a)) _             = inl (inl x , a)
  I (inr f)       (inl (y , a)) = inl (inr y , a)
  I (inr f)       (inr g)       = inr h
   where
    h : (Σ z ꞉ X ∔ Y , A z) → 𝟘
    h (inl x , a) = f (x , a)
    h (inr y , a) = g (y , a)

  II : is-decidable (Σ z ꞉ X ∔ Y , A z)
  II = I (c (λ x → A (inl x))
            (λ x → δ (inl x)))
         (d (λ y → A (inr y))
            (λ y → δ (inr y)))
```

## `Fin' n` is searchable

```agda
open import Fin-functions

Fin'-is-searchable : (n : ℕ) → is-searchable (Fin' n)
Fin'-is-searchable 0       = 𝟘-is-searchable
Fin'-is-searchable (suc n) = ∔-is-searchable
                              𝟙-is-searchable
                              (Fin'-is-searchable n)
```

## Searchable types are closed under isomorphism

```agda
open import isomorphisms

≅-is-searchable : {X Y : Type}
                → is-searchable X
                → X ≅ Y
                → is-searchable Y
≅-is-searchable {X} {Y} s (Isomorphism f (Inverse g _ ε)) A d = III
 where
  B : X → Type
  B x = A (f x)

  I : is-decidable-predicate B
  I x = d (f x)

  II : is-decidable (Σ B) → is-decidable (Σ A)
  II (inl (x , a)) = inl (f x , a)
  II (inr u)       = inr (λ (y , a) → u (g y , transport A (sym (ε y)) a))

  III : is-decidable (Σ A)
  III = II (s B I)
```

## `𝟚` is searchable

```agda
open import binary-type

𝟙∔𝟙-is-searchable : is-searchable (𝟙 ∔ 𝟙)
𝟙∔𝟙-is-searchable = ∔-is-searchable 𝟙-is-searchable 𝟙-is-searchable

𝟙∔𝟙-is-𝟚 : 𝟙 ∔ 𝟙 ≅ 𝟚
𝟙∔𝟙-is-𝟚 = Isomorphism f (Inverse g gf fg)
 where
  f : 𝟙 ∔ 𝟙 → 𝟚
  f (inl ⋆) = 𝟎
  f (inr ⋆) = 𝟏

  g : 𝟚 → 𝟙 ∔ 𝟙
  g 𝟎 = inl ⋆
  g 𝟏 = inr ⋆

  gf : g ∘ f ∼ id
  gf (inl ⋆) = refl (inl ⋆)
  gf (inr ⋆) = refl (inr ⋆)

  fg : f ∘ g ∼ id
  fg 𝟎 = refl 𝟎
  fg 𝟏 = refl 𝟏

𝟚-is-searchable : is-searchable 𝟚
𝟚-is-searchable = ≅-is-searchable
                   𝟙∔𝟙-is-searchable
                   𝟙∔𝟙-is-𝟚
```

## `Fin n` is searchable

```agda
open import Fin
open import isomorphism-functions

Fin-is-searchable : (n : ℕ) → is-searchable (Fin n)
Fin-is-searchable n = ≅-is-searchable
                       (Fin'-is-searchable n)
                       (≅-sym (Fin-isomorphism n))
```

## Running the programs/proofs produced above

We proved the above facts by writing programs. Because the proofs are
programs, we can run them. Here is an example.

We first need to set the scene for the example.

```agda
_<ᶠⁱⁿ_ : {n k : ℕ} → Fin n → Fin k → Type
zero  <ᶠⁱⁿ zero  = 𝟘
zero  <ᶠⁱⁿ suc y = 𝟙
suc x <ᶠⁱⁿ zero  = 𝟘
suc x <ᶠⁱⁿ suc y = x <ᶠⁱⁿ y

<ᶠⁱⁿ-is-decidable : {n k : ℕ} (x : Fin n) (y : Fin k)
                  → is-decidable (x <ᶠⁱⁿ y)
<ᶠⁱⁿ-is-decidable zero    zero    = 𝟘-is-decidable
<ᶠⁱⁿ-is-decidable zero    (suc y) = 𝟙-is-decidable
<ᶠⁱⁿ-is-decidable (suc x) zero    = 𝟘-is-decidable
<ᶠⁱⁿ-is-decidable (suc x) (suc y) = <ᶠⁱⁿ-is-decidable x y

import negation

is-even : {n : ℕ} → Fin n → Type
is-even zero    = 𝟙
is-even (suc x) = ¬ is-even x

evenness-is-decidable : {n : ℕ} (x : Fin n) → is-decidable (is-even x)
evenness-is-decidable zero    = 𝟙-is-decidable
evenness-is-decidable (suc x) = g
 where
  IH : is-decidable (is-even x)
  IH = evenness-is-decidable x

  f : is-decidable (is-even x) → is-decidable (¬ is-even x)
  f (inl e) = inr (¬¬-intro e)
  f (inr f) = inl f

  g : is-decidable (¬ is-even x)
  g = f IH

min : {n : ℕ} → Fin n → ℕ → Fin n
min zero    y       = zero
min (suc x) zero    = zero
min (suc x) (suc y) = suc (min x y)
```
Using the above, we can run a proof. Here is an admitedly convoluted
example (we want to keep it short):

```agda
open import natural-numbers-functions hiding (is-even ; min)
open import decidability
open import Maybe

searchability-example : (n : ℕ) → Maybe (Fin n)
searchability-example n = f δ
 where
  A : Fin n → Type
  A x = is-even x × (min x 7 <ᶠⁱⁿ x)

  d : is-decidable-predicate A
  d x = ×-preserves-decidability
         (evenness-is-decidable x)
         (<ᶠⁱⁿ-is-decidable (min x 7) x)

  δ : is-decidable (Σ A)
  δ = Fin-is-searchable n A d

  f : is-decidable (Σ A) → Maybe (Fin n)
  f (inl (x , a)) = just x
  f (inr _)       = nothing
```

We can now compute with `ctrl-c ctrl-n" (normalize). We can run things
like `searchability-example 6` and `searchability-example 8`. Try
them. What other proofs in other handouts can be run? Proofs are
programs. This means that they compute.
