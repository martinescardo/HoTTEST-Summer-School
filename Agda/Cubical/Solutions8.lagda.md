# Week 8 - Cubical Agda Exercises - Solutions

```agda
{-# OPTIONS --cubical #-}

module Solutions8 where

open import cubical-prelude
open import Lecture7-notes
open import Lecture8-notes
```

## Part I: `transp` and `hcomp`

### Exercise 1 (★)

Prove the propositional computation law for `J`:

```agda
-- J = λ {x} P d p → transp (λ i → P (p i) (λ j → p (i ∧ j))) i0 d

JRefl : {A : Type ℓ} {x : A} (P : (z : A) → x ≡ z → Type ℓ'')
  (d : P x refl) → J P d refl ≡ d
JRefl {x = x} P d i = transp (λ _ → P x (λ _ → x)) i d
```

### Exercise 2 (★★)

Using `transp`, construct a method for turning dependent paths into paths.

**Hint**:
Transport the point `p i` to the fibre `A i1`, and set `φ = i` such that the
transport computes away at `i = i1`.
```text
   x ----(p i)----> y
  A i0    A i      A i1
```

```agda
fromPathP : {A : I → Type ℓ} {x : A i0} {y : A i1} →
  PathP A x y → transport (λ i → A i) x ≡ y
fromPathP {A = A} p i = transp (λ j → A (i ∨ j)) i (p i)
```

### Exercise 3 (★★★)

Using `hcomp`, construct a method for turning paths into dependent paths.

**Hint**:
At each point `i`, the verical fibre of the following diagram should lie in
`A i`. The key is to parametrise the bottom line with a dependent path from `x`
to `transport A x`. This requires writing a `transp` that computes away at
`i = i0`.

```text
       x  - - - -> y
       ^           ^
       ¦           ¦
  refl ¦           ¦ p i
       ¦           ¦
       ¦           ¦
       x ---> transport A x
```


```agda
toPathP : {A : I → Type ℓ} {x : A i0} {y : A i1} →
  transport (λ i → A i) x ≡ y → PathP A x y
toPathP {A = A} {x = x} p i =
  hcomp
    (λ {j (i = i0) → x ;
        j (i = i1) → p j })
    (transpFill i)
   where
   transpFill : PathP A x (transport (λ i → A i) x)
   transpFill i = transp (λ j → A (i ∧ j)) (~ i) x
```

### Exercise 4 (★)

Using `toPathP`, prove the following lemma, which lets you fill in dependent
lines in hProps, provided their boundary.

```agda
isProp→PathP : {A : I → Type ℓ} (p : (i : I) → isProp (A i))
  (a₀ : A i0) (a₁ : A i1) → PathP A a₀ a₁
isProp→PathP p a₀ a₁ = toPathP (p i1 _ a₁)
```

### Exercise 5 (★★)

Prove the following lemma characterizing equality in subtypes:

```agda
Σ≡Prop : {A : Type ℓ} {B : A → Type ℓ'} {u v : Σ A B} (h : (x : A) → isProp (B x))
       → (p : pr₁ u ≡ pr₁ v) → u ≡ v
Σ≡Prop {B = B} {u = u} {v = v} h p i = p i , isProp→PathP (λ i → h (p i)) (pr₂ u) (pr₂ v) i
```

### Exercise 6 (★★★)

Prove that `isContr` is a proposition:

**Hint**:
This requires drawing a cube (yes, an actual 3D one)!

```agda
isPropIsContr : {A : Type ℓ} → isProp (isContr A)
isPropIsContr (c0 , h0) (c1 , h1) j = h0 c1 j , λ y i →
  hcomp (λ {k (i = i0) → h0 c1 j ;
            k (i = i1) → h1 y k ;
            k (j = i0) → h0 (h1 y k) i ;
            k (j = i1) → h1 y (i ∧ k) }) (h0 c1 (i ∨ j))
```
