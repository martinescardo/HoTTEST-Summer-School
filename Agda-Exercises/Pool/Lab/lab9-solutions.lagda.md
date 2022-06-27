# Week 9 - Lab Sheet Solutions

```agda
{-# OPTIONS --safe --without-K --auto-inline #-}

module exercises.lab9-solutions where

open import prelude
open import decidability
open import Fin
open import List-functions
open import isomorphisms
open import sorting
open import strict-total-order

data Pos' {X : Type} : List X → Type where
  here : {x : X} {xs : List X}
       → Pos' (x :: xs)
  there : {x : X} {xs : List X}
        → (p : Pos' xs) → Pos' (x :: xs)

Pos-to-Pos' : {X : Type} (xs : List X)
            → Pos xs → Pos' xs
Pos-to-Pos' []          = 𝟘-elim
Pos-to-Pos' (x :: xs) (inl ⋆) = here
Pos-to-Pos' (x :: xs) (inr p) = there (Pos-to-Pos' xs p)

Pos'[]-is-empty : {X : Type} → is-empty (Pos' {X} [])
Pos'[]-is-empty ()

Pos'-to-Pos : {X : Type} (xs : List X)
            → Pos' xs → Pos xs
Pos'-to-Pos []        = Pos'[]-is-empty
Pos'-to-Pos (x :: xs) here      = inl ⋆
Pos'-to-Pos (x :: xs) (there p) = inr (Pos'-to-Pos xs p)

Pos-isomorphic-to-Pos' : {X : Type} (xs : List X)
                       → Pos xs ≅ Pos' xs
Pos-isomorphic-to-Pos' {X} xs = record { bijection = f ; bijectivity = f-is-bijection }
 where
  f : Pos xs → Pos' xs
  f = Pos-to-Pos' xs

  g : Pos' xs → Pos xs
  g = Pos'-to-Pos xs

  gf : g ∘ f ∼ id
  gf = lemma xs
   where
    lemma : (ys : List X)
          → (Pos'-to-Pos ys ∘ Pos-to-Pos' ys) ∼ id
    lemma (y :: ys) (inl ⋆) = refl _
    lemma (y :: ys) (inr p) = ap inr (lemma ys p)

  fg : f ∘ g ∼ id
  fg = lemma xs
   where
    lemma : (ys : List X)
          → (Pos-to-Pos' ys ∘ Pos'-to-Pos ys) ∼ id
    lemma (y :: ys) here      = refl _
    lemma (y :: ys) (there p) = ap there (lemma ys p)

  f-is-bijection : is-bijection f
  f-is-bijection = record { inverse = g ; η = gf ; ε = fg }


Pos-to-Fin-length : {X : Type} (xs : List X)
                  → Pos xs → Fin (length xs)
Pos-to-Fin-length []                = 𝟘-elim
Pos-to-Fin-length (x :: xs) (inl ⋆) = zero
Pos-to-Fin-length (x :: xs) (inr p) = suc (Pos-to-Fin-length xs p)

Fin-length-to-Pos : {X : Type} (xs : List X)
                  → Fin (length xs) → Pos xs
Fin-length-to-Pos []        = Fin-0-is-empty
Fin-length-to-Pos (x :: xs) zero    = inl ⋆
Fin-length-to-Pos (x :: xs) (suc i) = inr (Fin-length-to-Pos xs i)

Pos-isomorphic-to-Fin-length : {X : Type} (xs : List X)
                             → Pos xs ≅ Fin (length xs)
Pos-isomorphic-to-Fin-length {X} xs = record { bijection = f ; bijectivity = f-is-bijection }
 where
  f : Pos xs → Fin (length xs)
  f = Pos-to-Fin-length xs

  g : Fin (length xs) → Pos xs
  g = Fin-length-to-Pos xs

  gf : g ∘ f ∼ id
  gf = lemma xs
   where
    lemma : (ys : List X)
          → (Fin-length-to-Pos ys ∘ Pos-to-Fin-length ys) ∼ id
    lemma (y :: ys) (inl ⋆) = refl _
    lemma (y :: ys) (inr p) = ap inr (lemma ys p)

  fg : f ∘ g ∼ id
  fg = lemma xs
   where
    lemma : (ys : List X)
          → (Pos-to-Fin-length ys ∘ Fin-length-to-Pos ys) ∼ id
    lemma (y :: ys) zero    = refl _
    lemma (y :: ys) (suc i) = ap suc (lemma ys i)

  f-is-bijection : is-bijection f
  f-is-bijection = record { inverse = g ; η = gf ; ε = fg }


×-has-decidable-equality : {X Y : Type}
                         → has-decidable-equality X
                         → has-decidable-equality Y
                         → has-decidable-equality (X × Y)
×-has-decidable-equality δX δY (x , y) (x' , y') = lemma (δX x x' , δY y y')
 where
  lemma : (x ≡ x') ∔ ¬ (x ≡ x')
        × (y ≡ y') ∔ ¬ (y ≡ y')
        → is-decidable ((x , y) ≡ (x' , y'))
  lemma (inl (refl x) , inl (refl y)) = inl (refl (x , y))
  lemma (inl (refl x) , inr ne'     ) = inr (λ e → ne' (ap snd e))
  lemma (inr ne       , inl (refl y)) = inr (λ e → ne  (ap fst e))
  lemma (inr ne       , inr _       ) = inr (λ e → ne  (ap fst e))

ℕ² : Type
ℕ² = ℕ × ℕ

ℕ²-has-decidable-equality : has-decidable-equality ℕ²
ℕ²-has-decidable-equality =
 ×-has-decidable-equality ℕ-has-decidable-equality ℕ-has-decidable-equality


_<ₗ_ : ℕ × ℕ → ℕ × ℕ → Type
(n , m) <ₗ (n' , m') = (n <ₙ n') ∔ ((n ≡ n') × (m <ₙ m'))

<ₗ-is-irreflexive : (p : ℕ × ℕ) → ¬ (p <ₗ p)
<ₗ-is-irreflexive (n , m) (inl n<n)       = <ₙ-irreflexive n n<n
<ₗ-is-irreflexive (n , m) (inr (_ , m<m)) = <ₙ-irreflexive m m<m

<ₗ-is-transitive : {p q r : ℕ × ℕ} → p <ₗ q → q <ₗ r → p <ₗ r
<ₗ-is-transitive {n , m} {n' , m'} {n'' , m''}
                 (inl n<n') (inl n'<n'') = inl (<ₙ-trans n<n' n'<n'')
<ₗ-is-transitive {n , m} {n' , m'} {n'' , m''}
                 (inl n<n') (inr (refl n' , _)) = inl n<n'
<ₗ-is-transitive {n , m} {.n , m'} {n'' , m''}
                 (inr (refl n , m<m')) (inl n<n'') = inl n<n''
<ₗ-is-transitive {n , m} {.n , m'} {n'' , m''}
                 (inr (refl n , m<m')) (inr (refl n , m'<m'')) = goal
 where
  goal : (n <ₙ n) ∔ ((n ≡ n) × (m <ₙ m''))
  goal = inr (refl n , <ₙ-trans m<m' m'<m'')

<ₗ-is-connected : {p q : ℕ × ℕ} → ¬ (p ≡ q) → (p <ₗ q) ∔ (q <ₗ p)
<ₗ-is-connected {n , m} {n' , m'} pairs-not-equal =
 lemma (ℕ-has-decidable-equality n n' , ℕ-has-decidable-equality m m')
 where
  lemma : (n ≡ n') ∔ ¬ (n ≡ n')
        × (m ≡ m') ∔ ¬ (m ≡ m')
        → ((n , m) <ₗ (n' , m')) ∔ ((n' , m') <ₗ (n , m))
  lemma (inl (refl n) , inl (refl m)) = 𝟘-elim (pairs-not-equal (refl (n , m)))
  lemma (inl e , inr ne') = sublemma (<ₙ-connected ne')
   where
    sublemma : (m <ₙ m') ∔ (m' <ₙ m)
             → ((n , m) <ₗ (n' , m')) ∔ ((n' , m') <ₗ (n , m))
    sublemma (inl m<m') = inl (inr (e     , m<m'))
    sublemma (inr m'<m) = inr (inr (sym e , m'<m))
  lemma (inr ne , _)       = sublemma (<ₙ-connected ne)
   where
    sublemma : (n <ₙ n') ∔ (n' <ₙ n)
             → ((n , m) <ₗ (n' , m')) ∔ ((n' , m') <ₗ (n , m))
    sublemma (inl n<n') = inl (inl n<n')
    sublemma (inr n'<n) = inr (inl n'<n)

strict-total-order-on-ℕ² : StrictTotalOrder ℕ²
strict-total-order-on-ℕ² = record {
    _<_          = _<ₗ_
  ; decidable   = ℕ²-has-decidable-equality
  ; irreflexive = <ₗ-is-irreflexive
  ; transitive  = <ₗ-is-transitive
  ; connected   = <ₗ-is-connected
  }


record NonStrictTotalOrder (X : Type) : Type₁ where
 field
  _≤_ : X → X → Type
  decidable : has-decidable-equality X
  reflexive : (x : X) → x ≤ x
  transitive : {x y z : X} → x ≤ y → y ≤ z → x ≤ z
  antisymmetric : {x y : X} → x ≤ y → y ≤ x → x ≡ y
  strongly-connected : (x y : X) → (x ≤ y) ∔ (y ≤ x)

module _
        {X : Type}
        (sto : StrictTotalOrder X)
       where

 open StrictTotalOrder sto

 _≤_ : X → X → Type
 x ≤ y = (y ≡ x) ∔ (x < y)

 <-to-≤ : {x y : X} → x < y → x ≤ y
 <-to-≤ = inr

 ≤-is-reflexive : (x : X) → x ≤ x
 ≤-is-reflexive x = inl (refl x)

 <-≤-trans : {x y z : X} → x < y → y ≤ z → x ≤ z
 <-≤-trans x<y (inl (refl _)) = inr x<y
 <-≤-trans x<y (inr y<z     ) = inr (transitive x<y y<z)

 ≤-is-transitive : {x y z : X} → x ≤ y → y ≤ z → x ≤ z
 ≤-is-transitive (inl (refl _)) y≤z = y≤z
 ≤-is-transitive (inr x<y     ) y≤z = <-≤-trans x<y y≤z

 ≤-is-antisymmetric : {x y : X} → x ≤ y → y ≤ x → x ≡ y
 ≤-is-antisymmetric (inl e  ) q         = sym e
 ≤-is-antisymmetric (inr x<y) (inl e)   = e
 ≤-is-antisymmetric (inr x<y) (inr y<x) = 𝟘-elim (antisymmetric _ _ x<y y<x)

 ≤-is-strongly-connected : (x y : X) → (x ≤ y) ∔ (y ≤ x)
 ≤-is-strongly-connected x y = lemma (decidable x y)
  where
   lemma : (x ≡ y) ∔ ¬ (x ≡ y)
         → (x ≤ y) ∔ (y ≤ x)
   lemma (inl e ) = inr (inl e)
   lemma (inr ne) = sublemma (connected ne)
    where
     sublemma : (x < y) ∔ (y < x)
              → (x ≤ y) ∔ (y ≤ x)
     sublemma (inl x<y) = inl (<-to-≤ x<y)
     sublemma (inr y<x) = inr (<-to-≤ y<x)

 non-strict-total-order-from-strict-total-order : NonStrictTotalOrder X
 non-strict-total-order-from-strict-total-order = record {
    _≤_                = _≤_
  ; decidable          = decidable
  ; reflexive          = ≤-is-reflexive
  ; transitive         = ≤-is-transitive
  ; antisymmetric      = ≤-is-antisymmetric
  ; strongly-connected = ≤-is-strongly-connected
  }
```
