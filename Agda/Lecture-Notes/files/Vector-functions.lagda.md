
[Martin Escardo](Https://www.Cs.Bham.Ac.Uk/~mhe/).
Notes originally written for the module *Advanced Functional Programming* of the [University of Birmingham](https://www.birmingham.ac.uk/index.aspx), UK.


<!--
```agda
{-# OPTIONS --without-K --safe #-}

module Vector-functions where

open import prelude
```
-->
# Some functions on vectors

As mentioned in the [introduction](introduction.lagda.md), vectors allow us to have safe `head` and `tail` functions.
```agda
head : {A : Type} {n : ℕ} → Vector A (suc n) → A
head (x :: xs) = x

tail : {A : Type} {n : ℕ} → Vector A (suc n) → Vector A n
tail (x :: xs) = xs
```

We can also define a safe indexing function on vectors using [finite types](Fin.lagda.md) as follows.
```agda
open import Fin

_!!_ : ∀ {X n} → Vector X n → Fin n → X
(x :: xs) !! zero  = x
(x :: xs) !! suc n = xs !! n
```
Alternatively, this can be defined as follows:
```agda
_!!'_ : {X : Type} {n : ℕ} → Vector X n → Fin n → X
[]        !!' ()
(x :: xs) !!' zero  = x
(x :: xs) !!' suc n = xs !!' n
```

We can also do vector concatenation:
```agda
_++_ : {X : Type} {m n : ℕ} → Vector X m → Vector X n → Vector X (m + n)
[]        ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

infixr 20 _++_
```

## Vectors represented as a Basic MLTT type

```agda
open import unit-type
open import binary-products

Vector' : Type → ℕ → Type
Vector' A 0       = 𝟙
Vector' A (suc n) = A × Vector' A n

[]' : {A : Type} → Vector' A 0
[]' = ⋆

_::'_ : {A : Type} {n : ℕ} → A → Vector' A n → Vector' A (suc n)
x ::' xs = x , xs

infixr 10 _::'_

private
 example₀ : Vector' ℕ 3
 example₀ = 1 ::' 2 ::' 3 ::' ([]' {ℕ})

 example₁ : example₀ ≡ (1 , 2 , 3 , ⋆)
 example₁ = refl _

open import isomorphisms

Vector-iso : {A : Type} {n : ℕ} → Vector A n ≅ Vector' A n
Vector-iso {A} {n} = record { bijection = f n ; bijectivity = f-is-bijection n }
 where
  f : (n : ℕ) → Vector A n → Vector' A n
  f 0       []        = []' {A}
  f (suc n) (x :: xs) = x ::' f n xs

  g : (n : ℕ) → Vector' A n → Vector A n
  g 0       ⋆        = []
  g (suc n) (x , xs) = x :: g n xs

  gf : (n : ℕ) → g n ∘ f n ∼ id
  gf 0       []        = refl []
  gf (suc n) (x :: xs) = ap (x ::_) (gf n xs)

  fg : (n : ℕ) → f n ∘ g n ∼ id
  fg 0       ⋆        = refl ⋆
  fg (suc n) (x , xs) = ap (x ,_) (fg n xs)

  f-is-bijection : (n : ℕ) → is-bijection (f n)
  f-is-bijection n = record { inverse = g n ; η = gf n ; ε = fg n }

private
 open _≅_
 open is-bijection

 example₂ : bijection Vector-iso (1 :: 2 :: 3 :: []) ≡ (1 , 2 , 3 , ⋆)
 example₂ = refl _

 example₄ : Vector ℕ 3
 example₄ = inverse (bijectivity Vector-iso) (1 , 2 , 3 , ⋆)

 example₅ : example₄ ≡ 1 :: 2 :: 3 :: []
 example₅ = refl _
```

[Go back to the table of contents](https://martinescardo.github.io/HoTTEST-Summer-School/)
