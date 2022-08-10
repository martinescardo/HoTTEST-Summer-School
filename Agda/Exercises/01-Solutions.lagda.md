# Week 01 - Agda Exercises - Solutions

```agda
{-# OPTIONS --without-K --safe #-}

module 01-Solutions where

open import prelude hiding (not-is-involution)
```

## Part I

```agda
_&&'_ : Bool → Bool → Bool
true  &&' true  = true
true  &&' false = false
false &&' true  = false
false &&' false = false

_xor_ : Bool → Bool → Bool
true  xor true  = false
true  xor false = true
false xor true  = true
false xor false = false

_^_ : ℕ → ℕ → ℕ
n ^ zero  = 1
n ^ suc m = n * (n ^ m)

^-example : 3 ^ 4 ≡ 81
^-example = refl 81

_! : ℕ → ℕ
zero  !  = 1
suc n !  = suc n * (n !)

!-example : 4 ! ≡ 24
!-example = refl 24

max : ℕ → ℕ → ℕ
max zero    m       = m
max (suc n) zero    = suc n
max (suc n) (suc m) = suc (max n m)

min : ℕ → ℕ → ℕ
min zero    m       = zero
min (suc n) zero    = zero
min (suc n) (suc m) = suc (min n m)

min-example : min 5 3 ≡ 3
min-example = refl 3

map : {X Y : Type} → (X → Y) → List X → List Y
map f []        = []
map f (x :: xs) = f x :: map f xs

map-example : map (_+ 3) (1 :: 2 :: 3 :: []) ≡ 4 :: 5 :: 6 :: []
map-example = refl _

filter : {X : Type} (p : X → Bool) → List X → List X
filter {X} p []        = []
filter {X} p (x :: xs) = if (p x) then (x :: ys) else ys
 where
  ys : List X
  ys = filter p xs

is-non-zero : ℕ → Bool
is-non-zero zero    = false
is-non-zero (suc _) = true

filter-example : filter is-non-zero (4 :: 3 :: 0 :: 1 :: 0 :: []) ≡ 4 :: 3 :: 1 :: []
filter-example = refl _
```

## Part II

```agda
_≣_ : Bool → Bool → Type
true  ≣ true  = 𝟙
true  ≣ false = 𝟘
false ≣ true  = 𝟘
false ≣ false = 𝟙

Bool-refl : (b : Bool) → b ≣ b
Bool-refl true  = ⋆
Bool-refl false = ⋆

≡-to-≣ : (a b : Bool) → a ≡ b → a ≣ b
≡-to-≣ b b (refl b) = Bool-refl b

≣-to-≡ : (a b : Bool) → a ≣ b → a ≡ b
≣-to-≡ true  true  ⋆ = refl true
≣-to-≡ false false ⋆ = refl false
```

## Part III

```agda
not-is-involution : (b : Bool) → not (not b) ≡ b
not-is-involution true  = refl true
not-is-involution false = refl false

||-is-commutative : (a b : Bool) → a || b ≡ b || a
||-is-commutative true true   = refl true
||-is-commutative true false  = refl true
||-is-commutative false true  = refl true
||-is-commutative false false = refl false

&&-is-commutative : (a b : Bool) → a && b ≡ b && a
&&-is-commutative true  true  = refl true
&&-is-commutative true  false = refl false
&&-is-commutative false true  = refl false
&&-is-commutative false false = refl false

-- Notice how we choose to pattern match on the leftmost argument, because
-- that's also how we defined &&.
&&-is-associative : (a b c : Bool) → a && (b && c) ≡ (a && b) && c
&&-is-associative true  b c = refl (b && c)
&&-is-associative false b c = refl false

-- Because &&' is defined by pattern matching on all its arguments, we now need
-- to consider 2^3 = 8 cases.
&&'-is-associative : (a b c : Bool) → a &&' (b &&' c) ≡ (a &&' b) &&' c
&&'-is-associative true  true  true  = refl true
&&'-is-associative true  true  false = refl false
&&'-is-associative true  false true  = refl false
&&'-is-associative true  false false = refl false
&&'-is-associative false true  true  = refl false
&&'-is-associative false true  false = refl false
&&'-is-associative false false true  = refl false
&&'-is-associative false false false = refl false

max-is-commutative : (n m : ℕ) → max n m ≡ max m n
max-is-commutative zero    zero    = refl zero
max-is-commutative zero    (suc m) = refl (suc m)
max-is-commutative (suc n) zero    = refl (suc n)
max-is-commutative (suc n) (suc m) = to-show
 where
  IH : max n m ≡ max m n      -- induction hypothesis
  IH = max-is-commutative n m -- recursive call on smaller arguments
  to-show : suc (max n m) ≡ suc (max m n)
  to-show = ap suc IH         -- ap(ply) suc on both sides of the equation

min-is-commutative : (n m : ℕ) → min n m ≡ min m n
min-is-commutative zero    zero    = refl zero
min-is-commutative zero    (suc m) = refl zero
min-is-commutative (suc n) zero    = refl zero
min-is-commutative (suc n) (suc m) = to-show
 where
  IH : min n m ≡ min m n      -- induction hypothesis
  IH = min-is-commutative n m -- recursive call on smaller arguments
  to-show : suc (min n m) ≡ suc (min m n)
  to-show = ap suc IH         -- ap(ply) suc on both sides of the equation

0-right-neutral : (n : ℕ) → n ≡ n + 0
0-right-neutral zero    = refl zero
0-right-neutral (suc n) = to-show
 where
  IH : n ≡ n + 0         -- induction hypothesis
  IH = 0-right-neutral n -- recursive call on smaller argument
  to-show : suc n ≡ suc (n + 0)
  to-show = ap suc IH    -- ap(ply) suc on both sides of the equation

map-id : {X : Type} (xs : List X) → map id xs ≡ xs
map-id []        = refl []
map-id (x :: xs) = to-show
 where
  IH : map id xs ≡ xs
  IH = map-id xs
  to-show : x :: map id xs ≡ x :: xs
  to-show = ap (x ::_) IH

map-comp : {X Y Z : Type} (f : X → Y) (g : Y → Z)
           (xs : List X) → map (g ∘ f) xs ≡ map g (map f xs)
map-comp f g []        = refl []
map-comp f g (x :: xs) = to-show
 where
  IH : map (g ∘ f) xs ≡ map g (map f xs)
  IH = map-comp f g xs
  to-show : g (f x) :: map (g ∘ f) xs ≡ g (f x) :: map g (map f xs)
  to-show = ap (g (f x) ::_) IH
```
