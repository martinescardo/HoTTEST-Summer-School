# Week 2 - Lab Sheet - Solutions

```agda
{-# OPTIONS --without-K --safe #-}

module Pool.Lab.lab2-solutions where

open import prelude hiding (_||_)

_≣_ : Bool → Bool → Type
true  ≣ true  = 𝟙
true  ≣ false = 𝟘
false ≣ true  = 𝟘
false ≣ false = 𝟙

_==_ : Bool → Bool → Bool
true  == true  = true
true  == false = false
false == true  = false
false == false = true

≡-to-≣ : (x y : Bool) → x ≡ y → x ≣ y
≡-to-≣ true  true  e = ⋆
≡-to-≣ false false e = ⋆

is-true : Bool → Type
is-true b = b ≡ true

≣-to-== : (x y : Bool) → x ≣ y → is-true (x == y)
≣-to-== true  true e  = refl true
≣-to-== false false e = refl true

==-to-≡ : (x y : Bool) → is-true (x == y) → x ≡ y
==-to-≡ true  true  e = refl true
==-to-≡ false false e = refl false

≡-to-== : (x y : Bool) → x ≡ y → is-true (x == y)
≡-to-== x y e = ≣-to-== x y (≡-to-≣ x y e)

≣-to-≡ : (x y : Bool) → x ≣ y → x ≡ y
≣-to-≡ x y e = ==-to-≡ x y (≣-to-== x y e)

==-to-≣ : (x y : Bool) → is-true (x == y) → x ≣ y
==-to-≣ x y e = ≡-to-≣ x y (==-to-≡ x y e)


data Either (A B : Type) : Type where
 left  : A → Either A B
 right : B → Either A B

if'_then_else_ : {A B : Type} → Bool → A → B → Either A B
if' true  then x else y = left  x
if' false then x else y = right y


_||_ : Bool → Bool → Bool
true  || y = true
false || y = y

_||'_ : Bool → Bool → Bool
true  ||' true  = true
true  ||' false = true
false ||' true  = true
false ||' false = false


||-assoc : (a b c : Bool)  → a || (b || c) ≡ (a || b) || c
||-assoc true  b c = refl true
||-assoc false b c = refl (b || c)

||'-assoc : (a b c : Bool) → a ||' (b ||' c) ≡ (a ||' b) ||' c
||'-assoc true  true  true  = refl true
||'-assoc true  true  false = refl true
||'-assoc true  false true  = refl true
||'-assoc true  false false = refl true
||'-assoc false true  true  = refl true
||'-assoc false true  false = refl true
||'-assoc false false true  = refl true
||'-assoc false false false = refl false

||-is-commutative : (a b : Bool) → a || b ≡ b || a
||-is-commutative true  true  = refl true
||-is-commutative true  false = refl true
||-is-commutative false true  = refl true
||-is-commutative false false = refl false

false-left-unit-for-|| : (b : Bool) → false || b ≡ b
false-left-unit-for-|| = refl

false-right-unit-for-|| : (b : Bool) → b || false ≡ b
false-right-unit-for-|| true  = refl true
false-right-unit-for-|| false = refl false

&&-is-associative : (a b c : Bool) → a && (b && c) ≡ (a && b) && c
&&-is-associative true  b c = refl (b && c)
&&-is-associative false b c = refl false

&&-is-commutative : (a b : Bool) → a && b ≡ b && a
&&-is-commutative true  true  = refl true
&&-is-commutative true  false = refl false
&&-is-commutative false true  = refl false
&&-is-commutative false false = refl false

true-left-unit-for-&& : (b : Bool) → true && b ≡ b
true-left-unit-for-&& = refl

true-right-unit-for-&& : (b : Bool) → b && true ≡ b
true-right-unit-for-&& true  = refl true
true-right-unit-for-&& false = refl false

&&-distributes-over-|| : (a b c : Bool) → a && (b || c) ≡ (a && b) || (a && c)
&&-distributes-over-|| true  true  c     = refl true
&&-distributes-over-|| true  false true  = refl true
&&-distributes-over-|| true  false false = refl false
&&-distributes-over-|| false b     c     = refl false

||-distributes-over-&& : (a b c : Bool) → a || (b && c) ≡ (a || b) && (a || c)
||-distributes-over-&& true  b     c = refl true
||-distributes-over-&& false true  c = refl c
||-distributes-over-&& false false c = refl false


+-suc-on-left : (x y : ℕ) → (suc x) + y ≡ suc (x + y)
+-suc-on-left zero    y = refl (suc y)
+-suc-on-left (suc x) y = refl (suc (suc x) + y)

max : ℕ → ℕ → ℕ
max zero    n       = n
max (suc m) zero    = suc m
max (suc m) (suc n) = suc (max m n)

min : ℕ → ℕ → ℕ
min zero    n       = zero
min (suc m) zero    = zero
min (suc m) (suc n) = suc (min m n)


+-0-on-right : (x : ℕ) → x + 0 ≡ x
+-0-on-right zero    = refl zero
+-0-on-right (suc x) = ap suc IH
 where
  IH : x + 0 ≡ x -- IH is short for induction hypothesis
  IH = +-0-on-right x

+-suc-on-right : (x y : ℕ) → x + suc y ≡ suc (x + y)
+-suc-on-right zero y    = refl (suc y)
+-suc-on-right (suc x) y = ap suc IH
 where
  IH : x + suc y ≡ suc (x + y)
  IH = +-suc-on-right x y

max-idempotent : (x : ℕ) → max x x ≡ x
max-idempotent zero    = refl zero
max-idempotent (suc x) = ap suc IH
 where
  IH : max x x ≡ x
  IH = max-idempotent x

max-commutative : (x y : ℕ) → max x y ≡ max y x
max-commutative zero    zero    = refl zero
max-commutative zero    (suc y) = refl (suc y)
max-commutative (suc x) zero    = refl (suc x)
max-commutative (suc x) (suc y) = ap suc IH
 where
  IH : max x y ≡ max y x
  IH = max-commutative x y

min-idempotent : (x : ℕ) → min x x ≡ x
min-idempotent zero    = refl zero
min-idempotent (suc x) = ap suc IH
 where
  IH : min x x ≡ x
  IH = min-idempotent x

min-commutative : (x y : ℕ) → min x y ≡ min y x
min-commutative zero    zero    = refl zero
min-commutative zero    (suc y) = refl zero
min-commutative (suc x) zero    = refl zero
min-commutative (suc x) (suc y) = ap suc IH
 where
  IH : min x y ≡ min y x
  IH = min-commutative x y
```
