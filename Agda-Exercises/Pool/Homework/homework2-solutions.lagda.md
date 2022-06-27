Week 2 - Homework Sheet - Solutions

```agda
{-# OPTIONS --without-K --safe #-}

module Pool.Homework.homework2-solutions where

open import prelude hiding (id ; _∘_)

ap² : {A : Type} (f : A → A) {x y : A} → x ≡ y → f (f x) ≡ f (f y)
ap² f e = ap f (ap f e)

double-not-eq : {a b : Bool} → a ≡ b → not (not a) ≡ not (not b)
double-not-eq e = ap² not e

transport-vec-A : {A : Type} {n m : ℕ} → n ≡ m
                → Vector A n → Vector A m
transport-vec-A (refl n) v = v


map : {A B : Type} → (A → B) → List A → List B
map f []        = []
map f (x :: xs) = f x :: map f xs

id : {A : Type} → A → A
id = λ x → x

_∘_ : {A B C : Type} → (g : B → C) → (f : A → B)→ A → C
g ∘ f = λ x → g (f x)

map-law1 : {A : Type} (xs : List A) → map id xs ≡ xs
map-law1 []        = refl []
map-law1 (x :: xs) = ap (x ::_) IH
 where
  IH : map id xs ≡ xs -- IH is short for induction hypothesis
  IH = map-law1 xs

map-law2 : {A B C : Type} (g : B → C) (f : A → B) (xs : List A)
         → map (g ∘ f) xs ≡ map g (map f xs)
map-law2 g f []        = refl []
map-law2 g f (x :: xs) = ap (g (f x) ::_) IH
 where
  IH : map (g ∘ f) xs ≡ map g (map f xs)
  IH = map-law2 g f xs


and : List Bool → Bool
and []            = true
and (true  :: bs) = and bs
and (false :: bs) = false

and-example1 : and (true :: false :: []) ≡ false
and-example1 = refl false

and-example2 : and [] ≡ true
and-example2 = refl true

for-all : {A : Type} → (A → Bool) → List A → Bool
for-all f xs = and (map f xs)

filter : {A : Type} → (A → Bool) → List A → List A
filter p []        = []
filter p (x :: xs) = if (p x) then x :: ys else ys
 where
  ys = filter p xs

filter-soundness : {A : Type} → Type
filter-soundness {A} = (p : A → Bool) (xs : List A)
                     → for-all p (filter p xs) ≡ true
