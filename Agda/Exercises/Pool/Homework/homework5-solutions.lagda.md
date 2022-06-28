```agda
{-# OPTIONS --without-K --safe #-}

module Pool.Homework.homework5-solutions where

open import prelude hiding (Bool-elim)
open import natural-numbers-functions hiding (_≤_ ; is-even ; +-assoc ; +-comm)
open import List-functions
open import isomorphisms
open import negation

open import Pool.Homework.homework4-solutions
open import Pool.Lab.lab4-solutions
open import Pool.Lab.lab5-solutions

length-of-reverse : {A : Type} (xs : List A)
                  → length (reverse xs) ≡ length xs
length-of-reverse []        = refl 0
length-of-reverse (x :: xs) =
  length (reverse xs ++ [ x ])       ≡⟨ length-of-++ (reverse xs) [ x ] ⟩
  length (reverse xs) + length [ x ] ≡⟨ refl _                          ⟩
  length (reverse xs) + 1            ≡⟨ ap (_+ 1) IH                    ⟩
  length xs + 1                      ≡⟨ +-comm (length xs) 1            ⟩
  1 + length xs                      ∎
   where
    IH : length (reverse xs) ≡ length xs
    IH = length-of-reverse xs

ℕ-[⋆]-iso : ℕ ≅ List 𝟙
ℕ-[⋆]-iso = record { bijection = f ; bijectivity = f-is-bijection }
 where
  f : ℕ → List 𝟙
  f 0       = []
  f (suc n) = ⋆ :: f n

  g : List 𝟙 → ℕ
  g []        = 0
  g (⋆ :: ⋆s) = suc (g ⋆s)

  gf : g ∘ f ∼ id
  gf 0       = refl 0
  gf (suc n) = ap suc (gf n)

  fg : f ∘ g ∼ id
  fg [] = refl []
  fg (⋆ :: ⋆s) = ap (⋆ ::_) (fg ⋆s)

  f-is-bijection : is-bijection f
  f-is-bijection = record { inverse = g ; η = gf ; ε = fg }

open _≅_

ℕ→[⋆]-preserves-length : (n : ℕ) → length (bijection ℕ-[⋆]-iso n) ≡ n
ℕ→[⋆]-preserves-length zero = refl 0
ℕ→[⋆]-preserves-length (suc n) = ap suc (ℕ→[⋆]-preserves-length n)

principle-of-bivalence : (b : Bool) → (b ≡ true) ∔ (b ≡ false)
principle-of-bivalence true  = inl (refl true)
principle-of-bivalence false = inr (refl false)

is-even-is-decidable : (n : ℕ) → is-decidable (is-even n)
is-even-is-decidable n =
 ∔-nondep-elim goal₁ goal₂ (principle-of-bivalence (check-even n))
  where
   goal₁ : check-even n ≡ true → is-decidable (is-even n)
   goal₁ p = inl (check-even⇒even n p)

   goal₂ : check-even n ≡ false → is-decidable (is-even n)
   goal₂ p = inr subgoal
    where
     subgoal : ¬ is-even n
     subgoal q = true-is-not-false (true         ≡⟨ sym (even⇒check-even n q) ⟩
                                    check-even n ≡⟨ p ⟩
                                    false        ∎)

filter : {A : Type} → (A → Bool) → List A → List A
filter P []        = []
filter P (x :: xs) = if P x then (x :: ys) else ys
 where
  ys = filter P xs

≤-suc-lemma : (n : ℕ) → n ≤ (1 + n)
≤-suc-lemma 0       = ≤-zero (1 + 0)
≤-suc-lemma (suc n) = goal
 where
  IH : n ≤ (1 + n)
  IH = ≤-suc-lemma n
  goal : suc n ≤ suc (suc n)
  goal = ≤-suc n (suc n) IH

Bool-elim : (A : Bool → Type)
          → A false
          → A true
          → (x : Bool) → A x
Bool-elim A x₀ x₁ false = x₀
Bool-elim A x₀ x₁ true  = x₁

length-of-filter : {A : Type} (P : A → Bool) (xs : List A)
                 → length (filter P xs) ≤ length xs
length-of-filter P []        = ≤-zero 0
length-of-filter P (x :: xs) = Bool-elim goal-statement false-case
                                                         true-case
                                                         (P x)
 where
  ys = filter P xs

  {- Note that by definition
       filter P (x :: xs) = if P x then (x :: ys) else ys
     and so goal-statement is almost
       length (filter P (x :: xs)) ≤ length (x :: xs)
     except that we replace "P x" by the Boolean "b". -}
  goal-statement : Bool → Type
  goal-statement b = length (if b then (x :: ys) else ys) ≤ length (x :: xs)

  IH : length ys ≤ length xs
  IH = length-of-filter P xs

  {- The type of "false-case" is equal to "goal-statement false". -}
  false-case : length ys ≤ length (x :: xs)
  false-case = ≤-trans (length ys) (length xs) (length (x :: xs))
                 IH (≤-suc-lemma (length xs))

  {- The type of "true-case" is equal to "goal-statement true". -}
  true-case : length (x :: ys) ≤ length (x :: xs)
  true-case = ≤-suc (length ys) (length xs) IH

{- Here is a version that uses Agda's built-in with-keyword (as shown by Eric in
   the lab of 28 Feb) instead of Bool-elim. (Under the hood, they amount to the
   same thing.) -}
length-of-filter' : {A : Type} (P : A → Bool) (xs : List A)
                  → length (filter P xs) ≤ length xs
length-of-filter' P []        = ≤-zero 0

length-of-filter' P (x :: xs) with P x
length-of-filter' P (x :: xs)    | true  = true-case
 where
  ys = filter P xs

  IH : length ys ≤ length xs
  IH = length-of-filter' P xs

  true-case : length (x :: ys) ≤ length (x :: xs)
  true-case = ≤-suc (length ys) (length xs) IH

length-of-filter' P (x :: xs)    | false = false-case
 where
  ys = filter P xs

  IH : length ys ≤ length xs
  IH = length-of-filter' P xs

  false-case : length ys ≤ length (x :: xs)
  false-case = ≤-trans (length ys) (length xs) (length (x :: xs))
                 IH (≤-suc-lemma (length xs))

length-of-filters : {A : Type} (P : A → Bool) (xs : List A)
                  → length (filter P xs) + length (filter (not ∘ P) xs)
                  ≡ length xs
length-of-filters P []        = refl _
length-of-filters P (x :: xs) = Bool-elim goal-statement false-case
                                                         true-case
                                                         (P x)
 where
  ys  = filter P xs
  ys' = filter (not ∘ P) xs

  IH : length ys + length ys' ≡ length xs
  IH = length-of-filters P xs

  {- Note that by definition
       filter P (x :: xs) = if P x then (x :: ys) else ys
     and so goal-statement is almost
         length (filter P         (x :: xs)) +
         length (filter (not ∘ P) (x :: xs))
       ≡ length (x :: xs)
     except that we replace "P x" by the Boolean "b". -}
  goal-statement : Bool → Type
  goal-statement b = length (if b     then (x :: ys ) else ys ) +
                     length (if not b then (x :: ys') else ys')
                   ≡ 1 + length xs

  {- The type of "false-case" is equal to "goal-statement false. -}
  false-case : length ys + length (x :: ys') ≡ length (x :: xs)
  false-case =
   length ys + length (x :: ys') ≡⟨ refl _                                    ⟩
   length ys + (1 + length ys')  ≡⟨ +-assoc (length ys) 1 (length ys')        ⟩
   (length ys + 1) + length ys'  ≡⟨ ap (_+ length ys') (+-comm (length ys) 1) ⟩
   (1 + length ys) + length ys'  ≡⟨ sym (+-assoc 1 (length ys) (length ys'))  ⟩
   1 + (length ys + length ys')  ≡⟨ ap (1 +_) IH                              ⟩
   1 + length xs                 ∎

   {- The type of "true-case" is equal to "goal-statement true". -}
  true-case : length (x :: ys) + length ys' ≡ length (x :: xs)
  true-case =
   length (x :: ys) + length ys' ≡⟨ refl _                             ⟩
   (1 + length ys) + length ys'  ≡⟨ +-assoc 1 (length ys) (length ys') ⟩
   1 + (length ys + length ys')  ≡⟨ ap (1 +_) IH                       ⟩
   1 + length xs                 ∎

{- Here is a version that uses Agda's built-in with-keyword (as shown by Eric in
   the lab of 28 Feb) instead of Bool-elim. (Under the hood, they amount to the
   same thing.) -}
length-of-filters' : {A : Type} (P : A → Bool) (xs : List A)
                   → length (filter P xs) + length (filter (not ∘ P) xs)
                   ≡ length xs
length-of-filters' P []        = refl _

length-of-filters' P (x :: xs) with P x
length-of-filters' P (x :: xs)    | true  = true-case
 where
  ys  = filter P xs
  ys' = filter (not ∘ P) xs

  IH : length ys + length ys' ≡ length xs
  IH = length-of-filters P xs

  true-case : length (x :: ys) + length ys' ≡ length (x :: xs)
  true-case =
   length (x :: ys) + length ys' ≡⟨ refl _                             ⟩
   (1 + length ys) + length ys'  ≡⟨ +-assoc 1 (length ys) (length ys') ⟩
   1 + (length ys + length ys')  ≡⟨ ap (1 +_) IH                       ⟩
   1 + length xs                 ∎

length-of-filters' P (x :: xs)    | false = false-case
 where
  ys  = filter P xs
  ys' = filter (not ∘ P) xs

  IH : length ys + length ys' ≡ length xs
  IH = length-of-filters P xs

  false-case : length ys + length (x :: ys') ≡ length (x :: xs)
  false-case =
   length ys + length (x :: ys') ≡⟨ refl _                                    ⟩
   length ys + (1 + length ys')  ≡⟨ +-assoc (length ys) 1 (length ys')        ⟩
   (length ys + 1) + length ys'  ≡⟨ ap (_+ length ys') (+-comm (length ys) 1) ⟩
   (1 + length ys) + length ys'  ≡⟨ sym (+-assoc 1 (length ys) (length ys'))  ⟩
   1 + (length ys + length ys')  ≡⟨ ap (1 +_) IH                              ⟩
   1 + length xs                 ∎
```
