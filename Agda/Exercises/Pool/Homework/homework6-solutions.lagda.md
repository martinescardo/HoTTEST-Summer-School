```agda
{-# OPTIONS --without-K --safe #-}

module Pool.Homework.homework6-solutions where

open import prelude
open import isomorphisms
open import natural-numbers-functions
open import Fin
open import Vector


×-distributivity-+ : (X Y Z : Type) → (X ∔ Y) × Z ≅ (X × Z) ∔ (Y × Z)
×-distributivity-+ X Y Z =
 record { bijection = f
        ; bijectivity = record { inverse = g
                               ; η       = section
                               ; ε       = retraction } }
  where
   f : (X ∔ Y) × Z → (X × Z) ∔ (Y × Z)
   f (inl x , z) = inl (x , z)
   f (inr y , z) = inr (y , z)

   g : (X × Z) ∔ (Y × Z) → (X ∔ Y) × Z
   g (inl (x , z)) = inl x , z
   g (inr (y , z)) = inr y , z

   section : (g ∘ f) ∼ id
   section (inl x , z) = refl (inl x , z)
   section (inr y , z) = refl (inr y , z)

   retraction : (f ∘ g) ∼ id
   retraction (inl (x , z)) = refl (inl (x , z))
   retraction (inr (y , z)) = refl (inr (y , z))

alternate : Type → Type → Bool → Type
alternate X _ true  = X
alternate _ Y false = Y

∔-isomorphic-to-Σ-bool : (X Y : Type) → (X ∔ Y) ≅ (Σ b ꞉ Bool , alternate X Y b)
∔-isomorphic-to-Σ-bool X Y =
 record { bijection = f ; bijectivity = record { inverse = g
                                               ; η       = section
                                               ; ε       = retraction } }
  where
   f : X ∔ Y → Σ b ꞉ Bool , alternate X Y b
   f (inl x) = true  , x
   f (inr y) = false , y

   g : (Σ b ꞉ Bool , alternate X Y b) → X ∔ Y
   g (true  , X) = inl X
   g (false , Y) = inr Y

   section : (g ∘ f) ∼ id
   section (inl x) = refl (inl x)
   section (inr y) = refl (inr y)

   retraction : (f ∘ g) ∼ id
   retraction (true  , X) = refl (true  , X)
   retraction (false , Y) = refl (false , Y)


fib : ℕ → ℕ
fib 0 = 0
fib 1 = 1
fib (suc (suc n)) = fib n + fib (suc n)

fib-aux : ℕ → ℕ → ℕ → ℕ
fib-aux a b 0       = b
fib-aux a b (suc n) = fib-aux (b + a) a n

fib-fast : ℕ → ℕ
fib-fast = fib-aux 1 0

fib-aux-fib-lemma : (k n : ℕ) → fib-aux (fib (suc n)) (fib n) k ≡ fib (k + n)
fib-aux-fib-lemma zero    n = refl (fib n)
fib-aux-fib-lemma (suc k) n =
 fib-aux (fib n + fib (1 + n)) (fib (1 + n)) k ≡⟨ refl _              ⟩
 fib-aux (fib (2 + n)) (fib (1 + n)) k         ≡⟨ IH                  ⟩
 fib (k + suc n)                               ≡⟨ ap fib (+-step k n) ⟩
 fib (suc (k + n))                             ∎
 where
  IH : fib-aux (fib (2 + n)) (fib (1 + n)) k ≡ fib (k + suc n)
  IH = fib-aux-fib-lemma k (suc n)

fib-fast-is-correct : (n : ℕ) → fib-fast n ≡ fib n
fib-fast-is-correct n = fib-fast n    ≡⟨ refl _            ⟩
                        fib-aux 1 0 n ≡⟨ claim             ⟩
                        fib (n + 0)   ≡⟨ ap fib (+-base n) ⟩
                        fib n         ∎
 where
  lemma : fib-aux (fib 1) (fib 0) n ≡ fib (n + 0)
  lemma = fib-aux-fib-lemma n 0
  claim : fib-aux 1 0 n ≡ fib (n + 0)
  claim = lemma
```
