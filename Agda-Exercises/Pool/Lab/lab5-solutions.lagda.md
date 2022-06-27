```agda
{-# OPTIONS --without-K --safe #-}

module Pool.Lab.lab5-solutions where

open import prelude
open import natural-numbers-functions hiding (_≤_ ; is-even ; +-assoc ; +-comm)
open import List-functions
open import isomorphisms

open import decidability
open import negation

open import Pool.Homework.homework4-solutions
open import Pool.Lab.lab4-solutions


{- Verbose solution, manually performing and showing many equalities that hold
   by definition. -}
map-preserves-length : {A B : Type} (f : A → B) (xs : List A)
                     → length (map f xs) ≡ length xs
map-preserves-length f []        = refl _
map-preserves-length f (x :: xs) =
 length (map f (x :: xs))   ≡⟨ refl _ ⟩
 length (f x :: (map f xs)) ≡⟨ refl _ ⟩
 1 + length (map f xs)      ≡⟨ ap (1 +_) IH ⟩
 1 + length xs              ∎
  where
   IH : length (map f xs) ≡ length xs
   IH = map-preserves-length f xs

{- Alternative, shorter solution that relies on Agda computing the necessary
   equalities for us.
   We come up with such proofs by looking at the goal, using `C-c C-,`, which
   we sometimes normalize (by prefixing the command by `C-u C-u`) to let Agda
   do even more work for us. -}
map-preserves-length' : {A B : Type} (f : A → B) (xs : List A)
                      → length (map f xs) ≡ length xs
map-preserves-length' f []        = refl _
map-preserves-length' f (x :: xs) = ap suc (map-preserves-length' f xs)

{- Verbose solution, manually performing and showing many equalities that hold
   by definition. -}
length-of-++ : {A : Type} (xs ys : List A)
             → length (xs ++ ys) ≡ length xs + length ys
length-of-++ []        ys = refl (length ys)
length-of-++ (x :: xs) ys =
  length ((x :: xs) ++ ys)      ≡⟨ refl _ ⟩
  length (x :: (xs ++ ys))      ≡⟨ refl _ ⟩
  (1 + length (xs ++ ys))       ≡⟨ ap (1 +_) IH ⟩
  (1 + (length xs + length ys)) ≡⟨ +-assoc 1 (length xs) (length ys) ⟩
  (1 + length xs) + length ys   ≡⟨ refl _ ⟩
  length (x :: xs) + length ys  ∎
 where
   IH : length (xs ++ ys) ≡ length xs + length ys
   IH = length-of-++ xs ys

 {- Alternative, shorter solution that relies on Agda computing the necessary
    equalities for us.
    We come up with such proofs by looking at the goal, using `C-c C-,`, which
    we sometimes normalize (by prefixing the command by `C-u C-u`) to let Agda
    do even more work for us. -}
length-of-++' : {A : Type} (xs ys : List A)
              → length (xs ++ ys) ≡ length xs + length ys
length-of-++' []        ys = refl (length ys)
length-of-++' (x :: xs) ys = ap suc IH
  where
   IH : length (xs ++ ys) ≡ length xs + length ys
   IH = length-of-++ xs ys

length-of-prefix : {A : Type} (xs ys : List A)
                 → xs ≼' ys
                 → length xs ≤' length ys
length-of-prefix xs ys (zs , e) = (length zs , goal)
 where
  goal = length xs + length zs ≡⟨ sym (length-of-++ xs zs) ⟩
         length (xs ++ zs)     ≡⟨ ap length e              ⟩
         length ys             ∎

is-nonempty : {A : Type} → List A → Type
is-nonempty xs = 1 ≤' length xs

tail : {A : Type} (xs : List A) → is-nonempty xs → List A
tail (x :: xs) p = xs

head : {A : Type} (xs : List A) → is-nonempty xs → A
head (x :: xs) p = x

length-of-tail : {A : Type} (xs : List A) (p : is-nonempty xs)
               → 1 + length (tail xs p) ≡ length xs
length-of-tail (x :: xs) p =
 1 + length (tail (x :: xs) p) ≡⟨ refl _ ⟩
 1 + length xs                 ≡⟨ refl _ ⟩
 length (x :: xs)              ∎

≤'-suc-lemma : (n : ℕ) → n ≤' (1 + n)
≤'-suc-lemma zero    = (1 , refl 1)
≤'-suc-lemma (suc n) = (1 , goal)
 where
  goal : suc n + 1 ≡ 1 + suc n
  goal = +-comm (suc n) 1

length-of-tail-decreases : {A : Type} (xs : List A) (p : is-nonempty xs)
                         → length (tail xs p) ≤' length xs
length-of-tail-decreases (x :: xs) p = goal
 where
  goal : length xs ≤' (1 + length xs)
  goal = ≤'-suc-lemma (length xs)

×-iso : (X Y : Type) → X × Y ≅ Y × X
×-iso X Y = record { bijection = f ; bijectivity = f-is-bijection }
 where
  f : X × Y → Y × X
  f (x , y) = y , x

  g : Y × X → X × Y
  g (y , x) = x , y

  gf : g ∘ f ∼ id
  gf (x , y) = refl (x , y)

  fg : f ∘ g ∼ id
  fg (y , x) = refl (y , x)

  f-is-bijection : is-bijection f
  f-is-bijection = record { inverse = g ; η = gf ; ε = fg }

+-iso : (X Y : Type) → X ∔ Y ≅ Y ∔ X
+-iso X Y = record { bijection = f ; bijectivity = f-is-bijection }
 where
  f : X ∔ Y → Y ∔ X
  f (inl x) = inr x
  f (inr y) = inl y

  g : Y ∔ X → X ∔ Y
  g (inl y) = inr y
  g (inr x) = inl x

  gf : g ∘ f ∼ id
  gf (inl x) = refl (inl x)
  gf (inr y) = refl (inr y)

  fg : f ∘ g ∼ id
  fg (inl y) = refl (inl y)
  fg (inr x) = refl (inr x)

  f-is-bijection : is-bijection f
  f-is-bijection = record { inverse = g ; η = gf ; ε = fg }

lists-from-vectors : {A : Type} → List A ≅ (Σ n ꞉ ℕ , Vector A n)
lists-from-vectors {A}
 = record { bijection = f ; bijectivity = f-is-bijection }
 where
  f : List A → Σ n ꞉ ℕ , Vector A n
  f []        = 0 , []
  f (x :: xs) = suc (fst (f xs)) , (x :: snd (f xs))

  g : Σ n ꞉ ℕ , Vector A n → List A
  g (0     , []       ) = []
  g (suc n , (x :: xs)) = x :: g (n , xs)

  gf : g ∘ f ∼ id
  gf []        = refl []
  gf (x :: xs) = ap (x ::_) (gf xs)

  fg : f ∘ g ∼ id
  fg (0     , []       ) = refl (0 , [])
  fg (suc n , (x :: xs))
   = ap (λ - → suc (fst -) , (x :: snd -)) (fg (n , xs))

  f-is-bijection : is-bijection f
  f-is-bijection = record { inverse = g ; η = gf ; ε = fg }

open _≅_

lfv-preserves-length : {A : Type} (xs : List A)
                     → length xs
                     ≡ fst (bijection lists-from-vectors xs)
lfv-preserves-length []        = refl 0
lfv-preserves-length (x :: xs) = ap suc (lfv-preserves-length xs)

is-even : ℕ → Type
is-even x = Σ y ꞉ ℕ , x ≡ 2 * y

check-even : ℕ → Bool
check-even zero          = true
check-even (suc zero)    = false
check-even (suc (suc n)) = check-even n

evenness-lemma₁ : (n : ℕ) → is-even (2 + n) → is-even n
evenness-lemma₁ n (suc k , p) = k , goal
 where
  subgoal : suc (suc n) ≡ suc (suc (2 * k))
  subgoal = suc (suc n)       ≡⟨ p                         ⟩
            suc k + suc k     ≡⟨ ap suc (+-comm k (suc k)) ⟩
            suc ((suc k) + k) ∎

  goal : n ≡ 2 * k
  goal = suc-is-injective (suc-is-injective subgoal)

evenness-lemma₂ : (n : ℕ) → is-even n → is-even (2 + n)
evenness-lemma₂ n (k , p) = suc k , goal
 where
  goal : 2 + n ≡ 2 * suc k
  goal = 2 + n          ≡⟨ ap (λ - → 2 + -) p        ⟩
          2 + (k + k)   ≡⟨ ap suc (+-comm (suc k) k) ⟩
          suc k + suc k ∎

even⇒check-even : (n : ℕ) → is-even n → check-even n ≡ true
even⇒check-even zero _ = refl true
even⇒check-even (suc zero) (suc zero , ())
even⇒check-even (suc zero) (suc (suc _) , ())
even⇒check-even (suc (suc n)) p = even⇒check-even n (evenness-lemma₁ n p)

check-even⇒even : (n : ℕ) → check-even n ≡ true → is-even n
check-even⇒even zero (refl true) = zero , refl zero
check-even⇒even (suc zero) ()
check-even⇒even (suc (suc n)) p = evenness-lemma₂ n (check-even⇒even n p)
```
