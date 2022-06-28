```agda
{-# OPTIONS --without-K --safe #-}

module Pool.Homework.homework4-solutions where

open import prelude
open import List-functions hiding (++-assoc)

+-comm : (x y : ℕ) → x + y ≡ y + x
+-comm 0       0       = refl zero
+-comm 0       (suc y) =  ap  suc        (+-comm zero y)
+-comm (suc x) 0       =  ap  suc        (+-comm x zero)
+-comm (suc x) (suc y)
 = suc (x + suc y)     ≡⟨ ap  suc        (+-comm x (suc y)) ⟩
   suc (suc (y + x))   ≡⟨ ap (suc ∘ suc) (+-comm y x)       ⟩
   suc (suc x + y)     ≡⟨ ap  suc        (+-comm (suc x) y) ⟩
   suc (y + suc x)     ∎

data _≼_ {X : Type} : List X → List X → Type where
 []-is-prefix : (xs : List X) → [] ≼ xs
 ::-is-prefix : (x : X) (xs ys : List X)
              → xs ≼ ys → (x :: xs) ≼ (x :: ys)

_≼'_ : {X : Type} → List X → List X → Type
_≼'_ {X} xs ys = Σ zs ꞉ List X , xs ++ zs ≡ ys


++-assoc : {X : Type} (xs ys zs : List X)
         → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc []        ys zs = refl (ys ++ zs)
++-assoc (x :: xs) ys zs = ap (λ - → x :: -) IH
  where
    IH : (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
    IH = ++-assoc xs ys zs

≼'-is-transitive : {X : Type} (xs ys zs : List X)
                 → xs ≼' ys → ys ≼' zs → xs ≼' zs
≼'-is-transitive xs ys zs (l , e) (l' , e') = ((l ++ l') , e'')
 where
  e'' : xs ++ l ++ l' ≡ zs
  e'' = xs ++ l ++ l'   ≡⟨ sym (++-assoc xs l l') ⟩
        (xs ++ l) ++ l' ≡⟨ ap (λ - → - ++ l') e ⟩
        ys ++ l'        ≡⟨ e' ⟩
        zs              ∎


≼-++ : {X : Type} (xs ys : List X) → xs ≼ (xs ++ ys)
≼-++ [] ys        = []-is-prefix ys
≼-++ (x :: xs) ys = ::-is-prefix x xs (xs ++ ys) IH
 where
  IH : xs ≼ (xs ++ ys)
  IH = ≼-++ xs ys

≼-unprime : {X : Type} (xs ys : List X) → xs ≼' ys → xs ≼ ys
≼-unprime xs _ (zs , refl _) = ≼-++ xs zs


≼'-[] : {X : Type} (xs : List X) → [] ≼' xs
≼'-[] xs = (xs , refl xs)

≼'-cons : {X : Type} (x : X) (xs ys : List X)
        → xs ≼' ys
        → (x :: xs) ≼' (x :: ys)
≼'-cons x xs ys (zs , e) = (zs , ap (λ - → x :: -) e)

≼-prime : {X : Type} (xs ys : List X) → xs ≼ ys → xs ≼' ys
≼-prime []        ys        ([]-is-prefix ys)        = ≼'-[] ys
≼-prime (x :: xs) (x :: ys) (::-is-prefix x xs ys h) = ≼'-cons x xs ys IH
 where
  IH : xs ≼' ys
  IH = ≼-prime xs ys h


≼-is-transitive : {X : Type} (xs ys zs : List X)
                → xs ≼ ys → ys ≼ zs → xs ≼ zs
≼-is-transitive xs ys zs p q = ≼-unprime xs zs
                                (≼'-is-transitive xs ys zs (≼-prime xs ys p)
                                                           (≼-prime ys zs q))
```
