```agda
{-# OPTIONS --without-K --safe #-}

module Pool.Lab.lab4-solutions where

open import prelude
open import List-functions

reverse-lemma : {X : Type} (x : X) (xs : List X)
              → x :: reverse xs ≡ reverse (xs ++ [ x ])
reverse-lemma x []        = refl (x :: [])
reverse-lemma x (y :: xs) = ap (_++ [ y ]) (reverse-lemma x xs)

reverse-is-involution : {X : Type} → (xs : List X) → xs ≡ reverse (reverse xs)
reverse-is-involution {X} [] = refl []
reverse-is-involution {X} (x :: xs)
 = x :: xs                       ≡⟨ ap (x ::_) (reverse-is-involution xs) ⟩
   x :: reverse (reverse xs)     ≡⟨ reverse-lemma x (reverse xs)          ⟩
   reverse (reverse xs ++ [ x ]) ≡⟨ refl (reverse (reverse xs ++ [ x ]))  ⟩
   reverse (reverse (x :: xs))   ∎

+-assoc : (x y z : ℕ) → x + (y + z) ≡ (x + y) + z
+-assoc zero    y z = refl (y + z)
+-assoc (suc x) y z = ap suc (+-assoc x y z)


data _≤_ : ℕ → ℕ → Type where
 ≤-zero : (  y : ℕ) → 0 ≤ y
 ≤-suc  : (x y : ℕ) → x ≤ y → suc x ≤ suc y

_≤'_ : ℕ → ℕ → Type
x ≤' y = Σ k ꞉ ℕ , x + k ≡ y


≤'-zero : (y : ℕ) → 0 ≤' y
≤'-zero y = y , refl y

≤'-suc : (x y : ℕ) → x ≤' y → suc x ≤' suc y
≤'-suc x y (n , p) = n , ap suc p

≤-prime : (x y : ℕ) → x ≤ y → x ≤' y
≤-prime 0            y  (≤-zero  y)   = ≤'-zero y
≤-prime (suc x) (suc y) (≤-suc x y p) = ≤'-suc x y (≤-prime x y p)

≤-unprime : (x y : ℕ) → x ≤' y → x ≤ y
≤-unprime zero y (n , p) = ≤-zero y
≤-unprime (suc x) (suc .(x + n)) (n , refl .(suc (x + n)))
 = ≤-suc x (x + n) (≤-unprime x (x + n) (n , refl (x + n)))

≤-trans : (x y z : ℕ) → x ≤ y → y ≤ z → x ≤ z
≤-trans zero y z p q = ≤-zero z
≤-trans (suc x) .(suc y) .(suc z) (≤-suc .x y p) (≤-suc .y z q)
 = ≤-suc x z (≤-trans x y z p q)

≤'-trans : (x y z : ℕ) → x ≤' y → y ≤' z → x ≤' z
≤'-trans x .(x + n) .((x + n) + m) (n , refl .(x + n)) (m , refl .((x + n) + m))
 = (n + m) , +-assoc x n m

is-decidable : Type → Type
is-decidable A = A ∔ ¬ A

has-decidable-equality : Type → Type
has-decidable-equality A = (x y : A) → is-decidable (x ≡ y)

bool-has-decidable-equality : has-decidable-equality Bool
bool-has-decidable-equality true  true  = inl (refl true)
bool-has-decidable-equality true  false = inr (λ ())
bool-has-decidable-equality false true  = inr (λ ())
bool-has-decidable-equality false false = inl (refl false)

≤-lemma : (m n : ℕ) → suc m ≤ suc n → m ≤ n
≤-lemma m n (≤-suc m n p) = p

not-suc-≤-zero : (n : ℕ) → ¬ (suc n ≤ 0)
not-suc-≤-zero n ()

≤-is-decidable : (m n : ℕ) → is-decidable (m ≤ n)
≤-is-decidable zero    zero    = inl (≤-zero zero)
≤-is-decidable zero    (suc n) = inl (≤-zero (suc n))
≤-is-decidable (suc m) zero    = inr (not-suc-≤-zero m)
≤-is-decidable (suc m) (suc n) = ∔-nondep-elim f g IH
 where
  IH : (m ≤ n) ∔ ¬ (m ≤ n)
  IH = ≤-is-decidable m n
  f : m ≤ n → is-decidable (suc m ≤ suc n)
  f p = inl (≤-suc m n p)
  g : ¬ (m ≤ n) → is-decidable (suc m ≤ suc n)
  g p = inr (λ q → p (≤-lemma m n q))
```
