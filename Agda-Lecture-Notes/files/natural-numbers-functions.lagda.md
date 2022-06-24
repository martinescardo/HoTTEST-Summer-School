
Martin Escardo.
Notes originally written for the module "Advanced Functional Programming"
at the School of Computer Science of the University of Birmingham, UK.


<!--
```agda
{-# OPTIONS --without-K --safe #-}

module natural-numbers-functions where


open import prelude
open import negation
```
-->
# Natural numbers functions, relations and properties

## Some general properties

```agda
suc-is-not-zero : {x : ℕ} → suc x ≢ 0
suc-is-not-zero ()

zero-is-not-suc : {x : ℕ} → 0 ≢ suc x
zero-is-not-suc ()

pred : ℕ → ℕ
pred 0       = 0
pred (suc n) = n

suc-is-injective : {x y : ℕ} → suc x ＝ suc y → x ＝ y
suc-is-injective = ap pred
```

## Order relation _≤_

The less-than order on natural numbers can be defined in a number of
equivalent ways. The first one says that `x ≤ y` iff `x + z ＝ y` for
some `z`:
```agda
_≤₀_ : ℕ → ℕ → Type
x ≤₀ y = Σ a ꞉ ℕ , x + a ＝ y
```
The second one is defined by recursion:
```agda
_≤₁_ : ℕ → ℕ → Type
0     ≤₁ y     = 𝟙
suc x ≤₁ 0     = 𝟘
suc x ≤₁ suc y = x ≤₁ y
```
The third one, which we will as the official one, is defined *by induction* using `data`:
```agda
data _≤_ : ℕ → ℕ → Type where
 0-smallest      : {y : ℕ} → 0 ≤ y
 suc-preserves-≤ : {x y : ℕ} → x ≤ y → suc x ≤ suc y

_≥_ : ℕ → ℕ → Type
x ≥ y = y ≤ x

infix 0 _≤_
infix 0 _≥_
```

We will now show some properties of these relations.
```agda
suc-reflects-≤ : {x y : ℕ} → suc x ≤ suc y → x ≤ y
suc-reflects-≤ {x} {y} (suc-preserves-≤ l) = l

suc-preserves-≤₀ : {x y : ℕ} → x ≤₀ y → suc x ≤₀ suc y
suc-preserves-≤₀ {x} {y} (a , p) = γ
 where
  q : suc (x + a) ＝ suc y
  q = ap suc p

  γ : suc x ≤₀ suc y
  γ = (a , q)

≤₀-implies-≤₁ : {x y : ℕ} → x ≤₀ y → x ≤₁ y
≤₀-implies-≤₁ {zero}  {y}     (a , p) = ⋆
≤₀-implies-≤₁ {suc x} {suc y} (a , p) = IH
 where
  q : x + a ＝ y
  q = suc-is-injective p

  γ : x ≤₀ y
  γ = (a , q)

  IH : x ≤₁ y
  IH = ≤₀-implies-≤₁ {x} {y} γ

≤₁-implies-≤ : {x y : ℕ} → x ≤₁ y → x ≤ y
≤₁-implies-≤ {zero}  {y}     l = 0-smallest
≤₁-implies-≤ {suc x} {suc y} l = γ
 where
  IH : x ≤ y
  IH = ≤₁-implies-≤ l

  γ : suc x ≤ suc y
  γ = suc-preserves-≤ IH

≤-implies-≤₀ : {x y : ℕ} → x ≤ y → x ≤₀ y
≤-implies-≤₀ {0}     {y}      0-smallest         = (y , refl y)
≤-implies-≤₀ {suc x} {suc y} (suc-preserves-≤ l) = γ
 where
  IH : x ≤₀ y
  IH = ≤-implies-≤₀ {x} {y} l

  γ : suc x ≤₀ suc y
  γ = suc-preserves-≤₀ IH
```

## Exponential function

```agda
_^_ : ℕ → ℕ → ℕ
y ^ 0     = 1
y ^ suc x = y * y ^ x

infix 40 _^_
```

## Maximum and minimum

```agda
max : ℕ → ℕ → ℕ
max 0       y       = y
max (suc x) 0       = suc x
max (suc x) (suc y) = suc (max x y)

min : ℕ → ℕ → ℕ
min 0       y       = 0
min (suc x) 0       = 0
min (suc x) (suc y) = suc (min x y)
```

## No natural number is its own successo

We now show that there is no natural number `x` such that `x = suc x`.
```agda
every-number-is-not-its-own-successor : (x : ℕ) → x ≢ suc x
every-number-is-not-its-own-successor 0       e = zero-is-not-suc e
every-number-is-not-its-own-successor (suc x) e = goal
 where
  IH : x ≢ suc x
  IH = every-number-is-not-its-own-successor x

  e' : x ＝ suc x
  e' = suc-is-injective e

  goal : 𝟘
  goal = IH e'

there-is-no-number-which-is-its-own-successor : ¬ (Σ x ꞉ ℕ , x ＝ suc x)
there-is-no-number-which-is-its-own-successor (x , e) = every-number-is-not-its-own-successor x e
```

## Prime numbers

```agda
is-prime : ℕ → Type
is-prime n = (n ≥ 2) × ((x y : ℕ) → x * y ＝ n → (x ＝ 1) ∔ (x ＝ n))
```
**Exercise.** Show that `is-prime n` is [decidable](decidability.lagda.md) for every `n : ℕ`. Hard.

The following is a conjecture that so far mathematicians haven't been able to prove or disprove. But we can still say what the conjecture is in Agda:
```agda
twin-prime-conjecture : Type
twin-prime-conjecture = (n : ℕ) → Σ p ꞉ ℕ , (p ≥ n)
                                          × is-prime p
                                          × is-prime (p + 2)
```

## Properties of addition

```agda
+-base : (x : ℕ) → x + 0 ＝ x
+-base 0       = 0 + 0       ＝⟨ refl _ ⟩
                 0           ∎

+-base (suc x) = suc (x + 0) ＝⟨ ap suc (+-base x) ⟩
                 suc x       ∎

+-step : (x y : ℕ) → x + suc y ＝ suc (x + y)
+-step 0       y = 0 + suc y         ＝⟨ refl _ ⟩
                   suc y             ∎

+-step (suc x) y = suc x + suc y     ＝⟨ refl _ ⟩
                   suc (x + suc y)   ＝⟨ ap suc (+-step x y) ⟩
                   suc (suc (x + y)) ＝⟨ refl _ ⟩
                   suc (suc x + y)   ∎

+-comm : (x y : ℕ) → x + y ＝ y + x
+-comm 0       y = 0 + y       ＝⟨ refl _ ⟩
                   y           ＝⟨ sym (+-base y) ⟩
                   y + 0       ∎

+-comm (suc x) y = suc x + y   ＝⟨ refl _ ⟩
                          suc (x + y) ＝⟨ ap suc (+-comm x y) ⟩
                          suc (y + x) ＝⟨ refl _ ⟩
                          suc y + x   ＝⟨ sym (+-step y x) ⟩
                          y + suc x   ∎
```

## Associativity of addition

```agda
+-assoc : (x y z : ℕ) → (x + y) + z ＝ x + (y + z)
+-assoc 0       y z = refl (y + z)
+-assoc (suc x) y z =
   (suc x + y) + z   ＝⟨ refl _ ⟩
   suc (x + y) + z   ＝⟨ refl _ ⟩
   suc ((x + y) + z) ＝⟨ ap suc (+-assoc x y z) ⟩
   suc (x + (y + z)) ＝⟨ refl _ ⟩
   suc x + (y + z)   ∎

+-assoc' : (x y z : ℕ) → (x + y) + z ＝ x + (y + z)
+-assoc' 0       y z = refl (y + z)
+-assoc' (suc x) y z = ap suc (+-assoc' x y z)
```

## 1 is a neutral element of multiplication

```agda
1-*-left-neutral : (x : ℕ) → 1 * x ＝ x
1-*-left-neutral x = refl x

1-*-right-neutral : (x : ℕ) → x * 1 ＝ x
1-*-right-neutral 0       = refl 0
1-*-right-neutral (suc x) =
   suc x * 1 ＝⟨ refl _ ⟩
   x * 1 + 1 ＝⟨ ap (_+ 1) (1-*-right-neutral x) ⟩
   x + 1     ＝⟨ +-comm x 1 ⟩
   1 + x     ＝⟨ refl _ ⟩
   suc x     ∎
```

## Multiplication distributes over addition:

```agda
*-+-distrib : (x y z : ℕ) → x * (y + z) ＝ x * y + x * z
*-+-distrib 0       y z = refl 0
*-+-distrib (suc x) y z = goal
 where
  IH : x * (y + z) ＝ x * y + x * z
  IH = *-+-distrib x y z

  goal : suc x * (y + z) ＝ suc x * y + suc x * z
  goal = suc x * (y + z)         ＝⟨ refl _ ⟩
         x * (y + z) + (y + z)   ＝⟨ ap (_+ y + z) IH ⟩
         (x * y + x * z) + y + z ＝⟨ +-assoc (x * y) (x * z) (y + z) ⟩
         x * y + x * z + y + z   ＝⟨ ap (x * y +_) (sym (+-assoc (x * z) y z)) ⟩
         x * y + (x * z + y) + z ＝⟨ ap (λ - → x * y + - + z) (+-comm (x * z) y) ⟩
         x * y + (y + x * z) + z ＝⟨ ap (x * y +_) (+-assoc y (x * z) z) ⟩
         x * y + y + x * z + z   ＝⟨ sym (+-assoc (x * y) y (x * z + z)) ⟩
         (x * y + y) + x * z + z ＝⟨ refl _ ⟩
         suc x * y + suc x * z   ∎
```

## Commutativity of multiplication

```agda
*-base : (x : ℕ) → x * 0 ＝ 0
*-base 0       = refl 0
*-base (suc x) =
   suc x * 0 ＝⟨ refl _ ⟩
   x * 0 + 0 ＝⟨ ap (_+ 0) (*-base x) ⟩
   0 + 0     ＝⟨ refl _ ⟩
   0 ∎

*-comm : (x y : ℕ) → x * y ＝ y * x
*-comm 0       y = sym (*-base y)
*-comm (suc x) y =
   suc x * y     ＝⟨ refl _ ⟩
   x * y + y     ＝⟨ +-comm (x * y) y ⟩
   y + x * y     ＝⟨ ap (y +_) (*-comm x y) ⟩
   y + y * x     ＝⟨ ap (_+ (y * x)) (sym (1-*-right-neutral y)) ⟩
   y * 1 + y * x ＝⟨ sym (*-+-distrib y 1 x) ⟩
   y * (1 + x)   ＝⟨ refl _ ⟩
   y * suc x     ∎

```

## Associativity of multiplication

```agda
*-assoc : (x y z : ℕ) → (x * y) * z ＝ x * (y * z)
*-assoc zero    y z = refl _
*-assoc (suc x) y z = (x * y + y) * z     ＝⟨ *-comm (x * y + y) z             ⟩
                      z * (x * y + y)     ＝⟨ *-+-distrib z (x * y) y          ⟩
                      z * (x * y) + z * y ＝⟨ ap (z * x * y +_) (*-comm z y)   ⟩
                      z * (x * y) + y * z ＝⟨ ap (_+ y * z) (*-comm z (x * y)) ⟩
                      (x * y) * z + y * z ＝⟨ ap (_+ y * z) (*-assoc x y z)    ⟩
                      x * y * z + y * z   ∎
```


## Even and odd numbers

```agda
is-even is-odd : ℕ → Type
is-even x = Σ y ꞉ ℕ , x ＝ 2 * y
is-odd  x = Σ y ꞉ ℕ , x ＝ 1 + 2 * y

zero-is-even : is-even 0
zero-is-even = 0 , refl 0

ten-is-even : is-even 10
ten-is-even = 5 , refl _

zero-is-not-odd : ¬ is-odd 0
zero-is-not-odd ()

one-is-not-even : ¬ is-even 1
one-is-not-even (0 , ())
one-is-not-even (suc (suc x) , ())

one-is-not-even' : ¬ is-even 1
one-is-not-even' (suc zero , ())

one-is-odd : is-odd 1
one-is-odd = 0 , refl 1

even-gives-odd-suc : (x : ℕ) → is-even x → is-odd (suc x)
even-gives-odd-suc x (y , e) = goal
 where
  e' : suc x ＝ 1 + 2 * y
  e' = ap suc e

  goal : is-odd (suc x)
  goal = y , e'

even-gives-odd-suc' : (x : ℕ) → is-even x → is-odd (suc x)
even-gives-odd-suc' x (y , e) = y , ap suc e

odd-gives-even-suc : (x : ℕ) → is-odd x → is-even (suc x)
odd-gives-even-suc x (y , e) = goal
 where
  y' : ℕ
  y' = 1 + y

  e' : suc x ＝ 2 * y'
  e' = suc x           ＝⟨ ap suc e ⟩
       suc (1 + 2 * y) ＝⟨ refl _ ⟩
       2 + 2 * y       ＝⟨ sym (*-+-distrib 2 1 y) ⟩
       2 * (1 + y)     ＝⟨ refl _ ⟩
       2 * y'          ∎

  goal : is-even (suc x)
  goal = y' , e'

even-or-odd : (x : ℕ) → is-even x ∔ is-odd x
even-or-odd 0       = inl (0 , refl 0)
even-or-odd (suc x) = goal
 where
  IH : is-even x ∔ is-odd x
  IH = even-or-odd x

  f : is-even x ∔ is-odd x → is-even (suc x) ∔ is-odd (suc x)
  f (inl e) = inr (even-gives-odd-suc x e)
  f (inr o) = inl (odd-gives-even-suc x o)

  goal : is-even (suc x) ∔ is-odd (suc x)
  goal = f IH
```

```agda
even : ℕ → Bool
even 0       = true
even (suc x) = not (even x)

even-true  : (y : ℕ)  → even (2 * y) ＝ true
even-true 0       = refl _
even-true (suc y) = even (2 * suc y)         ＝⟨ refl _ ⟩
                    even (suc y + suc y)     ＝⟨ refl _ ⟩
                    even (suc (y + suc y))   ＝⟨ refl _ ⟩
                    not (even (y + suc y))   ＝⟨ ap (not ∘ even) (+-step y y) ⟩
                    not (even (suc (y + y))) ＝⟨ refl _ ⟩
                    not (not (even (y + y))) ＝⟨ not-is-involution (even (y + y)) ⟩
                    even (y + y)             ＝⟨ refl _ ⟩
                    even (2 * y)             ＝⟨ even-true y ⟩
                    true ∎

even-false : (y : ℕ) → even (1 + 2 * y) ＝ false
even-false 0       = refl _
even-false (suc y) = even (1 + 2 * suc y)   ＝⟨ refl _ ⟩
                     even (suc (2 * suc y)) ＝⟨ refl _ ⟩
                     not (even (2 * suc y)) ＝⟨ ap not (even-true (suc y)) ⟩
                     not true               ＝⟨ refl _ ⟩
                     false                  ∎

div-by-2 : ℕ → ℕ
div-by-2 x = f (even-or-odd x)
 where
  f : is-even x ∔ is-odd x → ℕ
  f (inl (y , _)) = y
  f (inr (y , _)) = y

even-odd-lemma : (y z : ℕ) →  1 + 2 * y ＝ 2 * z → 𝟘
even-odd-lemma y z e = false-is-not-true impossible
 where
  impossible = false            ＝⟨ sym (even-false y) ⟩
               even (1 + 2 * y) ＝⟨ ap even e ⟩
               even (2 * z)     ＝⟨ even-true z ⟩
               true             ∎

not-both-even-and-odd : (x : ℕ) → ¬ (is-even x × is-odd x)
not-both-even-and-odd x ((y , e) , (y' , o)) = even-odd-lemma y' y d
 where
  d = 1 + 2 * y' ＝⟨ sym o ⟩
      x          ＝⟨ e ⟩
      2 * y      ∎

double : ℕ → ℕ
double 0 = 0
double (suc x) = suc (suc (double x))

double-correct : (x : ℕ) → double x ＝ x + x
double-correct 0       = double 0 ＝⟨ refl _ ⟩
                         0        ＝⟨ refl _ ⟩
                         0 + 0    ∎
double-correct (suc x) = goal
 where
  IH : double x ＝ x + x
  IH = double-correct x

  goal : double (suc x) ＝ suc x + suc x
  goal = double (suc x)       ＝⟨ refl _ ⟩
         suc (suc (double x)) ＝⟨ ap (suc ∘ suc) IH ⟩
         suc (suc (x + x))    ＝⟨ ap suc (sym (+-step x x)) ⟩
         suc (x + suc x)      ＝⟨ refl _ ⟩
         suc x + suc x        ∎
```
