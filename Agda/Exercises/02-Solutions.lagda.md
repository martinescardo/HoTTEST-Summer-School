# Week 02 - Agda Exercises - Solutions

```agda
{-# OPTIONS --without-K --safe #-}

module 02-Solutions where

open import prelude
open import decidability
open import sums

```

## Part I

### Exercise 1
```agda
uncurry : {A B X : Type} → (A → B → X) → (A × B → X)
uncurry f (a , b) = f a b

curry : {A B X : Type} → (A × B → X) → (A → B → X)
curry f a b = f (a , b)
```
Under the propositions-as-types interpretation curry and unccurry
tell us that "if A then if B then X"  is (logically) equivalent
to "if A and B then X"


### Exercise 3
```agda
¬¬_ : Type → Type
¬¬ A = ¬ (¬ A)

¬¬¬ : Type → Type
¬¬¬ A = ¬ (¬¬ A)

tne : ∀ {A : Type} → ¬¬¬ A → ¬ A
tne f a = f (λ g → g a)
```

### Exercise 4
```agda
contraposition : {A B : Type} → (A → B) → ¬ B → ¬ A
contraposition f g a = g (f a)

¬¬-functor : {A B : Type} → (A → B) → ¬¬ A → ¬¬ B
¬¬-functor f = contraposition (contraposition f)

¬¬-kleisli : {A B : Type} → (A → ¬¬ B) → ¬¬ A → ¬¬ B
¬¬-kleisli f g = tne (¬¬-functor f g)
```




## Part II

```agda
bool-as-type : Bool → Type
bool-as-type true = 𝟙
bool-as-type false = 𝟘

bool-≡-char₁ : ∀ (b b' : Bool) → b ≡ b' → (bool-as-type b ⇔ bool-as-type b')
bool-≡-char₁ b .b (refl .b) = ⇔-refl
 where
 ⇔-refl : {X : Type} → X ⇔ X
 pr₁ ⇔-refl x = x
 pr₂ ⇔-refl x = x

true≢false : ¬ (true ≡ false)
true≢false p = bool-≡-char₁ true false p .pr₁ ⋆
-- also true≢false ()

bool-≡-char₂ : ∀ (b b' : Bool) → (bool-as-type b ⇔ bool-as-type b') → b ≡ b'
bool-≡-char₂ true true (b→b' , b'→b) = refl true
bool-≡-char₂ true false (b→b' , b'→b) = 𝟘-elim (b→b' ⋆)
bool-≡-char₂ false true (b→b' , b'→b) = 𝟘-elim (b'→b ⋆)
bool-≡-char₂ false false (b→b' , b'→b) = refl false
```




## Part III

```agda
case_of_ : {A B : Type} → A → (A → B) → B
case x of f = f x

has-bool-dec-fct : Type → Type
has-bool-dec-fct A = Σ {A → A → Bool} (λ f → ∀ x y → x ≡ y ⇔ (f x y) ≡ true)

decidable-equality-char : (A : Type) → has-decidable-equality A ⇔ has-bool-dec-fct A
pr₁ (decidable-equality-char A) discA = f , f-dec -- left to right implication
  where
  f' : (a b : A) → is-decidable (a ≡ b) → Bool
  f' a b (inl _) = true
  f' a b (inr _) = false

  f'-refl : (x : A) (d : is-decidable (x ≡ x)) → f' x x d ≡ true
  f'-refl x (inl _) = refl true
  f'-refl x (inr x≢x) = 𝟘-nondep-elim (x≢x (refl x))

  f : A → A → Bool
  f a b = f' a b (discA a b)

  f-dec : ∀ x y → x ≡ y ⇔ (f x y) ≡ true
  pr₁ (f-dec x .x) (refl .x) = f'-refl x (discA x x)
  pr₂ (f-dec x y) with discA x y
  ... | (inl p) = λ _ → p
  ... | (inr _) = λ q → 𝟘-nondep-elim (true≢false (q ⁻¹))

pr₂ (decidable-equality-char A) (f , f-dec) x y -- right to left implication
    with Bool-has-decidable-equality (f x y) true
... | (inl p) = inl (f-dec x y .pr₂ p)
... | (inr g) = inr λ p → g (f-dec x y .pr₁ p)
```
