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
Under the propositions-as-types interpretation curry and uncurry
tell us that "if A then if B then X"  is (logically) equivalent
to "if A and B then X"

### Exercise 2
```agda
[i] : {A B C : Type} → (A × B) ∔ C → (A ∔ C) × (B ∔ C)
[i] (inl (a , b)) = inl a , inl b
[i] (inr c) = inr c , inr c

[ii] : {A B C : Type} → (A ∔ B) × C → (A × C) ∔ (B × C)
[ii] (inl a , c) = inl (a , c)
[ii] (inr b , c) = inr (b , c)

[iii] : {A B : Type} → ¬ (A ∔ B) → ¬ A × ¬ B
pr₁ ([iii] f) a = f (inl a)
pr₂ ([iii] f) b = f (inr b)
```

The next goal `[iv] : {A B : Type} → ¬ (A × B) → ¬ A ∔ ¬ B`
is not provable. Under propositions-as-types it says that
"not (A and B) implies not A or not B", which is not true
in constructive logic. At the end we have to give a term of
the form `inl ...` or `inr ...` but for abstract `A B` we
can not say of which form it should be.
```agda
[v] : {A B : Type} → (A → B) → ¬ B → ¬ A -- also known as contraposition
[v] f g a = g (f a)
```

Neither of `[vi] : {A B : Type} → (¬ A → ¬ B) → B → A`
and `[vii] : {A B : Type} → ((A → B) → A) → A` are provable
Under propositions-as-types `[vi]` is known as *inverse contraposition*
and `[vii]` is known as *Peirce's law*. At the end we have to construct
something of type `A` but this is not possible with all the assumptions
being functions.
```agda
[viii] : {A : Type} {B : A → Type}
    → ¬ (Σ a ꞉ A , B a) → (a : A) → ¬ B a
[viii] f a bₐ = f (a , bₐ)
```
The next goal
`[ix] : {A : Type} {B : A → Type} → ¬ ((a : A) → B a) → (Σ a ꞉ A , ¬ B a)`
reads as: "If not for all a, B(a), then there is an a such that not B(a)"
This is not true in constructive logic. Again, we have to construct
an `a : A` as the first projection of the Sigma-type in the conclusion,
which is not possible from our assumptions.

```agda
[x] : {A B : Type} {C : A → B → Type}
      → ((a : A) → (Σ b ꞉ B , C a b))
      → Σ f ꞉ (A → B) , ((a : A) → C a (f a))
pr₁ ([x] g) a = g a .pr₁
pr₂ ([x] g) a = g a .pr₂
```
Note that under propositions-as-types `[x]` reads somewhat like the
*axiom of choice*. Yet it is still provable. This result is often
referred to as the *distributivity of Π over Σ* and shows that
propositions-as-types should be taken with a grain of salt sometimes.

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
¬¬-functor : {A B : Type} → (A → B) → ¬¬ A → ¬¬ B
¬¬-functor f = [v] ([v] f)

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
has-bool-dec-fct : Type → Type
has-bool-dec-fct A = Σ f ꞉ (A → A → Bool) , (∀ x y → x ≡ y ⇔ (f x y) ≡ true)

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
