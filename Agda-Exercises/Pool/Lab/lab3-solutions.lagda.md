# Week 3 - Lab Sheet - Solutions

```agda
{-# OPTIONS --without-K --safe #-}
module Pool.Lab.lab3-solutions where

open import prelude hiding (𝟘-nondep-elim)

¬¬_ : Type → Type
¬¬ A = ¬ (¬ A)

¬¬¬ : Type → Type
¬¬¬ A = ¬ (¬¬ A)

∔-introduction-left  : {A B : Type} → A → A ∔ B
∔-introduction-left a = inl a

∔-introduction-right : {A B : Type} → B → A ∔ B
∔-introduction-right b = inr b

∔-elimination : {A B X : Type} → (A → X) → (B → X) → (A ∔ B → X)
∔-elimination p q (inl a) = p a
∔-elimination p q (inr b) = q b


×-elimination-left : {A B : Type} → A × B → A
×-elimination-left (a , b) = a

×-elimination-right : {A B : Type} → A × B → B
×-elimination-right (a , b) = b

×-introduction : {A B : Type} → A → B → A × B
×-introduction a b = (a , b)

×-introduction' : {A B X : Type} → (X → A) → (X → B) → (X → A × B)
×-introduction' p q x = (p x , q x)


uncurry : {A B X : Type} → (A → B → X) → (A × B → X)
uncurry p (a , b) = p a b

curry : {A B X : Type} → (A × B → X) → (A → B → X)
curry p a b = p (a , b)

→-trans : {A B C : Type} → (A → B) → (B → C) → (A → C)
→-trans p q = λ a → q (p a)


𝟘-nondep-elim : {A : Type} → 𝟘 → A
𝟘-nondep-elim = λ ()

¬¬-introduction : {A : Type} → A → ¬¬ A
¬¬-introduction a = λ p → p a

not-implies-not³ : {A : Type} → ¬ A → ¬¬¬ A
not-implies-not³ p = λ q → q p

not³-implies-not : {A : Type} → ¬¬¬ A → ¬ A
not³-implies-not p = λ a → p (λ q → q a)

contraposition : {A B : Type} → (A → B) → ¬ B → ¬ A
contraposition p q = λ a → q (p a)

¬¬-functor : {A B : Type} → (A → B) → ¬¬ A → ¬¬ B
¬¬-functor p = contraposition (contraposition p)

¬¬-kleisli : {A B : Type} → (A → ¬¬ B) → ¬¬ A → ¬¬ B
¬¬-kleisli p = contraposition (λ q → λ a → p a q)


de-morgan₁ : {A B : Type} → ¬ (A ∔ B) → ¬ A × ¬ B
de-morgan₁ {A} {B} p = ×-introduction p₁ p₂
 where
  p₁ : ¬ A
  p₁ = p ∘ ∔-introduction-left
  p₂ : ¬ B
  p₂ = p ∘ ∔-introduction-right

de-morgan₂ : {A B : Type} → ¬ A ∔ ¬ B → ¬ (A × B)
de-morgan₂ = ∔-elimination (→-trans ×-elimination-left)
                           (→-trans ×-elimination-right)

¬-and-+-exercise₁ : {A B : Type} → ¬ A ∔ B → A → B
¬-and-+-exercise₁ (inl p) a = 𝟘-nondep-elim (p a)
¬-and-+-exercise₁ (inr q) _ = q

¬-and-+-exercise₂ : {A B : Type} → ¬ A ∔ B → ¬ (A × ¬ B)
¬-and-+-exercise₂ (inl p) = λ { (a , _) → p a }
¬-and-+-exercise₂ (inr q) = λ { (a , r) → r q }

distributivity₁ : {A B C : Type} → (A × B) ∔ C → (A ∔ C) × (B ∔ C)
distributivity₁ {A} {B} {C} = ∔-elimination q₁ q₂
 where
  q₁ : A × B → (A ∔ C) × (B ∔ C)
  q₁ (a , b) = (inl a , inl b)
  q₂ : C → A ∔ C × B ∔ C
  q₂ c = (inr c , inr c)

distributivity₂ : {A B C : Type} → (A ∔ B) × C → (A × C) ∔ (B × C)
distributivity₂ (p , c) =
 ∔-elimination (λ a → inl (a , c)) (λ b → inr (b , c)) p


Σ-introduction : {A : Type} {B : (A → Type)} → (a : A) → B a → (Σ a ꞉ A , B a)
Σ-introduction a b = (a , b)

Σ-to-× : {A : Type} {B : (A → Type)} → ((a , _) : (Σ a ꞉ A , B a)) → A × B a
Σ-to-× (a , b) = (a , b)

Σ-on-Bool : {B : Bool → Type} → (Σ x ꞉ Bool , B x) → B true ∔ B false
Σ-on-Bool (true  , b) = inl b
Σ-on-Bool (false , b) = inr b


Π-apply : {A : Type} {B : (A → Type)} → ((a : A) → B a) → (a : A) → B a
Π-apply p a = p a

Π-→ : {A : Type} {B C : A → Type}
    → ((a : A) → B a → C a)
    → ((a : A) → B a) → ((a : A) → C a)
Π-→ p q = λ a → p a (q a)
```
