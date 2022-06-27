# Week 3 - Homework Sheet - Solutions

```agda
{-# OPTIONS --without-K --safe #-}

module Pool.Homework.homework3-solutions where

open import prelude hiding (𝟘-nondep-elim)
open import Pool.Lab.lab3-solutions

∔-assoc : {A B C : Type} → A ∔ (B ∔ C) → (A ∔ B) ∔ C
∔-assoc (inl a)       = inl (inl a)
∔-assoc (inr (inl b)) = inl (inr b)
∔-assoc (inr (inr c)) = inr c

×-assoc : {A B C : Type} → A × (B × C) → (A × B) × C
×-assoc (a , (b , c)) = (a , b) , c

∔-comm : {A B : Type} → A ∔ B → B ∔ A
∔-comm (inl a) = inr a
∔-comm (inr b) = inl b

×-comm : {A B : Type} → A × B → B × A
×-comm (a , b) = b , a


not-A-and-not-A : {A : Type} → ¬ (A × ¬ A)
not-A-and-not-A (a , p) = p a

A-and-not-A-implies-B : {A B : Type} → A × ¬ A → B
A-and-not-A-implies-B p = 𝟘-nondep-elim (not-A-and-not-A p)

LEM : {A : Type} → A ∔ ¬ A
LEM = {!!}

not-not-LEM : {A : Type} → ¬¬ (A ∔ ¬ A)
not-not-LEM p = p (inr (λ a → p (inl a)))

DNE : {A : Type} → ¬¬ A → A
DNE = {!!}

LEM' : {A : Type} → A ∔ ¬ A
LEM' = DNE not-not-LEM

DNE' : {A : Type} → ¬¬ A → A
DNE' {A} p = γ LEM
 where
  γ : A ∔ ¬ A → A
  γ (inl a) = a
  γ (inr q) = 𝟘-nondep-elim (p q)

not-not-DNE : {A : Type} → ¬¬ (¬¬ A → A)
not-not-DNE {A} p = p dne
 where
  r : ¬ A
  r a = p (λ _ → a)
  dne : ¬¬ A → A
  dne q = 𝟘-nondep-elim (q r)


Σ-∔-distributivity : {A : Type} {B C : A → Type}
                   → (Σ a ꞉ A , (B a ∔ C a))
                   → (Σ a ꞉ A , B a) ∔ (Σ a ꞉ A , C a)
Σ-∔-distributivity (a , inl b) = inl (a , b)
Σ-∔-distributivity (a , inr c) = inr (a , c)

¬Σ-if-forall-not : {A : Type} {B : A → Type}
                 → ((a : A) → ¬ B a) → ¬ (Σ a ꞉ A , B a)
¬Σ-if-forall-not p (a , b) = p a b

forall-not-if-¬Σ : {A : Type} {B : A → Type}
                 → ¬ (Σ a ꞉ A , B a) → (a : A) → ¬ B a
forall-not-if-¬Σ p a b = p (a , b)

Π-Σ-distributivity : {A B : Type} {C : A → B → Type}
                   → ((a : A) → (Σ b ꞉ B , C a b))
                   → Σ f ꞉ (A → B) , ((a : A) → C a (f a))
Π-Σ-distributivity p = (λ a → fst (p a)) , (λ a → snd (p a))
```
