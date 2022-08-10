# Week 3 - Homework Sheet

**Please finish the lab sheet before moving on to these exercises.**

```agda
{-# OPTIONS --without-K --safe #-}

module Pool.Homework.homework3 where

open import prelude
open import Pool.Lab.lab3-solutions
```

## Part I: Associativity and Commutativity of ∔ and ×

We have already seen that the Boolean operations `_||_` and `_&&_` are
associative and commutative.

The type formers that represent these logical connectives are also associative
and commutative.

### Exercise 1.1

**Prove** that `_∔_` is associative.

```agda
∔-assoc : {A B C : Type} → A ∔ (B ∔ C) → (A ∔ B) ∔ C
∔-assoc = {!!}
```

### Exercise 1.2

**Prove** that `_×_` is associative.

```agda
×-assoc : {A B C : Type} → A × (B × C) → (A × B) × C
×-assoc = {!!}
```

### Exercise 1.3

**Prove** that `_∔_` is commutative.

```agda
∔-comm : {A B : Type} → A ∔ B → B ∔ A
∔-comm = {!!}
```
### Exercise 1.4

**Prove** that `_×_` is commutative.

```agda
×-comm : {A B : Type} → A × B → B × A
×-comm = {!!}
```

## Part II: Law of excluded middle and double-negation elimination

In classical logic, we have the law of excluded middle (LEM): `A + ¬ A`, for any
logical formula `A`.

### Exercise 2.1

This seems intuitive to us, as having both `A` and `¬ A` gives us a
contradiction.

```agda
not-A-and-not-A : {A : Type} → ¬ (A × ¬ A)
not-A-and-not-A = {!!}
```

**Complete** the proof that `¬ (A x ¬ A)`.

### Exercise 2.2

Furthermore, if we had both `A` and `¬ A`, we could prove anything.

```agda
A-and-not-A-implies-B : {A B : Type} → A × ¬ A → B
A-and-not-A-implies-B p = {!!}
```

**Complete** the above statement *without* using pattern matching.

Hint: Use `𝟘-nondep-elim`.

### Exercise 2.3

However, it turns out that LEM is not provable (or disprovable) in Agda.

You can try this out yourself (but you won't succeed):

```agda
LEM : {A : Type} → A ∔ ¬ A
LEM = {!!} -- You are not expected to complete this hole.
           -- In fact, it's impossible.
```

However, we *can* prove the *double-negation* of `LEM`.

```agda
not-not-LEM : {A : Type} → ¬¬ (A ∔ ¬ A)
not-not-LEM = {!!}
```

**Prove** the double-negation of the law of excluded middle.

### Exercise 2.4

If we had access to double-negation elimination (DNE), as in classical logic, we
could give `LEM`.

Note: Do not try to prove DNE (see Exercise 2.5).

**Complete** `LEM'` using `DNE`.

```agda
DNE : {A : Type} → ¬¬ A → A
DNE = {!!} -- You are not expected to complete this hole.
           -- In fact, it's impossible.

LEM' : {A : Type} → A ∔ ¬ A
LEM' = {!!}
```

### Exercise 2.5

However, `DNE` is *also* not provable or disprovable in Agda.

It is the case, however, that if we had access to `LEM`, we could prove `DNE`.

```agda
DNE' : {A : Type} → ¬¬ A → A
DNE' {A} = {!!}
```

**Complete** `DNE'` using `LEM`.

### Exercise 2.6

So we have seen that `LEM` and `DNE` are both not provable in Agda, yet are
equivalent in the sense that having one gives us the other.

Finally, we can also show that the *double-negation* of DNE *is* provable in
Agda.

```agda
not-not-DNE : {A : Type} → ¬¬ (¬¬ A → A)
not-not-DNE {A} = {!!}
```

**Prove** the double-negation of the law of excluded middle.

## Part III: Sums and products

### Exercise 3.1

**Complete** the following proof of distributivity of `Σ` over `_∔_`.

```agda
Σ-∔-distributivity : {A : Type} {B C : A → Type}
                   → (Σ a ꞉ A , (B a ∔ C a))
                   → (Σ a ꞉ A , B a) ∔ (Σ a ꞉ A , C a)
Σ-∔-distributivity = {!!}
```

### Exercise 3.2

If, for every `a : A` we have `¬ B a` (the type `B a` is empty), then there
does not exist any `a : A` satisfying `B a` (the type `Σ B` is empty).

```agda
¬Σ-if-forall-not : {A : Type} {B : A → Type}
                 → ((a : A) → ¬ B a) → ¬ (Σ a ꞉ A , B a)
¬Σ-if-forall-not = {!!}
```

**Complete** the proof of the above statement.

### Exercise 3.3

**Prove** that the converse of the above also holds.

```agda
forall-not-if-¬Σ : {A : Type} {B : A → Type}
                 → ¬ (Σ a ꞉ A , B a) → (a : A) → ¬ B a
forall-not-if-¬Σ = {!!}
```

### Exercise 3.4

Finally, **prove** that `Σ` distributes over "for all".

```agda
Π-Σ-distributivity : {A B : Type} {C : A → B → Type}
                   → ((a : A) → (Σ b ꞉ B , C a b))
                   → Σ f ꞉ (A → B) , ((a : A) → C a (f a))
Π-Σ-distributivity = {!!}
```
