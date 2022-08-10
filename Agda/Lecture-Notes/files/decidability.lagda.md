
[Martin Escardo](Https://www.Cs.Bham.Ac.Uk/~mhe/).
Notes originally written for the module *Advanced Functional Programming* of the [University of Birmingham](https://www.birmingham.ac.uk/index.aspx), UK.


<!--
```agda
{-# OPTIONS --without-K --safe #-}

module decidability where

open import prelude
open import negation
open import natural-numbers-type
```
-->
# Propositions as types versus propositions as booleans

When programming in conventional programming languages such as Haskell, C, Java, Python, etc., we use *booleans* rather than *types* to encode logical propositions. But this works only because we restrict ourselves to *decidable* propositions, as we'll see below.

We now discuss *why* we use *types* to encode logical propositions, and
*when* we can use *booleans* instead. It is not always.

## Discussion and motivation

**Examples.** We *can automatically check* equality of booleans, integers, strings and much more, using algorithms.

**Counter-example.** We *can't check* equality of functions of type `ℕ → ℕ`, for instance. Intuitively, to check that two functions `f` and `g` of this type are equal, we need to check infinitely many cases, namely `f x = g x` for all `x : ℕ`. But, we are afraid, intuition is not enough. This has to be proved. Luckily in our case, [Alan Turing](https://en.wikipedia.org/wiki/Alan_Turing) provided the basis to prove that. He showed that the [Halting Problem](https://en.wikipedia.org/wiki/Halting_problem) can't be solved by an algorithm in any programming language. It follows from this that we can't check whether two such functions `f` and `g` are equal or not using an algorithm.

The above examples and counter-examples show that sometimes we can decide equality with an algorithm, and sometimes we can't. However, for example, the identity type `_≡_` applies to *all* types, whether they have decidable equality or not, and this is why it is useful. We can think about equality, not only in our heads but also in Agda, without worrying whether it can be *checked* to be true or not by a computer. The identity type is not about *checking* equality. It is about asserting that two things are equal, and then proving this ourselves. In fact, equality is very often not checkable by the computer. It is instead about *stating* and *proving* or *disproving* equalities, where the proving and disproving is done by people (the lecturers and the students in this case), by hard, intelligent work.

## Decidable propositions

Motivated by the above discussion, we define when a logical proposition is decidable under the understanding of propositions as types:
```agda
is-decidable : Type → Type
is-decidable A = A ∔ ¬ A
```
This means that we can produce an element of `A` or show that no such element can be found.

Although it is not possible in general to write a program of type `¬¬ A → A`, this is possible when `A` is decidable:
```agda
¬¬-elim : {A : Type} → is-decidable A → ¬¬ A → A
¬¬-elim (inl x) f = x
¬¬-elim (inr g) f = 𝟘-elim (f g)
```

## Decidable propositions as booleans

The following shows that a type `A` is decidable if and only if there is `b : Bool` such that `A` holds if and only if the boolean `b` is `true`.

For the purposes of this handout, understanding the following proof is not important at a first reading. What is important is to understand *what* the type of the following function is saying, which is what we explained above.
```agda
decidability-with-booleans : (A : Type) → is-decidable A ⇔ Σ b ꞉ Bool , (A ⇔ b ≡ true)
decidability-with-booleans A = f , g
 where
  f : is-decidable A → Σ b ꞉ Bool , (A ⇔ b ≡ true)
  f (inl x) = true , (α , β)
   where
    α : A → true ≡ true
    α _ = refl true

    β : true ≡ true → A
    β _ = x

  f (inr ν) = false , (α , β)
   where
    α : A → false ≡ true
    α x = 𝟘-elim (ν x)

    β : false ≡ true → A
    β ()

  g : (Σ b ꞉ Bool , (A ⇔ b ≡ true)) → is-decidable A
  g (true ,  α , β) = inl (β (refl true))
  g (false , α , β) = inr (λ x → false-is-not-true (α x))
```

## Decidable predicates as boolean-valued functions

Consider the logical statement "x is even". This is decidable, because
there is an easy algorithm that tells whether a natural number `x` is
even or not. In programming languages we write this algorithm as a
procedure that returns a boolean. But an equally valid definition is to say that `x` is even if there is a natural number `y` such that `x = 2 * y`. This definition doesn't automatically give an algorithm to check whether or not `x` is even.
<!--
```agda
module _ where
 private
```
-->
```agda
  is-even : ℕ → Type
  is-even x = Σ y ꞉ ℕ , x ≡ 2 * y
```
This says what to be even *means*. But it doesn't say how we *check* with a computer program whether a number is even or not, which would be given by a function `check-even : ℕ → Bool`.
```agda
  check-even : ℕ → Bool
  check-even 0       = true
  check-even (suc x) = not (check-even x)
```

For this function to be correct, it has to be the case that

 > `is-even x ⇔ check-even x ≡ true`

**Exercise.** We believe you have learned enough Agda, try this.

This is possible because

 > `(x : X) → is-decidable (is-even x)`.

The following generalizes the above discussion and implements it in Agda.

First we define what it means for a predicate, such as `A = is-even`, to be decidable:
```agda
is-decidable-predicate : {X : Type} → (X → Type) → Type
is-decidable-predicate {X} A = (x : X) → is-decidable (A x)

```
In our example, this means that we can tell whether a number is even or not.

Next we show that a predicate `A` is decidable if and only if there is a boolean valued function `α` such that `A x` holds if and only if `α x ≡ true`. In the above example, `A` plays the role of `is-even` and `alpha` plays the role of `check-even`.

Again, what is important at a first reading of this handout is not to understand the proof but what the type of the function is saying. But we will discuss the proof in lectures.

```agda
predicate-decidability-with-booleans : {X : Type} (A : X → Type)
                                     → is-decidable-predicate A
                                     ⇔ Σ α ꞉ (X → Bool) , ((x : X) → A x ⇔ α x ≡ true)
predicate-decidability-with-booleans {X} A = f , g
 where
  f : is-decidable-predicate A → Σ α ꞉ (X → Bool) , ((x : X) → A x ⇔ α x ≡ true)
  f d = α , β
   where
    α : X → Bool
    α x = pr₁ (lr-implication I (d x))
     where
      I : is-decidable (A x) ⇔ Σ b ꞉ Bool , (A x ⇔ b ≡ true)
      I = decidability-with-booleans (A x)

    β : (x : X) → A x ⇔ α x ≡ true
    β x = ϕ , γ
     where
      I : is-decidable (A x) → Σ b ꞉ Bool , (A x ⇔ b ≡ true)
      I = lr-implication (decidability-with-booleans (A x))

      II : Σ b ꞉ Bool , (A x ⇔ b ≡ true)
      II = I (d x)

      ϕ : A x → α x ≡ true
      ϕ = lr-implication (pr₂ II)

      γ : α x ≡ true → A x
      γ = rl-implication (pr₂ II)

  g : (Σ α ꞉ (X → Bool) , ((x : X) → A x ⇔ α x ≡ true)) → is-decidable-predicate A
  g (α , ϕ) = d
   where
    d : is-decidable-predicate A
    d x = III
     where
      I : (Σ b ꞉ Bool , (A x ⇔ b ≡ true)) → is-decidable (A x)
      I = rl-implication (decidability-with-booleans (A x))

      II : Σ b ꞉ Bool , (A x ⇔ b ≡ true)
      II = (α x , ϕ x)

      III : is-decidable (A x)
      III = I II
```

Although boolean-valued predicates are fine, we prefer to use type-valued predicates for the sake of uniformity, because we can always define type valued predicates, but only on special circumstances can we define boolean-valued predicates. It is better to define all predicates in the same way, and then write Agda code for predicates that happen to be decidable.

## Preservation of decidability

If `A` and `B` are logically equivalent, then `A` is decidable if and only if `B` is decidable. We first prove one direction.
```agda
map-decidable : {A B : Type} → (A → B) → (B → A) → is-decidable A → is-decidable B
map-decidable f g (inl x) = inl (f x)
map-decidable f g (inr h) = inr (λ y → h (g y))

map-decidable-corollary : {A B : Type} → (A ⇔ B) → (is-decidable A ⇔ is-decidable B)
map-decidable-corollary (f , g) = map-decidable f g , map-decidable g f
```
Variation:
```agda
map-decidable' : {A B : Type} → (A → ¬ B) → (¬ A → B) → is-decidable A → is-decidable B
map-decidable' f g (inl x) = inr (f x)
map-decidable' f g (inr h) = inl (g h)
```

```agda
pointed-types-are-decidable : {A : Type} → A → is-decidable A
pointed-types-are-decidable = inl

empty-types-are-decidable : {A : Type} → ¬ A → is-decidable A
empty-types-are-decidable = inr

𝟙-is-decidable : is-decidable 𝟙
𝟙-is-decidable = pointed-types-are-decidable ⋆

𝟘-is-decidable : is-decidable 𝟘
𝟘-is-decidable = empty-types-are-decidable 𝟘-is-empty

∔-preserves-decidability : {A B : Type}
                         → is-decidable A
                         → is-decidable B
                         → is-decidable (A ∔ B)
∔-preserves-decidability (inl x) _       = inl (inl x)
∔-preserves-decidability (inr _) (inl y) = inl (inr y)
∔-preserves-decidability (inr h) (inr k) = inr (∔-nondep-elim h k)

×-preserves-decidability : {A B : Type}
                         → is-decidable A
                         → is-decidable B
                         → is-decidable (A × B)
×-preserves-decidability (inl x) (inl y) = inl (x , y)
×-preserves-decidability (inl _) (inr k) = inr (λ (x , y) → k y)
×-preserves-decidability (inr h) _       = inr (λ (x , y) → h x)

→-preserves-decidability : {A B : Type}
                         → is-decidable A
                         → is-decidable B
                         → is-decidable (A → B)
→-preserves-decidability _       (inl y) = inl (λ _ → y)
→-preserves-decidability (inl x) (inr k) = inr (λ f → k (f x))
→-preserves-decidability (inr h) (inr k) = inl (λ x → 𝟘-elim (h x))

¬-preserves-decidability : {A : Type}
                         → is-decidable A
                         → is-decidable (¬ A)
¬-preserves-decidability d = →-preserves-decidability d 𝟘-is-decidable
```

## Exhaustively searchable types

We will explain in a future lecture why we need to use `Type₁` rather than `Type` in the following definition. For the moment we just mention that because the definition mentions `Type`, there would be a circularity if the type of the definition where again `Type`. Such circular definitions are not allowed because if they were then we would be able to prove that `0=1`. We have that `Type : Type₁` (the type of `Type` is `Type₁`) but we can't have `Type : Type`.
```agda
is-exhaustively-searchable : Type → Type₁
is-exhaustively-searchable X = (A : X → Type)
                             → is-decidable-predicate A
                             → is-decidable (Σ x ꞉ X , A x)
```
**Exercise**. Show, in Agda, that the types `𝟘`, `𝟙` , `Bool` and  `Fin n`, for any `n : ℕ`, are exhaustively searchable. The idea is that we check whether or not `A x` holds for each `x : A`, and if we find at least one, we conclude that `Σ x ꞉ X , A x`, and otherwise we conclude that `¬ (Σ x ꞉ X , A x)`. This is possible because these types are finite.

**Exercise**. Think why there can't be any program of type `is-exhaustively-searchable ℕ`, by reduction to the Halting Problem. No Agda code is asked in this question. In fact, the question is asking you to think why such Agda code can't exist. This is very different from proving, in Agda, that `¬ is-exhaustively-searchable ℕ`. Interestingly, this is also not provable in Agda, but explaining why this is the case is beyond the scope of this module. In any case, this is an example of a statement `A` such that neither `A` nor `¬ A` are provable in Agda. Such statements are called *independent*. It must be remarked that the reason why there isn't an Agda program of type `is-exhaustively-searchable ℕ` is *not* merely that `ℕ` is infinite, because there are, perhaps surprisingly, infinite types `A` such that a program of type `is-exhastively-searchable A` can be coded in Agda. One really does an argument such as reduction to the Halting Problem to show that there is no program that can exaustively search the set `ℕ` of natural numbers.

```agda
Π-exhaustibility : (X : Type)
                 → is-exhaustively-searchable X
                 → (A : X → Type)
                 → is-decidable-predicate A
                 → is-decidable (Π x ꞉ X , A x)
Π-exhaustibility X s A d = VI
 where
  I : is-decidable-predicate (λ x → ¬ (A x))
  I x = ¬-preserves-decidability (d x)

  II : is-decidable (Σ x ꞉ X , ¬ (A x))
  II = s (λ x → ¬ (A x)) I

  III : (Σ x ꞉ X , ¬ (A x)) → ¬ (Π x ꞉ X , A x)
  III (x , f) g = f (g x)

  IV : ¬ (Σ x ꞉ X , ¬ (A x)) → (Π x ꞉ X , A x)
  IV h x = ii
   where
    i : ¬¬ A x
    i f = h (x , f)

    ii : A x
    ii = ¬¬-elim (d x) i

  V : is-decidable (Σ x ꞉ X , ¬ (A x)) → is-decidable (Π x ꞉ X , A x)
  V = map-decidable' III IV

  VI : is-decidable (Π x ꞉ X , A x)
  VI = V II
```
**Exercises.** If two types `A` and `B` are exhaustively searchable types, then so are the types `A × B` and `A + B`. Moreover, if `X` is an exhaustively searchable type and `A : X → Type` is a family of types, and the type `A x` is exhaustively searchable for each `x : X`, then the type `Σ x ꞉ X , A x` is exhaustively searchable.

## Decidable equality

A particular case of interest regarding the above discussion is the notion of a type having decidable equality, which can be written in Agda as follows.

```agda
has-decidable-equality : Type → Type
has-decidable-equality X = (x y : X) → is-decidable (x ≡ y)
```
**Exercise.** Show, in Agda, that a type `X` has decidable equality if and only if there is a function `X → X → Bool` that checks whether two elements of `X` are equal or not.

Some examples:
```agda
Bool-has-decidable-equality : has-decidable-equality Bool
Bool-has-decidable-equality true  true  = inl (refl true)
Bool-has-decidable-equality true  false = inr true-is-not-false
Bool-has-decidable-equality false true  = inr false-is-not-true
Bool-has-decidable-equality false false = inl (refl false)

open import natural-numbers-functions

ℕ-has-decidable-equality : has-decidable-equality ℕ
ℕ-has-decidable-equality 0       0       = inl (refl zero)
ℕ-has-decidable-equality 0       (suc y) = inr zero-is-not-suc
ℕ-has-decidable-equality (suc x) 0       = inr suc-is-not-zero
ℕ-has-decidable-equality (suc x) (suc y) = III
 where
  IH : is-decidable (x ≡ y)
  IH = ℕ-has-decidable-equality x y

  I : x ≡ y → suc x ≡ suc y
  I = ap suc

  II : suc x ≡ suc y → x ≡ y
  II = suc-is-injective

  III : is-decidable (suc x ≡ suc y)
  III = map-decidable I II IH
```

## Equality of functions

As discussed above, it is not possible to decide whether or not we have `f ∼ g` for two functions `f` and `g`, for example of type `ℕ → ℕ`. However, sometimes we can *prove* or *disprove* this for *particular* functions. Here are some examples:

```agda
private
 f g h : ℕ → ℕ

 f x = x

 g 0       = 0
 g (suc x) = suc (g x)

 h x = suc x

 f-equals-g : f ∼ g
 f-equals-g 0       = refl (f 0)
 f-equals-g (suc x) = γ
  where
   IH : f x ≡ g x
   IH = f-equals-g x

   γ : f (suc x) ≡ g (suc x)
   γ = f (suc x) ≡⟨ refl _ ⟩
       suc x     ≡⟨ refl _ ⟩
       suc (f x) ≡⟨ ap suc IH ⟩
       suc (g x) ≡⟨ refl _ ⟩
       g (suc x) ∎

 f-not-equals-h : ¬ (f ∼ h)
 f-not-equals-h e = contradiction d
  where
   d : 0 ≡ 1
   d = e 0

   contradiction : ¬ (0 ≡ 1)
   contradiction ()
```

[Go back to the table of contents](https://martinescardo.github.io/HoTTEST-Summer-School/)
