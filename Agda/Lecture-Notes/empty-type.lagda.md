
[Martin Escardo](Https://www.Cs.Bham.Ac.Uk/~mhe/).
Notes originally written for the module *Advanced Functional Programming* of the [University of Birmingham](https://www.birmingham.ac.uk/index.aspx), UK.


<!--
```agda
{-# OPTIONS --without-K --safe #-}

module empty-type where

open import general-notation
```
-->
# The empty type 𝟘

It is convenient to have an empty type `𝟘`, with no elements at all. For example, this can be used in order to define [negation](negation.lagda.md), among other things.

```agda
data 𝟘 : Type where
```
And that's the complete definition. The list of constructors that define the type `𝟘` is empty.

Perhaps counter-intuitively, there is one function `𝟘 → 𝟘`, namely the [identity function](products.lagda.md). So although the type `𝟘` is empty, the type `𝟘 → 𝟘` is non-empty. In fact, the non-dependent elimination principle generalizes that.

## Proposition as types interpretation

The empty type is used to interpret "false". Because there is no way to prove the statement `false`, we use the empty type to represent `false` as a type.

In logic, in order to prove that a proposition is false, we assume it is true and use this assumption to reach a contradiction, such as `0 = 1`. With proofs as programs, in order to show that a statement represented by a type `A` is false, we assume a hypothetical element `x : A`, and from this we try to build a (necessarily impossible) element of the type `𝟘`, which is the desired contradiction. Because of this, in logic the negation of `A` is defined as `A implies false` or `A implies a contradiction`. Hence in type theory we define the negation of a type `A` to be the function type `A → 𝟘`:
```
¬_ : Type → Type
¬ A = A → 𝟘

infix 1000 ¬_
```


## Elimination principle

```agda
𝟘-elim : {A : 𝟘 → Type} (x : 𝟘) → A x
𝟘-elim ()
```
The [absurd pattern](https://agda.readthedocs.io/en/latest/language/function-definitions.html#absurd-patterns) `()`
expresses the fact that there is no pattern available because the type is empty. So in the same way that we define the type by giving an empty list of constructors, we define the function `𝟘-elim` by giving an empty list of equations. But we indicate this explicitly with the absurd pattern.

In terms of logic, this says that in order to show that a property `A` of elements of the empty type holds for all `x : 𝟘`, we have to do nothing, because there is no element to check, and by doing nothing we exhaust all possibilities. This is called [vacuous truth](https://en.wikipedia.org/wiki/Vacuous_truth).

It is important to notice that this is not a mere technicality. We'll see practical examples in due course.

The non-dependent version of the eliminator says that there is a function from the empty type to any type:
```agda
𝟘-nondep-elim : {A : Type} → 𝟘 → A
𝟘-nondep-elim {A} = 𝟘-elim {λ _ → A}
```

## Definition of emptiness

On the other hand, there is a function `f : A → 𝟘` if and only if `A`
has no elements, that is, if `A` is also empty. This is because if
`x : A`, there is no element `y : 𝟘` we can choose
in order to define `f x` to be `y`. In fact, we make this observation into our
definition of emptiness:
```agda
is-empty : Type → Type
is-empty A = A → 𝟘
```
So notice that this is the same definition as that of negation.

Here is another example of a type that is empty. In the [introduction](introduction.lagda.md) we defined the identity type former `_≡_`, which [we will revisit](identity-type.lagda.md), and we have that, for example, the type `3 ≡ 4` is empty, whereas the type `3 ≡ 3` has an element `refl 3`. Here are some examples coded in Agda:
```agda
𝟘-is-empty : is-empty 𝟘
𝟘-is-empty = 𝟘-nondep-elim

open import unit-type

𝟙-is-nonempty : ¬ is-empty 𝟙
𝟙-is-nonempty f = f ⋆
```

The last function works as follows. First we unfold the definition of `¬ is-empty 𝟙` to get `is-empty 𝟙 → 𝟘`. Unfolding again, we get the type `(𝟙 → 𝟘) → 𝟘`. So, given a hypothetical function `f : 𝟙 → 𝟘`, which of course cannot exist (and this what we are trying to conclude), we need to produce an element of `𝟘`. We do this by simply applying the mythical `f` to `⋆ : 𝟙`. We can actually incorporate this discussion in the Agda code, if we want:
```agda
𝟙-is-nonempty' : ¬ is-empty 𝟙
𝟙-is-nonempty' = γ
 where
  γ : (𝟙 → 𝟘) → 𝟘
  γ f = f ⋆
```
Agda accepts this second version because it automatically unfolds definitions, just as we have done above, to check whether what we have written makes sense. In this case, Agda knows that `¬ is-empty 𝟙` is exactly the same thing as `(𝟙 → 𝟘) → 𝟘` *by definition* of `¬` and `is-empty`. More examples are given in the file [negation](negation.lagda.md).

[Go back to the table of contents](https://martinescardo.github.io/HoTTEST-Summer-School/)
