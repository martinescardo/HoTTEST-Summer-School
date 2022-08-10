
[Martin Escardo](Https://www.Cs.Bham.Ac.Uk/~mhe/).
Notes originally written for the module *Advanced Functional Programming* of the [University of Birmingham](https://www.birmingham.ac.uk/index.aspx), UK.


# Hedberg's Theorem

Sometimes we wish to know that the identity type `x ≡ y` has at most one element for all elements `x` and `y` of a type. In this case we say that the type is a set. Alternatively, one says that the type satisfies *uniqueness of identity proofs* (UIP), or that it satisfies the *K axiom*. Perhaps surprisingly, this can't be proved for all types. But it can be proved for quite a few types, including the booleans, natural numbers, and functions `ℕ → ℕ`, among many others.

Hedberg's Theorem, whose proof is short, but quite difficult to understand, even for experts in Martin-Löf type theory, is a main tool for establishing that some types are sets.
Agda has the axiom `K` discussed above enabled by default. We are disabling it in all modules, including this. The reason is that towards the end of term we intend to give examples of types that are not sets, and explain why they are interesting.

```agda
{-# OPTIONS --without-K --safe #-}

module Hedbergs-Theorem where

open import prelude
open import negation

is-prop : Type → Type
is-prop X = (x y : X) → x ≡ y

𝟘-is-prop : is-prop 𝟘
𝟘-is-prop () ()

𝟙-is-prop : is-prop 𝟙
𝟙-is-prop ⋆ ⋆ = refl ⋆

is-set : Type → Type
is-set X = (x y : X) → is-prop (x ≡ y)

is-constant : {X Y : Type} → (X → Y) → Type
is-constant {X} f = (x x' : X) → f x ≡ f x'

has-constant-endofunction : Type → Type
has-constant-endofunction X = Σ f ꞉ (X → X), is-constant f

⁻¹-left∙ : {X : Type} {x y : X} (p : x ≡ y)
         → p ⁻¹ ∙ p ≡ refl y
⁻¹-left∙ (refl x) = refl (refl x)

⁻¹-right∙ : {X : Type} {x y : X} (p : x ≡ y)
          → p ∙ p ⁻¹ ≡ refl x
⁻¹-right∙ (refl x) = refl (refl x)

Hedbergs-Lemma : {X : Type} (x : X)
               → ((y : X) → has-constant-endofunction (x ≡ y))
               → (y : X) → is-prop (x ≡ y)
Hedbergs-Lemma {X} x c y p q = II
 where
  f : (y : X) → x ≡ y → x ≡ y
  f y = pr₁ (c y)

  κ : (y : X) (p q : x ≡ y) → f y p ≡ f y q
  κ y = pr₂ (c y)

  I : (y : X) (p : x ≡ y) → (f x (refl x))⁻¹ ∙ f y p ≡ p
  I x (refl x) = r
   where
    r : (f x (refl x)) ⁻¹ ∙ f x (refl x) ≡ refl x
    r = ⁻¹-left∙ (f x (refl x))

  II = p                         ≡⟨ (I y p)⁻¹                          ⟩
       (f x (refl x))⁻¹ ∙ f y p  ≡⟨ ap ((f x (refl x))⁻¹ ∙_) (κ y p q) ⟩
       (f x (refl x))⁻¹ ∙ f y q  ≡⟨ I y q                              ⟩
       q                         ∎


is-Hedberg-type : Type → Type
is-Hedberg-type X = (x y : X) → has-constant-endofunction (x ≡ y)

Hedberg-types-are-sets : (X : Type)
                       → is-Hedberg-type X
                       → is-set X
Hedberg-types-are-sets X c x = Hedbergs-Lemma x
                                (λ y → pr₁ (c x y) , pr₂ (c x y))

pointed-types-have-constant-endofunction : {X : Type}
                                         → X
                                         → has-constant-endofunction X
pointed-types-have-constant-endofunction x = ((λ y → x) , (λ y y' → refl x))

empty-types-have-constant-endofunction : {X : Type}
                                       → is-empty X
                                       → has-constant-endofunction X
empty-types-have-constant-endofunction e = (id , (λ x x' → 𝟘-elim (e x)))

open import decidability

decidable-types-have-constant-endofunctions : {X : Type}
                                            → is-decidable X
                                            → has-constant-endofunction X
decidable-types-have-constant-endofunctions (inl x) =
 pointed-types-have-constant-endofunction x
decidable-types-have-constant-endofunctions (inr e) =
 empty-types-have-constant-endofunction e

types-with-decidable-equality-are-Hedberg : {X : Type}
                                          → has-decidable-equality X
                                          → is-Hedberg-type X
types-with-decidable-equality-are-Hedberg d x y =
 decidable-types-have-constant-endofunctions (d x y)

Hedbergs-Theorem : {X : Type} → has-decidable-equality X → is-set X
Hedbergs-Theorem {X} d = Hedberg-types-are-sets X
                          (types-with-decidable-equality-are-Hedberg d)

ℕ-is-set : is-set ℕ
ℕ-is-set = Hedbergs-Theorem ℕ-has-decidable-equality

Bool-is-set : is-set Bool
Bool-is-set = Hedbergs-Theorem Bool-has-decidable-equality
```

[Go back to the table of contents](https://martinescardo.github.io/HoTTEST-Summer-School/)
