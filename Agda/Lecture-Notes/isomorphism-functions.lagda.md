
[Martin Escardo](Https://www.Cs.Bham.Ac.Uk/~mhe/).
Notes originally written for the module *Advanced Functional Programming* of the [University of Birmingham](https://www.birmingham.ac.uk/index.aspx), UK.


<!--
```agda
{-# OPTIONS --without-K --safe #-}

module isomorphism-functions where

open import prelude
open import isomorphisms
```
-->
# Some constructions with isomorphisms

```agda
≃-refl : (X : Type) → X ≅ X
≃-refl X = Isomorphism id (Inverse id refl refl)

≅-sym : {X Y : Type} → X ≅ Y → Y ≅ X
≅-sym (Isomorphism f (Inverse g η ε)) = Isomorphism g (Inverse f ε η)

≅-trans : {X Y Z : Type} → X ≅ Y → Y ≅ Z → X ≅ Z
≅-trans (Isomorphism f  (Inverse g  η  ε))
        (Isomorphism f' (Inverse g' η' ε'))
       = Isomorphism (f' ∘ f)
          (Inverse (g ∘ g')
            (λ x → g (g' (f' (f x))) ≡⟨ ap g (η' (f x)) ⟩
                   g (f x)           ≡⟨ η x ⟩
                   x                 ∎)
            (λ y → f' (f (g (g' y))) ≡⟨ ap f' (ε (g' y)) ⟩
                   f' (g' y)         ≡⟨ ε' y ⟩
                   y                 ∎))
```

Notation for chains of isomorphisms (like chains of equalities):

```agda
_≃⟨_⟩_ : (X {Y} {Z} : Type) → X ≅ Y → Y ≅ Z → X ≅ Z
_ ≃⟨ d ⟩ e = ≅-trans d e

_■ : (X : Type) → X ≅ X
_■ = ≃-refl

```

[Go back to the table of contents](https://martinescardo.github.io/HoTTEST-Summer-School/)
