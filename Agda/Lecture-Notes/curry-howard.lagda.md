
Martin Escardo.
Notes originally written for the module "Advanced Functional Programming"
at the School of Computer Science of the University of Birmingham, UK.


# Propositions as types and basic Martin-Löf type theory

We now complete the proposition-as-types interpretation of logic.

| Logic           | English                    | Type theory   | Agda          | Handouts                                            | Alternative terminology                    |
|-----------------|----------------------------|---------------|---------------|-----------------------------------------------------|--------------------------------------------|
| ⊥               | false                      | ℕ₀            | 𝟘             | [empty type](empty-type.lagda.md)                   |                                            |
| ⊤               | true (*)                   | ℕ₁            | 𝟙             | [unit type](unit-type.lagda.md)                     |                                            |
| A ∧ B           | A and B                    | A × B         | A × B         | [binary product](binary-products.lagda.md)          | cartesian product                          |
| A ∨ B           | A or B                     | A + B         | A ∔ B         | [binary sum](binary-sums.lagda.md)                  | coproduct, <br> binary disjoint union      |
| A → B           | A implies B                | A → B         | A → B         | [function type](products.lagda.md)                  | non-dependent function type                |
| ¬ A             | not A                      | A → ℕ₀        | A → 𝟘         | [negation](negation.lagda.md)                       |                                            |
| ∀ x : A, B x    | for all x:A, B x           | Π x : A , B x | (x : A) → B x | [product](products.lagda.md)                        | dependent function type                    |
| ∃ x : A, B x    | there is x:A such that B x | Σ x ꞉ A , B x | Σ x ꞉ A , B x | [sum](sums.lagda.md)                                | disjoint union, <br> dependent pair type   |
| x = y           | x equals y                 | Id x y        | x ≡ y         | [identity type](identity-type.lagda.md)             | equality type, <br> propositional equality |

## Remarks

 * (*) Not only the unit type 𝟙, but also any type with at least one element can be regarded as "true" in the propositions-as-types interpretation.

 * In Agda we can use any notation we like, of course, and people do use slightly different notatations for e.g. `𝟘`, `𝟏`, `+` and `Σ`.

 * We will refer to the above type theory together with the type `ℕ` of natural numbers as *Basic Martin-Löf Type Theory*.

 * As we will see, this type theory is very expressive and allows us to construct rather sophisticated types, including e.g. lists, vectors and trees.

 * All types in MLTT ([Martin-Löf type theory](http://archive-pml.github.io/martin-lof/pdfs/Bibliopolis-Book-1984.pdf)) come with *introduction* and *elimination* principles.
