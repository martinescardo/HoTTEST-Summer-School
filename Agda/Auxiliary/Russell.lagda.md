# Russell's paradox
(File provided by Ulrik Buchholtz)

Here we derive a contradiction from “type in type”,
a universe that contains itself, assuming that
this is additionally closed under generalized
inductive types.
Then we can directly encode Russell's paradox.

This development is inspired by Aczel's
[“sets as trees” interpretation of constructive set
theory](https://doi.org/10.1016/S0049-237X(08)71989-X),
from which this very simple paradox was
[deduced by Thierry Coquand](https://doi.org/10.1007/BF01995104).
N.G. de Bruijn also noticed a similar paradox.

```agda
{-#  OPTIONS --without-K --type-in-type #-}
module Russell where

Type = Set
```

We need some standard inductive types:
  Σ, ∅, and identity types.

```agda
data Σ (A : Type) (B : A → Type) : Type where
  _,_ : (a : A) → B a → Σ A B

pr₁ : {A : Type} {B : A → Type} → Σ A B → A
pr₁ (a , b) = a

data ∅ : Type where

data _≡_ {A : Type} (a : A) : A → Type where
  refl : a ≡ a
```

Then we use the following generalized inductive type.
(It's called generalized because it has a recursive
argument that is a function type.)
It represents trees that can branch according to
any type in the universe.
Without “type in type”, these would be well-founded
trees, like the membership trees in the cumulative
hierarchy model of set theory.

```agda
data V : Type where
  sup : (X : Type) → (X → V) → V
```

We can similarly define membership and non-membership.

```agda
_∈_ : V → V → Type
x ∈ sup X f = Σ X λ x' → x ≡ f x'

_∉_ : V → V → Type
x ∉ y = x ∈ y → ∅
```

Now it's straight-forward to define Russell's
paradoxical “set” of all sets that don't contain
themselves, and derive a contradiction.

```agda
R : V
R = sup (Σ V λ x → x ∉ x) pr₁

x∈R→x∉x : (x : V) → x ∈ R → x ∉ x
x∈R→x∉x x ((.x , x∉x) , refl) = x∉x

x∉x→x∈R : (x : V) → x ∉ x → x ∈ R
x∉x→x∈R x x∉x = (x , x∉x) , refl

R∉R : R ∉ R
R∉R R∈R = x∈R→x∉x R R∈R R∈R

boom : ∅
boom = R∉R (x∉x→x∈R R R∉R)
```
