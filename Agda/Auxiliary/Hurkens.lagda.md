# Hurkens' paradox
(File provided by Ulrik Buchholtz)

Hurkens' simplification of Girard's paradox.
This derives a contradiction using only Π-types
and “type in type”, a universe that contains itself.
For a description of how it works, and the
similarity to Burali-Forti's paradox, see:

https://www.cs.cmu.edu/~kw/scans/hurkens95tlca.pdf

```agda
{-#  OPTIONS --without-K --type-in-type #-}
module Hurkens where

Type = Set

P : Type → Type
P X = X → Type

PP : Type → Type
PP X = P (P X)

⊥ : Type
⊥ = (X : Type) → X

¬ : Type → Type
¬ X = X → ⊥

U : Type
U = (X : Type) → (PP X → X) → PP X

τ : PP U → U
τ t X f p = t λ x → p (f (x X f))

σ : U → PP U
σ s = s U λ t → τ t

Δ : P U
Δ y = ¬ ((p : P U) → σ y p → p (τ (σ y)))

Ω : U
Ω = τ λ p → (x : U) → σ x p → p x

D : Type
D = (p : P U) → σ Ω p → p (τ (σ Ω))

lemma : (p : P U) → ((x : U) → σ x p → p x) → p Ω
lemma p H = H Ω λ x → H (τ (σ x))

nd : ¬ D
nd = lemma Δ λ x H K → K Δ H λ p → K λ y → p (τ (σ y))

d : D
d p = lemma λ y → p (τ (σ y))

boom : ⊥
boom = nd d
```

With this encoding of false we can of course inhabit all types,
inlucing the inductively defined empty type.

```agda
data ∅ : Type where

boom' : ∅
boom' = boom ∅
```
