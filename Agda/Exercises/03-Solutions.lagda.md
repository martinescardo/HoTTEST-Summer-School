# Week 02 - Agda Exercises - Solutions

```agda
{-# OPTIONS --without-K --safe #-}

module 03-Solutions where

open import prelude hiding (Type)

open import Agda.Primitive
  using (Level; lzero; lsuc; _⊔_)
  renaming (Set to Type)
  public
```

# Part I


## Type isomorphisms

A function `f : A → B` is called a *bijection* if there is a function `g : B → A` in the opposite direction such that `g ∘ f ∼ id` and `f ∘ g ∼ id`. Recall that `_∼_` is [pointwise equality](identity-type.lagda.md) and that `id` is the [identity function](products.lagda.md). This means that we can convert back and forth between the types `A` and `B` landing at the same element with started with, either from `A` or from `B`. In this case, we say that the types `A` and `B` are *isomorphic*, and we write `A ≅ B`. Bijections are also called type *isomorphisms*. We can define these concepts in Agda using [sum types](sums.lagda.md) or [records](https://agda.readthedocs.io/en/latest/language/record-types.html). We will adopt the latter, but we include both definitions for the sake of illustration. Recall that we [defined](general-notation.lagda.md) the domain of a function `f : A → B` to be `A` and its codomain to be `B`.

```agda

module _ where
  private
    is-bijection : {A B : Type lzero} → (A → B) → Type lzero
    is-bijection f = Σ g ꞉ (codomain f → domain f) , ((g ∘ f ∼ id) × (f ∘ g ∼ id))

    _≅_ : Type lzero → Type lzero → Type lzero
    A ≅ B = Σ f ꞉ (A → B) , is-bijection f
```
And here we give an equivalent definition which uses records and is usually more convenient in practice and is the one we adopt:
```agda
record is-bijection {A B : Type lzero} (f : A → B) : Type lzero where
 constructor
  Inverse
 field
  inverse : B → A
  η       : inverse ∘ f ∼ id
  ε       : f ∘ inverse ∼ id

record _≅_ (A B : Type lzero) : Type lzero where
 constructor
  Isomorphism
 field
  bijection   : A → B
  bijectivity : is-bijection bijection

infix 0 _≅_
```
The definition with `Σ` is probably more intuitive, but, as discussed above, the definition with a record is often easier to work with, because we can easily extract the components of the definitions using the names of the fields. It also often allows Agda to infer more types, and to give us more sensible goals in the interactive development of Agda programs and proofs.

Notice that `inverse` plays the role of `g`. The reason we use `inverse` is that then we can use the word `inverse` to extract the inverse of a bijection. Similarly we use `bijection` for `f`, as we can use the word `bijection` to extract the bijection from a record.

# The binary type 𝟚

This type can be defined to be `𝟙 ∔ 𝟙` using [binary sums](binary-sums.lagda.md), but we give a direct definition which will allow us to discuss some relationships between the various type formers of Basic MLTT.
```agda
data 𝟚 : Type lzero where
 𝟎 𝟏 : 𝟚

Bool-𝟚-isomorphism : Bool ≅ 𝟚
Bool-𝟚-isomorphism = record { bijection = f ; bijectivity = f-is-bijection }
 where
  f : Bool → 𝟚
  f false = 𝟎
  f true  = 𝟏

  g : 𝟚 → Bool
  g 𝟎 = false
  g 𝟏 = true

  gf : g ∘ f ∼ id
  gf true  = refl true
  gf false = refl false

  fg : f ∘ g ∼ id
  fg 𝟎 = refl 𝟎
  fg 𝟏 = refl 𝟏

  f-is-bijection : is-bijection f
  f-is-bijection = record { inverse = g ; η = gf ; ε = fg }
```

# Part II

## Finite types

```agda
data Fin : ℕ → Type lzero where
 zero : {n : ℕ} → Fin (suc n)
 suc  : {n : ℕ} → Fin n → Fin (suc n)

Fin-elim : (A : {n : ℕ} → Fin n → Type)
         → ({n : ℕ} → A {suc n} zero)
         → ({n : ℕ} (k : Fin n) → A k → A (suc k))
         → {n : ℕ} (k : Fin n) → A k
Fin-elim A a f = h
 where
  h : {n : ℕ} (k : Fin n) → A k
  h zero    = a
  h (suc k) = f k (h k)


Fin' : ℕ → Type lzero
Fin' 0       = 𝟘
Fin' (suc n) = 𝟙 ∔ Fin' n

zero' : {n : ℕ} → Fin' (suc n)
zero' = inl ⋆

suc'  : {n : ℕ} → Fin' n → Fin' (suc n)
suc' = inr

Fin-isomorphism : (n : ℕ) → Fin n ≅ Fin' n
Fin-isomorphism n = record { bijection = f n ; bijectivity = f-is-bijection n }
 where
  f : (n : ℕ) → Fin n → Fin' n
  f (suc n) zero    = zero'
  f (suc n) (suc k) = suc' (f n k)

  g : (n : ℕ) → Fin' n → Fin n
  g (suc n) (inl ⋆) = zero
  g (suc n) (inr k) = suc (g n k)

  gf : (n : ℕ) → g n ∘ f n ∼ id
  gf (suc n) zero    = refl zero
  gf (suc n) (suc k) = γ
   where
    IH : g n (f n k) ≡ k
    IH = gf n k

    γ = g (suc n) (f (suc n) (suc k)) ≡⟨ refl _ ⟩
        g (suc n) (suc' (f n k))      ≡⟨ refl _ ⟩
        suc (g n (f n k))             ≡⟨ ap suc IH ⟩
        suc k                         ∎

  fg : (n : ℕ) → f n ∘ g n ∼ id
  fg (suc n) (inl ⋆) = refl (inl ⋆)
  fg (suc n) (inr k) = γ
   where
    IH : f n (g n k) ≡ k
    IH = fg n k

    γ = f (suc n) (g (suc n) (suc' k)) ≡⟨ refl _ ⟩
        f (suc n) (suc (g n k))        ≡⟨ refl _ ⟩
        suc' (f n (g n k))             ≡⟨ ap suc' IH ⟩
        suc' k                         ∎

  f-is-bijection : (n : ℕ) → is-bijection (f n)
  f-is-bijection n = record { inverse = g n ; η = gf n ; ε = fg n}
```

```agda

open import natural-numbers-functions
  using (_≤₁_)

open import decidability
  using (is-decidable; is-decidable-predicate)

is-lower-bound : (P : ℕ → Type₀) (n : ℕ) → Type₀
is-lower-bound P n = (m : ℕ) → P m → n ≤₁ m

minimal-element :
  (P : ℕ → Type₀) → Type₀
minimal-element P = Σ n ꞉ ℕ , (P n) × (is-lower-bound P n)


leq-zero : (n : ℕ) → 0 ≤₁ n
leq-zero n = ⋆


is-minimal-element-suc :
  (P : ℕ → Type₀) (d : is-decidable-predicate P)
  (m : ℕ) (pm : P (suc m))
  (is-lower-bound-m : is-lower-bound (λ x → P (suc x)) m) →
  ¬ (P 0) → is-lower-bound P (suc m)
is-minimal-element-suc P d m pm is-lower-bound-m neg-p0 0 p0 =
  𝟘-nondep-elim (neg-p0 p0)
is-minimal-element-suc
  P d 0 pm is-lower-bound-m neg-p0 (suc n) psuccn = leq-zero n
is-minimal-element-suc
  P d (suc m) pm is-lower-bound-m neg-p0 (suc n) psuccn =
  is-minimal-element-suc (λ x → P (suc x)) (λ x → d (suc x)) m pm
    ( λ m → is-lower-bound-m (suc m))
    ( is-lower-bound-m 0)
    ( n)
    ( psuccn)


well-ordering-principle-suc :
  (P : ℕ → Type₀) (d : is-decidable-predicate P)
  (n : ℕ) (p : P (suc n)) →
  is-decidable (P 0) →
  minimal-element (λ m → P (suc m)) → minimal-element P
well-ordering-principle-suc P d n p (inl p0) _  = 0 , (p0 , (λ m q → leq-zero m))
well-ordering-principle-suc P d n p (inr neg-p0) (m , (pm , is-min-m)) = (suc m) , (pm , is-minimal-element-suc P d m pm is-min-m neg-p0)


well-ordering-principle :
  (P : ℕ → Type₀) → (d : is-decidable-predicate P) → (n : ℕ) →  P n → minimal-element P
well-ordering-principle P d 0 p = 0 , (p , (λ m q → leq-zero m))
well-ordering-principle P d (suc n) p = well-ordering-principle-suc P d n p (d 0) (well-ordering-principle (λ m → P (suc m)) (λ m → d (suc m)) n p)

is-zero-well-ordering-principle-suc :
  (P : ℕ → Type₀) (d : is-decidable-predicate P)
  (n : ℕ) (p : P (suc n)) (d0 : is-decidable (P 0)) →
  (x : minimal-element (λ m → P (suc m))) (p0 : P 0) →
  (pr₁ (well-ordering-principle-suc P d n p d0 x)) ≡ 0
is-zero-well-ordering-principle-suc P d n p (inl p0) x q0 = refl 0
is-zero-well-ordering-principle-suc P d n p (inr np0) x q0 =
  𝟘-nondep-elim (np0 q0)

is-zero-well-ordering-principle :
  (P : ℕ → Type₀) (d : is-decidable-predicate P) →
  (n : ℕ) → (pn : P n) → P 0 → pr₁ (well-ordering-principle P d n pn)  ≡ 0
is-zero-well-ordering-principle P d 0 p p0 = refl 0
is-zero-well-ordering-principle P d (suc m) pm =
  is-zero-well-ordering-principle-suc P d m pm (d 0)
    ( well-ordering-principle
      ( λ z → P (suc z))
      ( λ x → d (suc x))
      m pm)
```
