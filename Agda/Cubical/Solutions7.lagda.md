```agda
```


```agda
{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Solutions7 where

open import cubical-prelude
open import Lecture7-notes
```

```agda
private
  variable
    A : Type ℓ
    B : A → Type ℓ
```

## Part I:

### Exercise 1
```agda
depFunExt : {f g : (x : A) → B x}
          → (∀ x → f x ≡ g x)
          → f ≡ g
depFunExt h i x = h x i
```

### Exercise 2
```agda
apd : (f : (x : A) → B x) {x y : A} (p : x ≡ y) → PathP (λ i → B (p i)) (f x) (f y)
apd f p i = f (p i)

```


## Part II

### Exercise 3
```agda
inhPropIsContr : isProp A → A → isContr A
inhPropIsContr h a = a , h a
```

### Exercise 4
```agda
isPropΠ : (h : (x : A) → isProp (B x)) → isProp ((x : A) → B x)
isPropΠ h f g i x = h x (f x) (g x) i
```

### Exercise 5
```agda
funExt⁻ : {f g : (x : A) → B x} → f ≡ g → ((x : A) → f x ≡ g x)
funExt⁻  p x i = p i x
```

### Exercise 6
```agda
isSetΠ : (h : (x : A) → isSet (B x)) → isSet ((x : A) → B x)
isSetΠ h f g p q i j x = h x (f x) (g x) (funExt⁻ p x) (funExt⁻ q x) i j
```

### Exercise 7
```agda
singl' : {A : Type ℓ} (a : A) → Type ℓ
singl' {A = A} a = Σ x ꞉ A , x ≡ a

isContrSingl' : (x : A) → isContr (singl' x)
isContrSingl' x = ctr , prf
  where
  ctr : singl' x
  ctr = (x , refl)

  prf : (s : singl' x) → ctr ≡ s
  prf (y , p) i = p (~ i) , λ j → p ((~ i) ∨ j)
```


## Part III: Equality in Σ-types
### Exercise 8
```agda
module _ {A : Type ℓ} {B : A → Type ℓ'} {x y : Σ A B} where

  ΣPathP : Σ p ꞉ pr₁ x ≡ pr₁ y , PathP (λ i → B (p i)) (pr₂ x) (pr₂ y)
         → x ≡ y
  ΣPathP (p , q) i = p i , q i

  PathPΣ : x ≡ y
         → Σ p ꞉ pr₁ x ≡ pr₁ y , PathP (λ i → B (p i)) (pr₂ x) (pr₂ y)
  PathPΣ p = (ap pr₁ p) , (apd pr₂ p)

  ΣPathP-PathPΣ : ∀ p → PathPΣ (ΣPathP p) ≡ p
  ΣPathP-PathPΣ _ = refl

  PathPΣ-ΣPathP : ∀ p → ΣPathP (PathPΣ p) ≡ p
  PathPΣ-ΣPathP _ = refl
```
