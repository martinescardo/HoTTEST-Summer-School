# Week 7 - Cubical Agda Exercises - Solutions

```agda
{-# OPTIONS --cubical #-}

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


## Part III: Some HITs
### Exercise 9
```agda
{-


The torus:

  ∙ ->->->-> ∙
  ∧          ∧
  |          |
  ∧          ∧
  |          |
  ∙ ->->->-> ∙




The Klein bottle:

  ∙ <-<-<-<- ∙
  ∧          ∧
  |          |
  ∧          ∧
  |          |
  ∙ ->->->-> ∙


-}
data KleinBottle : Type where
  point : KleinBottle
  line1 : point ≡ point
  line2 : point ≡ point
  square : PathP (λ i → line1 (~ i) ≡ line1 i) line2 line2

data KleinBottle' : Type where
  point : KleinBottle'
  line1 : point ≡ point
  line2 : point ≡ point
  square : (sym line1) ∙ line2 ∙ line1 ≡ line2
```



### Exercise 10
```agda
suspUnitChar : Susp Unit ≡ Interval
suspUnitChar = isoToPath (iso to fro toFro froTo)
  where
  to : Susp Unit → Interval
  to north = zero
  to south = one
  to (merid ⋆ i) = seg i

  fro : Interval → Susp Unit
  fro zero = north
  fro one = south
  fro (seg i) = merid ⋆ i

  toFro : (b : Interval) → to (fro b) ≡ b
  toFro zero = refl
  toFro one = refl
  toFro (seg i) = refl

  froTo : (s : Susp Unit) → fro (to s) ≡ s
  froTo north = refl
  froTo south = refl
  froTo (merid ⋆ i) = refl
```



### Exercise 11
```agda
SuspPushout : Type ℓ → Type ℓ
SuspPushout A = Pushout {A = A} {B = Unit} {C = Unit} (λ a → ⋆) (λ a → ⋆)

Susp≡SuspPushout : (A : Type ℓ) → Susp A ≡ SuspPushout A
Susp≡SuspPushout A = isoToPath (iso to fro toFro froTo)
  where
  to : Susp A → SuspPushout A
  to north = inl ⋆
  to south = inr ⋆
  to (merid a i) = push a i

  fro : SuspPushout A → Susp A
  fro (inl ⋆) = north
  fro (inr ⋆) = south
  fro (push a i) = merid a i

  toFro : (b : SuspPushout A) → to (fro b) ≡ b
  toFro (inl ⋆) = refl
  toFro (inr ⋆) = refl
  toFro (push a i) = refl

  froTo : (s : Susp A) → fro (to s) ≡ s
  froTo north = refl
  froTo south = refl
  froTo (merid a i) = refl
```

### Exercise 12

```agda
comp-filler : {x y z : A} (p : x ≡ y) (q : y ≡ z)
            → PathP (λ j → refl {x = x} j ≡ q j) p (p ∙ q)
comp-filler {x = x} p q j i = hfill (λ k → λ { (i = i0) → x
                                              ; (i = i1) → q k })
                                    (inS (p i)) j

rUnit : {x y : A} (p : x ≡ y) → p ∙ refl ≡ p
rUnit p = sym (comp-filler p refl)



suspBoolChar : Susp Bool ≡ S¹
suspBoolChar = isoToPath (iso to fro toFro froTo)
  where
  to : Susp Bool → S¹
  to north = base
  to south = base
  to (merid true i) = loop i
  to (merid false i) = base

  fro : S¹ → Susp Bool
  fro base = north
  fro (loop i) = (merid true ∙ sym (merid false)) i

  toFro : (b : S¹) → to (fro b) ≡ b
  toFro base = refl
  toFro (loop i) j = mySquare j i
    where
    mySquare : ap to (merid true ∙ sym (merid false)) ≡ loop
    mySquare = ap to (merid true ∙ sym (merid false)) ≡⟨ refl ⟩
               ap to (merid true) ∙ ap to (sym (merid false)) ≡⟨ refl ⟩
               ap to (merid true) ∙ refl ≡⟨ refl ⟩
               loop ∙ refl ≡⟨ rUnit loop ⟩
               loop ∎

  froTo : (s : Susp Bool) → fro (to s) ≡ s
  froTo north = refl
  froTo south = merid false
  froTo (merid true i) j = mySquare (~ j) i
    where
    mySquare : PathP (λ j → north ≡ sym (merid false) j)
                     (merid true)
                     (merid true ∙ sym (merid false))
    mySquare = comp-filler (merid true) (sym (merid false))
  froTo (merid false i) j = merid false (i ∧ j)
```
