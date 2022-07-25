```
{-# OPTIONS --rewriting --without-K #-}

open import new-prelude

module Lecture5-notes where

open import Lecture4-notes hiding (to; from; from-to-north; from-to-south; from-to-west; from-to-east; q) public

```

# Equivalences

```
record is-equiv {l1 l2 : Level} {A : Type l1} {B : Type l2} (f : A → B) : Type (l1 ⊔ l2) where
  constructor Inverse
  field
    post-inverse    : B → A
    is-post-inverse : post-inverse ∘ f ∼ id
    pre-inverse     : B → A
    is-pre-inverse  : f ∘ pre-inverse ∼ id

record _≃_ {l1 l2 : Level} (A : Type l1) (B : Type l2) : Type (l1 ⊔ l2) where
  constructor
    Equivalence
  field
    map : A → B
    is-equivalence : is-equiv map

fwd : ∀ {A B : Type} → A ≃ B → A → B
fwd e = _≃_.map e

bwd : ∀ {A B : Type} → A ≃ B → B → A
bwd e = is-equiv.post-inverse (_≃_.is-equivalence e)

improve : ∀ {l1 l2 : Level} {A : Type l1} {B : Type l2} → A ≅ B → A ≃ B
improve (Isomorphism f (Inverse g gf fg)) = Equivalence f (Inverse g gf g fg)

```

# Path over a path

```

data PathOver {l1 l2 : Level} {A : Type l1} (B : A → Type l2) : {a1 a2 : A} (p : a1 ≡ a2) (b1 : B a1) (b2 : B a2) → Type (l1 ⊔ l2) where
  reflo : {x : A} {y : B x} → PathOver B (refl x) y y 

syntax PathOver B p b1 b2 = b1 ≡ b2 [ B ↓ p ]

transport-to-pathover : {l1 l2 : Level} {A : Type l1} (B : A → Type l2)
                        {a1 a2 : A} (p : a1 ≡ a2)
                        (b1 : B a1) (b2 : B a2)
                     → (transport B p b1 ≡ b2) ≃ (b1 ≡ b2 [ B ↓ p ]) 
transport-to-pathover B (refl _) b1 b2 = improve (Isomorphism ((λ { (refl _) → reflo }))
                                                       (Inverse (\ { reflo → refl _})
                                                                (\ {(refl _) → refl _})
                                                                (\ {(reflo) → refl _})))

path-to-pathover : ∀ {A : Type} {B : A → Type}
                 → {a : A} {x y : B a}
                 → (p : x ≡ y)
                 → x ≡ y [ B ↓ refl a ]
path-to-pathover p = fwd (transport-to-pathover _ (refl _) _ _) p
```

# Dependent elims/induction for HITs

```
postulate
  Circle2-elim : (X : Circle2 → Type)
                 (n : X north)
                 (s : X south)
                 (w : n ≡ s [ X ↓ west ])
                 (e : n ≡ s [ X ↓ east ])
               → (x : Circle2) → X x
  Circle2-elim-north : (X : Circle2 → Type) (n : X north) (s : X south) (w : n ≡ s [ X ↓ west ]) (e : n ≡ s [ X ↓ east ])
                     → Circle2-elim X n s w e north ≡ n 
  Circle2-elim-south : (X : Circle2 → Type) (n : X north) (s : X south) (w : n ≡ s [ X ↓ west ]) (e : n ≡ s [ X ↓ east ])
                     → Circle2-elim X n s w e south ≡ s
  -- also need that dependent ap on west/east reduces to w/e 
```

# Proving equivalences

```
module RememberTheseFromLastTime where

  to : S1 → Circle2
  to = S1-rec north (east ∙ ! west)
  
  from : Circle2 → S1
  from = Circle2-rec base base (refl base) loop
  
  from-to-north : to (from north) ≡ north
  from-to-north = refl _
  
  from-to-south : to (from south) ≡ south
  from-to-south = west
  
  from-to-west : ap to (ap from west) ∙ from-to-south ≡ west
  from-to-west = ap to (ap from west) ∙ west ≡⟨ ap (\ H → ap to H ∙ west) (Circle2-rec-west _ _ _ _) ⟩
                  ap to (refl base) ∙ west    ≡⟨ ∙unit-l west ⟩
                  west ∎ 
  
  from-to-east : ap to (ap from east) ∙ from-to-south ≡ east
  from-to-east = ap to (ap from east) ∙ west ≡⟨ ap (\ H → ap to H ∙ west) (Circle2-rec-east _ _ _ _) ⟩
                 ap to loop ∙ west           ≡⟨ ap (\ H → H ∙ west) (S1-rec-loop _ _) ⟩
                 east ∙ ! west ∙ west        ≡⟨ ! (∙assoc _ (! west) west) ⟩
                 east ∙ (! west ∙ west)      ≡⟨ ap (\ H → east ∙ H) (!-inv-l west) ⟩
                 east ∎
open RememberTheseFromLastTime public
```

```
PathOver-roundtrip≡ : ∀ {A B : Type} (g : B → A) (f : A → B)
                        {a a' : A} (p : a ≡ a')
                        {q : g (f a) ≡ a}
                        {r : g (f a') ≡ a'}
                      → ! q ∙ ((ap g (ap f p)) ∙ r) ≡ p
                      → q ≡ r [ (\ x → g (f x) ≡ x) ↓ p ]
PathOver-roundtrip≡ g f  (refl _) {q = q} {r} h =
  path-to-pathover (ap (\ H → q ∙ H) (! h) ∙
                       ( ∙assoc _ _ (refl _ ∙ r) ∙
                        (ap (\ H → H ∙ (refl _ ∙ r)) (!-inv-r q) ∙
                         (∙unit-l (refl _ ∙ r) ∙  ∙unit-l r )) ))

from-to : (y : Circle2) → to (from y) ≡ y
from-to = Circle2-elim _
                       from-to-north
                       from-to-south
                       (PathOver-roundtrip≡ to from west (∙unit-l _ ∙ from-to-west))
                       (PathOver-roundtrip≡ to from east (∙unit-l _ ∙ from-to-east))
```

To do the other direction you'll need 

```
postulate
  S1-elim : (X : S1 → Type)
            (x : X base)
            (p : x ≡ x [ X ↓ loop ])
          → (x : S1) → X x
  
  S1-elim-base : (X : S1 → Type)
                 (x : X base)
                 (p : x ≡ x [ X ↓ loop ])
               → S1-elim X x p base ≡ x

{-# REWRITE S1-elim-base #-}
-- also need a reduction for dependent ap of S1-elim on loop
```

# Multiplication by angle x

```
PathOver-path-loop : ∀ {A : Type} 
                   {a a' : A} {p : a ≡ a'}
                   {q : a ≡ a}
                   {r : a' ≡ a'}
                 → q ∙ p ≡ p ∙ r
                 → q ≡ r [ (\ x → x ≡ x) ↓ p ]
PathOver-path-loop {p = (refl _)} h =  path-to-pathover (h ∙ (∙unit-l _)) 

mult : S1 → S1 → S1
mult = S1-rec ((\ x → x)) (λ≡ (S1-elim _ loop (PathOver-path-loop (refl _))))
```

Rest of funext

```
app≡ : {l1 l2 : Level} {A : Type l1} {B : A → Type l2} {f g : (x : A) → B x} → f ≡ g → f ∼ g
app≡ p x = ap (\ f → f x) p 

postulate
  λ≡β : {l1 l2 : Level} {A : Type l1} {B : A → Type l2} {f g : (x : A) → B x} → (h : f ∼ g) (a : A)
      → app≡ (λ≡ h) a ≡ h a
  -- really should be an equivalence but this is all we'll need for now 
```

