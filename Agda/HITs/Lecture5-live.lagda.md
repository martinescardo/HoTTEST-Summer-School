```agda
{-# OPTIONS --rewriting --without-K #-}

open import new-prelude

module Lecture5-live where

open import Lecture4-notes hiding (to; from; from-to-north; from-to-south; from-to-west; from-to-east; q) public

record is-equiv {l1 l2 : Level} {A : Type l1} {B : Type l2} (f : A → B) : Type (l1 ⊔ l2) where
 constructor
  Inverse
 field
  inverse : B → A
  η       : inverse ∘ f ∼ id
  inverse2 : B → A
  ε       : f ∘ inverse2 ∼ id

record _≃_ {l1 l2 : Level} (A : Type l1) (B : Type l2) : Type (l1 ⊔ l2) where
 constructor
  Equivalence
 field
  map   : A → B
  is-equivalence : is-equiv map

fwd : ∀ {l1 l2 : Level} {A : Type l1} {B : Type l2} → A ≃ B → A → B
fwd e = _≃_.map e

bwd : ∀ {l1 l2 : Level} {A : Type l1} {B : Type l2} → A ≃ B → B → A
bwd e = is-equiv.inverse (_≃_.is-equivalence e)

improve : ∀ {l1 l2 : Level} {A : Type l1} {B : Type l2} → A ≅ B → A ≃ B
improve (Isomorphism f (Inverse g gf fg)) =
  Equivalence f (Inverse g gf g fg)

data PathOver {l1 l2 : Level}
              {A : Type l1} (B : A → Type l2) :
              {a1 a2 : A} (p : a1 ≡ a2)
              (b1 : B a1) (b2 : B a2) → Type (l1 ⊔ l2) where
  reflo : {x : A} {y : B x} → PathOver B (refl x) y y

-- b1 ≡ b2 [ B a2 ] doesn't type check

syntax PathOver B p b1 b2 = b1 ≡ b2 [ B ↓ p ]

transport-to-pathover : {l1 l2 : Level} {A : Type l1} (B : A → Type l2)
                        {a1 a2 : A} (p : a1 ≡ a2)
                        (b1 : B a1) (b2 : B a2)
                     → (transport B p b1 ≡ b2 [ B a2 ]) ≃ (b1 ≡ b2 [ B ↓ p ]) 
transport-to-pathover B (refl _) b1 b2 =
  Equivalence (λ { (refl _) → reflo })
              (Inverse (\ { reflo → refl _})
                       (\ { (refl _) → refl _} )
                       ((\ { reflo → refl _}))
                       (\ { reflo → refl _}))

path-to-pathover : ∀ {A : Type} {B : A → Type}
                 → {a : A} {x y : B a}
                 → (p : x ≡ y)
                 → x ≡ y [ B ↓ refl a ]
path-to-pathover = fwd (transport-to-pathover _ _ _ _)

apd : {l1 l2 : Level} {A : Type l1} {B : A → Type l2}
      (f : (x : A) → B x) {a1 a2 : A} (p : a1 ≡ a2)
    → f a1 ≡ f a2 [ B ↓ p ]
apd f (refl _) = reflo

postulate

  -- Circle2-rec : {X : Type} (n : X) (s : X) (w : n ≡ s) (e : n ≡ s)
  --             → Circle2 → X

  Circle2-elim : (X : Circle2 → Type)
                 (n : X north)
                 (s : X south)
                 (w : n ≡ s [ X ↓ west ])
                 (e : n ≡ s [ X ↓ east ])
               → (x : Circle2) → X x

  Circle2-elim-north : (X : Circle2 → Type) (n : X north) (s : X south)
                       (w : n ≡ s [ X ↓ west ]) (e : n ≡ s [ X ↓ east ])
                     → Circle2-elim X n s w e north ≡ n
  Circle2-elim-south : (X : Circle2 → Type) (n : X north) (s : X south)
                       (w : n ≡ s [ X ↓ west ]) (e : n ≡ s [ X ↓ east ])
                     → Circle2-elim X n s w e south ≡ s
{-# REWRITE Circle2-elim-north #-}
{-# REWRITE Circle2-elim-south #-}
postulate
  Circle2-elim-west : (X : Circle2 → Type) (n : X north) (s : X south)
                      (w : n ≡ s [ X ↓ west ]) (e : n ≡ s [ X ↓ east ])
                    → apd (Circle2-elim X n s w e) west
                    ≡ w
  Circle2-elim-east : (X : Circle2 → Type) (n : X north) (s : X south)
                      (w : n ≡ s [ X ↓ west ]) (e : n ≡ s [ X ↓ east ])
                    → apd (Circle2-elim X n s w e) east ≡ e


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
  from-to-west =  ap to (ap from west) ∙ from-to-south ≡⟨ ap (\ H → ap to H ∙ from-to-south) (Circle2-rec-west _ _ _ _)  ⟩
                  ap to (refl base) ∙ from-to-south  ≡⟨ ∙unit-l from-to-south ⟩
                  from-to-south  ≡⟨ refl _ ⟩
                  west ∎  
  
  from-to-east : ap to (ap from east) ∙ from-to-south ≡ east
  from-to-east = ap to (ap from east) ∙ from-to-south ≡⟨ ap (\ H → ap to H ∙ from-to-south) (Circle2-rec-east _ _ _ _) ⟩
                 ap to loop ∙ from-to-south           ≡⟨ ap (\ H → H ∙ from-to-south) (S1-rec-loop _ _) ⟩
                 east ∙ ! west ∙ from-to-south        ≡⟨ ! (∙assoc _ (! west) from-to-south) ⟩
                 east ∙ (! west ∙ from-to-south)      ≡⟨ ap (\ H → east ∙ H) (!-inv-l west) ⟩
                 east ∎
                    
open RememberTheseFromLastTime public

PathOver-roundtrip≡ : ∀ {A B : Type} (g : B → A) (f : A → B)
                        {a a' : A} (p : a ≡ a')
                        {q : g (f a) ≡ a}
                        {r : g (f a') ≡ a'}
                      → ! q ∙ ap g (ap f p) ∙ r ≡ p 
                      → q ≡ r [ (\ x → g (f x) ≡ x) ↓ p ]
PathOver-roundtrip≡ g f (refl _) h = path-to-pathover (coh _ _ h) where
  coh : ∀ {A : Type} {a1 a2 : A} (q : a1 ≡ a2) (r : a1 ≡ a2)
      → ! q ∙ r ≡ refl _
      → q ≡ r
  coh (refl _) q h = ! h ∙ ∙unit-l q

from-to : (y : Circle2) → to (from y) ≡ y
from-to = Circle2-elim _
                       from-to-north
                       from-to-south
                       (PathOver-roundtrip≡ to from west {q = from-to-north} {r = from-to-south}
                         ( ! (∙assoc _ _ from-to-south) ∙ (∙unit-l _ ∙ from-to-west )))
                       ((PathOver-roundtrip≡ to from east (! (∙assoc _ _ from-to-south) ∙ ∙unit-l _ ∙ from-to-east)))

postulate
  S1-elim : (X : S1 → Type)
            (x : X base)
            (p : x ≡ x [ X ↓ loop ] )
          → (x : S1) → X x

  S1-elim-base : (X : S1 → Type)
                 (x : X base)
                 (p : x ≡ x [ X ↓ loop ])
               → S1-elim X x p base ≡ x

{-# REWRITE S1-elim-base #-}
postulate
  S1-elim-loop : (X : S1 → Type)
                 (x : X base)
                 (p : x ≡ x [ X ↓ loop ])
               → apd (S1-elim X x p) loop ≡ p



PathOver-path-loop : ∀ {A : Type} 
                     {a a' : A} {p : a ≡ a'}
                     {q : a ≡ a}
                     {r : a' ≡ a'}
                   → q ∙ p ≡ p ∙ r 
                   → q ≡ r [ (\ x → x ≡ x) ↓ p ]
PathOver-path-loop {p = refl _} (refl .(refl _ ∙ _)) = path-to-pathover (∙unit-l _)

mult : S1 → (S1 → S1)
mult = S1-rec ((\ x → x))
              (λ≡ (S1-elim _
                           loop
                           (PathOver-path-loop (refl _) )))

-- full funext

app≡ : {l1 l2 : Level} {A : Type l1} {B : A → Type l2}
       {f g : (x : A) → B x}
     → f ≡ g → f ∼ g
app≡ p x = ap (\ f → f x) p 

postulate
  λ≡βinv : {l1 l2 : Level} {A : Type l1} {B : A → Type l2} {f g : (x : A) → B x}
         → (h : f ∼ g) 
      → app≡ (λ≡ h) ≡ h


```
