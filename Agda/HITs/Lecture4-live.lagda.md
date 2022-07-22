```agda

{-# OPTIONS --without-K --rewriting #-}

open import new-prelude

module Lecture4-live where

  {-
  postulate
    Bool : Type
    true : Bool
    false : Bool
  -}
  
  postulate
    S1 : Type 
    base : S1
    loop : base ≡ base [ S1 ]

  example-path : base ≡ base
  example-path = loop ∙ ! loop ∙ loop ∙ ! loop ∙ loop

  -- groupoid laws

  ∙assoc : {A : Type} {x y z w : A}
         (p : x ≡ y)
         (q : y ≡ z)
         (r : z ≡ w)
         → (p ∙ (q ∙ r)) ≡ ((p ∙ q) ∙ r) [ x ≡ w [ A ] ]
  ∙assoc p q (refl _) = refl _

  ∙unit-l : {A : Type} {x y : A}
          → (p : x ≡ y)
          → (refl _ ∙ p) ≡ p
  ∙unit-l (refl _) = refl _

  ∙unit-r : {A : Type} {x y : A}
          → (p : x ≡ y) → (p ∙ refl _) ≡ p
  ∙unit-r p = refl p

  !-inv-l : {A : Type} {x y : A}
          → (p : x ≡ y)
          → (! p ∙ p) ≡ refl _
  !-inv-l (refl _) = refl _

  !-inv-r : {A : Type} {x y : A} → (p : x ≡ y)
        → (p ∙ ! p) ≡ refl _
  !-inv-r (refl _) = refl _

  example : loop ∙ ! loop ∙ loop ∙ ! loop ∙ loop
          ≡ loop 
  example = loop ∙ ! loop ∙ loop ∙ ! loop ∙ loop       ≡⟨ refl _ ⟩
            (((loop ∙ ! loop) ∙ loop) ∙ ! loop) ∙ loop ≡⟨  ap (\ H → H ∙ loop ∙ ! loop ∙ loop) (!-inv-r loop) ⟩
            ((refl _          ∙ loop) ∙ ! loop) ∙ loop ≡⟨ ap (λ H → H ∙ ! loop ∙ loop) (∙unit-l loop) ⟩
            ((loop ∙ ! loop) ∙ loop)                   ≡⟨  ! (∙assoc _ _ loop) ⟩
            (loop ∙ (! loop ∙ loop))                   ≡⟨  ap (\ H → loop ∙ H) (!-inv-l loop) ⟩
            (loop ∙ refl _)                            ≡⟨ ∙unit-r loop ⟩
            loop ∎

  -- Circle recursion
  postulate
    S1-rec : {X : Type} (x : X) (l : x ≡ x [ X ]) → (S1 → X)
    S1-rec-base : {X : Type} (x : X) (l : x ≡ x [ X ])
                → (S1-rec x l) base ≡ x

  {-# BUILTIN REWRITE _≡_ #-}
  {-# REWRITE S1-rec-base #-}

  postulate
    S1-rec-loop : {X : Type} (x : X) (l : x ≡ x [ X ])
                →  ap (S1-rec x l) loop ≡ l 

  double : S1 → S1
  double = S1-rec base (loop ∙ loop)

  double-loop : ap double loop ≡ loop ∙ loop
  double-loop = S1-rec-loop _ _

  ap-∙ : {A B : Type} {f : A → B} {x y z : A}
         (p : x ≡ y)
         (q : y ≡ z)
       → ap f (p ∙ q) ≡ ap f p ∙ ap f q
  ap-∙ (refl _) (refl _) = refl _

  double-2-loops : ap double (loop ∙ loop) ≡ (loop ∙ loop) ∙ (loop ∙ loop)
  double-2-loops =
    ap double (loop ∙ loop)         ≡⟨ ap-∙ loop loop ⟩
    ap double loop ∙ ap double loop ≡⟨ ap₂ (\ p q → p ∙ q)
                                           (S1-rec-loop _ _)
                                           (S1-rec-loop _ _)  ⟩
    (loop ∙ loop) ∙ (loop ∙ loop) ∎

  postulate
    Circle2 : Type
    north : Circle2
    south : Circle2
    west  : north ≡ south
    east  : north ≡ south
    Circle2-rec : {X : Type}
                  (n : X) (s : X) (w : n ≡ s) (e : n ≡ s)
                → Circle2 → X
    Circle2-rec-north : {X : Type} (n : X) (s : X) (w : n ≡ s) (e : n ≡ s)
                      → Circle2-rec n s w e north ≡ n 
    Circle2-rec-south : {X : Type} (n : X) (s : X) (w : n ≡ s) (e : n ≡ s)
                      → Circle2-rec n s w e south ≡ s 
  {-# REWRITE Circle2-rec-north #-}
  {-# REWRITE Circle2-rec-south #-}

  postulate
    Circle2-rec-west : {X : Type} (n : X) (s : X) (w : n ≡ s) (e : n ≡ s)
                     → ap (Circle2-rec n s w e) west ≡ w
    Circle2-rec-east : {X : Type} (n : X) (s : X) (w : n ≡ s) (e : n ≡ s)
                     → ap (Circle2-rec n s w e) east ≡ e

  to : S1 → Circle2
  to = S1-rec north (east ∙ ! west)

  from : Circle2 → S1
  from = Circle2-rec base base (refl _) loop

  from-to-north : to (from north) ≡ north
  from-to-north = refl _

  from-to-south : to (from south) ≡ south
  from-to-south = west

  from-to-west : ap to (ap from west) ∙ from-to-south ≡ west
  from-to-west = ap to (ap from west) ∙ west ≡⟨ ap (\ H → ap to H ∙ west) (Circle2-rec-west _ _ _ _) ⟩
                 ap to (refl base) ∙ west    ≡⟨ ∙unit-l west ⟩
                 west ∎ 


  -- Q: is loop distinct from refl?
  -- A: so far, maybe

```
