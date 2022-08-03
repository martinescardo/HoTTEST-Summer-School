```agda

{-# OPTIONS --rewriting --without-K #-}

open import new-prelude

open import Lecture4-notes
open import Lecture5-notes
open import Solutions5-dan using (PathOver-path≡)

module Lecture6-live where

{- remember the definition of S1 from Lectures 4 and 5

  S1 : Type
  base : S1
  loop : base ≡ base

  For {l : Level} {X : Type l} (x : X) (p : x ≡ x)
    S1-rec : S1 → X
    S1-rec-base : S1-rec x p base ≡ x
    S1-rec-loop : ap (S1-rec x p) loop ≡ p

  For {l : Level} (X : S1 → Type l)
      (x : X base)
      (p : x ≡ x [ X ↓ loop ])
    S1-elim : (x : S1) → X x
    S1-elim-base : S1-elim X x p base ≡ x
    S1-elim-loop : apd (S1-elim X x p) loop ≡ p

-}

Ω¹S1 : Type
Ω¹S1 = base ≡ base [ S1 ]

Ω²S1 : Type
Ω²S1 = refl base ≡ refl base [ base ≡ base [ S1 ] ]

{-
Correspondence

-2   ! loop ∙ ! loop   
-1   ! loop 
 0   refl _       , loop ∙ ! loop 
 1   loop         , loop ∙ loop ∙ ! loop
 2   loop ∙ loop

 refl _ =? loop NO, but we have to prove it
   
-}

data ℤ : Type where
 Pos : ℕ → ℤ  -- Pos 0 = 1 
 Zero : ℤ -- 0
 Neg : ℕ → ℤ -- Neg 0 = -1

module AssumeInts 
    (ℤ : Type)

    (0ℤ : ℤ)
    
    (succℤ : ℤ ≃ ℤ) -- successor and predecessor 


    (ℤ-rec : {X : Type}
             (z : X)
             (s : X ≃ X)
            → ℤ → X)


    (ℤ-rec-0ℤ : {X : Type}
                (z : X)
                (s : X ≃ X)
              → ℤ-rec z s 0ℤ ≡ z )
    (ℤ-rec-succℤ : {X : Type}
                   (z : X)
                   (s : X ≃ X)
                 → (x : ℤ) → ℤ-rec z s (fwd succℤ x) ≡ fwd s (ℤ-rec z s x))

    (ℤ-rec-unique : {X : Type}
                    (f : ℤ → X)
                    (z : X)
                    (s : X ≃ X)
                  → f 0ℤ ≡ z
                  → ((x : ℤ) → f (fwd succℤ x) ≡ fwd s (f x))
                 → (x : ℤ) → f x ≡ ℤ-rec z s x)
    where


  loop^ : ℤ → base ≡ base
  loop^ = ℤ-rec (refl _)
                (improve (Isomorphism (\ p → p ∙ loop)
                                      (Inverse (\ q → q ∙ ! loop)
                                               (\ p → ! (∙assoc _ loop (! loop))
                                                      ∙ ap (\ H → p ∙ H) (!-inv-r loop))
                                               (\ p → ! (∙assoc _ (! loop) (loop))
                                                      ∙ ap (\ H → p ∙ H) (!-inv-l loop)))))

  postulate 
    ua  : ∀ {l : Level} {X Y : Type l} → X ≃ Y → X ≡ Y
    uaβ : ∀ {l : Level} {X Y : Type l} (e : X ≃ Y) {x : X}
        → transport (\ X → X) (ua e) x ≡ fwd e x

  Cover : S1 → Type
  Cover = S1-rec ℤ (ua succℤ)

  transport-ap-assoc : {A : Type} (C : A → Type) {a a' : A} (p : a ≡ a') {x : C a}
                     → transport C p x ≡
                       transport (\ X → X) (ap C p) x
  transport-ap-assoc C (refl _) = refl _
  

  transport-Cover-loop : (x : ℤ) → transport Cover loop x ≡ fwd succℤ x
  transport-Cover-loop x = transport-ap-assoc Cover loop ∙
                           (ap (\ H → transport id H x) (S1-rec-loop _ _)
                           ∙ uaβ _)

  transport-Cover-then-loop : {x : S1} (p : x ≡ base) (y : Cover x)
                            → transport Cover (p ∙ loop) y ≡ fwd succℤ (transport Cover p y)
  transport-Cover-then-loop (refl _) y = ap (\ Z → transport Cover (Z) y) (∙unit-l loop) ∙
                                         transport-Cover-loop _

  encode : (x : S1) → base ≡ x → Cover x
  encode x p = transport Cover p 0ℤ
  -- .base (refl base) = 0ℤ

  encode-firsttry : base ≡ base → ℤ
  encode-firsttry = encode base

  endo-ℤ-is-id : (f : ℤ → ℤ)
               → f 0ℤ ≡ 0ℤ
               → ((x : ℤ) → f (fwd succℤ x) ≡ fwd succℤ (f x))
               → f ∼ id
  endo-ℤ-is-id f f0 fsucc x = ℤ-rec-unique f 0ℤ succℤ f0 fsucc x ∙
                             ! (ℤ-rec-unique (\x → x) 0ℤ succℤ (refl _) (\ _ → refl _) x) 

  encode-loop^ : (x : ℤ) → encode-firsttry (loop^ x) ≡ x
  encode-loop^ = endo-ℤ-is-id (encode-firsttry ∘ loop^)
                              (ap encode-firsttry (ℤ-rec-0ℤ _ _) ∙
                               refl _)
                              \ x → ap (\ H → encode base H) (ℤ-rec-succℤ _ _ x) ∙
                                    goal x where
    goal : (x : _) → transport Cover (loop^ x ∙ loop) 0ℤ ≡
                     fwd succℤ (transport Cover (loop^ x) 0ℤ)
    goal x = transport-Cover-then-loop (loop^ x) 0ℤ

  postulate
    PathOver-→ : {X : Type}
               {A : X → Type}
               {B : X → Type}
               {x x' : X} {p : x ≡ x'}
               {f1 : A x → B x}
               {f2 : A x' → B x'}
             → ((a : A x) → f1 a ≡ f2 (transport A p a) [ B ↓ p ])
             → f1 ≡ f2 [ (\ z → A z → B z) ↓ p ]
  -- this can be proved from function extensionality, see the Lecture 6 notes

  PathOver-path-to : ∀ {A : Type} 
                       {a0 a a' : A} {p : a ≡ a'}
                       {q : a0 ≡ a}
                       {r : a0 ≡ a'}
                      → q ∙ p ≡ r
                      → q ≡ r [ (\ x → a0 ≡ x) ↓ p ]
  PathOver-path-to {p = refl _} (refl _) = reflo

  decode : (x : S1) → Cover x → base ≡ x
  decode = S1-elim _ loop^
                     (PathOver-→ \ z → PathOver-path-to
                       (! (ap loop^ (transport-Cover-loop z) ∙
                         ℤ-rec-succℤ _ _ _ )))

  encode-decode : (x : S1) (p : base ≡ x) → decode x (encode x p) ≡  p 
  encode-decode .base (refl base) = ℤ-rec-0ℤ _ _

  loop^-encode : (p : base ≡ base) → loop^ (encode-firsttry p) ≡ p
  loop^-encode = encode-decode base

  theorem : (base ≡ base) ≃ ℤ
  theorem = improve (Isomorphism (encode base) (Inverse loop^ loop^-encode encode-loop^))

```

