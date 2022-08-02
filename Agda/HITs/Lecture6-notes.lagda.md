```agda

{-# OPTIONS --rewriting --without-K --allow-unsolved-metas #-}

open import new-prelude

open import Lecture4-notes
open import Lecture5-notes
open import Solutions5-dan using (PathOver-path≡)

module Lecture6-notes where

```
# Univalence and the universal cover of the circle

Similarly, univalence says that paths in the universe are equivalences.
We'll start with just the ability to turn an equivalence into a path.

```agda
postulate 
  ua  : ∀ {l : Level} {X Y : Type l} → X ≃ Y → X ≡ Y
```

Next we will work towards characterizing the fundamental group of the
circle.  The homotopy groups of a space are (roughly) the groups of
paths, paths-between-paths, etc. with path concatenation as the group
operation.  The homotopy groups are almost iterated identity types,
except you also need to use truncations (which we haven't talked about
yet).  The iterated identity types represent what is called the n-fold
loop space of a type, Ω^n A, which is the whole space of loops,
loops-between-refls, etc.  E.g.

```
transport-ap-assoc : {A : Type} (C : A → Type) {a a' : A} (p : a ≡ a') {x : C a}
                       → transport C p x ≡ transport (\ X → X) (ap C p) x
transport-ap-assoc C (refl _) = refl _

postulate
  uaβ : ∀{l : Level} {X Y : Type l} (e : X ≃ Y) {x : X} → transport (\ X → X) (ua e) x ≡ fwd e x

transport-→ : {X : Type}
              {A : X → Type}
              {B : X → Type}
              {x x' : X} (p : x ≡ x')
              {f : A x → B x}
            → transport (λ z → (y : A z) → B (z)) p f ≡ \ a → transport B p (f (transport A (! p) a))
transport-→ (refl _) = refl _

transport-inv-r : {X : Type}
                  {A : X → Type}
                  {x x' : X} (p : x ≡ x') (a : A x') 
                → transport A p (transport A (! p) a) ≡ a
transport-inv-r (refl _) a = refl _

PathOver-→ : {X : Type}
             {A : X → Type}
             {B : X → Type}
             {x x' : X} {p : x ≡ x'}
             {f1 : A x → B x}
             {f2 : A x' → B x'}
           → ((a : A x) → f1 a ≡ f2 (transport A p a) [ B ↓ p ])
           → f1 ≡ f2 [ (\ z → A z → B z) ↓ p ]
PathOver-→ {A = A} {B} {p = p} {f2 = f2} h =
  fwd (transport-to-pathover _ _ _ _)
    (transport-→ p ∙ λ≡ \ a → bwd (transport-to-pathover _ _ _ _)
       (h (transport A (! p) a)) ∙  ap f2 (transport-inv-r p a))

pair≡d : {l1 l2 : Level} {A : Type l1} {B : A → Type l2}
         {a a' : A} (p : a ≡ a')
         {b : B a} {b' : B a'} (q : b ≡ b' [ B ↓ p ])
       → (a , b) ≡ (a' , b') [ Σ B ]
pair≡d (refl _) reflo = refl _

fill-left : {X : Type}
            {A : X → Type}
            {x x' : X} (p : x ≡ x') (a : A x')
          → (transport A (! p) a) ≡ a [ A ↓ p ]
fill-left (refl _) a = reflo
              
transport-Π : {X : Type}
              {A : X → Type}
              {B : Σ A → Type}
              {x x' : X} (p : x ≡ x')
              {f : (y : A x) → B (x , y)}
            → transport (λ z → (y : A z) → B (z , y)) p f ≡ \ a → transport B (pair≡d p (fill-left p a)) (f (transport A (! p) a))
transport-Π (refl _) = refl _

PathOver-Π : {X : Type}
             {A : X → Type}
             {B : Σ A → Type}
             {x x' : X} {p : x ≡ x'}
             {f1 : (y : A x) → B (x , y)}
             {f2 : (y' : A x') → B (x' , y')}
           → ({a : A x} {a' : A x'} (q : a ≡ a' [ A ↓ p ]) → f1 a ≡ f2 a' [ B ↓ pair≡d p q ])
           → f1 ≡ f2 [ (\ z → (y : A z) → B (z , y)) ↓ p ]
PathOver-Π {A = A} {B} {p = p} {f1 = f1} {f2} h =
  fwd (transport-to-pathover _ _ _ _)
      ((transport-Π p) ∙ λ≡  \ a → 
       bwd (transport-to-pathover B (pair≡d p (fill-left p a)) _ _) (h _))

PathOver-path-to : ∀ {A : Type} 
                       {a0 a a' : A} {p : a ≡ a'}
                       {q : a0 ≡ a}
                       {r : a0 ≡ a'}
                      → q ∙ p ≡ r
                      → q ≡ r [ (\ x → a0 ≡ x) ↓ p ]
PathOver-path-to {p = refl _} {q = refl _} (refl _) = reflo
```


```agda
Ω¹S1 : Type
Ω¹S1 = base ≡ base

Ω²S1 : Type
Ω²S1 = refl base ≡ refl base [ base ≡ base ] 
```

"Calculating a loops space (or homotopy group)" means proving an
equivalence between the specified loop space and some more explicit
description of a group.  E.g. Ω¹S1 turns out to be the integers ℤ.  

To prove this, we will use the universal cover of the circle, which is a
fibration (type family) over the circle whose fiber over each point is
ℤ, and where going around the loop in the base goes up one level.  This
can be pictured as a helix.  But in type theory we just define it by
saying what the fibers are and what happens when you go around the loop.

```agda
module AssumeInts 
    (ℤ : Type)
    (0ℤ : ℤ)
    (succℤ : ℤ ≃ ℤ)
    (ℤ-rec : {X : Type}
             (b : X)
             (s : X ≃ X)
           → ℤ → X)
    (ℤ-rec-0ℤ : {X : Type}
                (b : X)
                (s : X ≃ X)
              → ℤ-rec b s 0ℤ ≡ b)
    (ℤ-rec-succℤ : {X : Type}
                   (b : X)
                   (s : X ≃ X)
                   (a : ℤ) → ℤ-rec b s (fwd succℤ a) ≡ fwd s (ℤ-rec b s a))
    (ℤ-rec-unique : {X : Type}
                    (f : ℤ → X)
                    (z : X)
                    (s : X ≃ X)
                  → f 0ℤ ≡ z
                  → ((f ∘ fwd succℤ) ∼ (fwd s ∘ f))
                 → (x : ℤ) → f x ≡ ℤ-rec z s x)
    (hSetℤ : is-set ℤ) where

  Cover : S1 → Type
  Cover = S1-rec ℤ (ua succℤ)
```

To check that going around the loop in the base adds one, we need
another bit of the univalence axiom (see above).  

Then we can calculate

```agda
  transport-Cover-loop : (x : ℤ) → transport Cover loop x ≡ fwd succℤ x
  transport-Cover-loop x = transport-ap-assoc Cover loop ∙
                           ap (\ H → transport id H x) (S1-rec-loop _ _) ∙
                           (uaβ  succℤ)

  PathOver-Cover-loop : (x : ℤ) → x ≡ fwd succℤ x [ Cover ↓ loop ]
  PathOver-Cover-loop x = fwd (transport-to-pathover _ _ _ _) (transport-Cover-loop x)
```

```
  loop^ : ℤ → base ≡ base
  loop^ = ℤ-rec (refl _)
                (improve (Isomorphism (\ p → p ∙ loop)
                                      (Inverse (\ p → p ∙ (! loop))
                                               (\ p → ! (∙assoc _ loop (! loop)) ∙
                                                      ap (\ H → p ∙ H) (!-inv-r loop) )
                                               (\ p → ! (∙assoc _ (! loop) loop) ∙
                                                      ap (\ H → p ∙ H) (!-inv-l loop)))))
  -- exercise: state and prove a more general lemma about transporting along p ∙ q
  -- and prove this from it
  transport-Cover-then-loop : {x : S1} (p : x ≡ base) (y : Cover x)
                            → transport Cover (p ∙ loop) y ≡ fwd succℤ (transport Cover p y)
  transport-Cover-then-loop (refl _) y = ap (\ Z → transport Cover (Z) y) (∙unit-l loop) ∙
                                         transport-Cover-loop _
  
  encode : (x : S1) → base ≡ x → Cover x
  encode x p = transport Cover p 0ℤ

  decode : (x : S1) → Cover x → base ≡ x
  decode = S1-elim _
                   loop^
                   (PathOver-→ (\ a →
                    PathOver-path-to (! (ℤ-rec-succℤ _ _ a) ∙ ! (ap loop^ (transport-Cover-loop _)))))
  
  encode-decode : (x : S1) (p : base ≡ x) → decode x (encode x p) ≡ p
  encode-decode .base (refl base) = ℤ-rec-0ℤ _ _

  endo-ℤ-is-id : (f : ℤ → ℤ)
               → f 0ℤ ≡ 0ℤ
               → (f ∘ fwd succℤ) ∼ (fwd succℤ ∘ f)
               → f ∼ id
  endo-ℤ-is-id f f0 fsucc x = ℤ-rec-unique f 0ℤ succℤ f0 fsucc x ∙
                           ! (ℤ-rec-unique (\ x → x) 0ℤ succℤ (refl _) (\ _ → refl _) x)  

  decode-encode : (x : S1) (p : Cover x) → encode x (decode x p) ≡ p
  decode-encode = S1-elim _
                          (\ x → endo-ℤ-is-id encode-loop^ encode-loop^-zero encode-loop^-succ x)
                          (PathOver-Π \ aa' → fwd (transport-to-pathover _ _ _ _) (hSetℤ _ _ _ _)) where
    encode-loop^ : ℤ → ℤ
    encode-loop^ x = encode base (loop^ x)
  
    encode-loop^-zero : encode-loop^ 0ℤ ≡ 0ℤ
    encode-loop^-zero = ap (\ H → transport Cover H 0ℤ) (ℤ-rec-0ℤ _ _)
  
    encode-loop^-succ : (encode-loop^ ∘ fwd succℤ) ∼ (fwd succℤ ∘ encode-loop^)
    encode-loop^-succ x = ap (\ H → encode base H) (ℤ-rec-succℤ _ _ x) ∙
                         transport-Cover-then-loop (loop^ x) 0ℤ 
```
