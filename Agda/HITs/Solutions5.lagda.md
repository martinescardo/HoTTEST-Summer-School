```
{-# OPTIONS --rewriting --without-K #-}

open import new-prelude
open import Lecture5-notes
open import Solutions4 using (ap-!; to-from-base; to-from-loop; s2c; c2s; susp-func)

module Solutions5 where
```

# 1 point and 2 point circles are equivalent (⋆)

In lecture, we defined maps between the one point circle (S1) and the
two point circle (Circle2) and checked that the round-trip on Circle2 is
the identity.

Prove that the round-trip on S1 is the identity (use to-from-base
and to-from-loop from the Lecture 4 exercises), and package all of
these items up as an equivalence S1 ≃ Circle2.  

```
to-from : (x : S1) → from (to x) ≡ x
to-from = S1-elim _
                  to-from-base
                  (PathOver-roundtrip≡ from to loop (∙unit-l _ ∙ to-from-loop))

circles-equivalent : S1 ≃ Circle2
circles-equivalent = improve (Isomorphism to (Inverse from to-from from-to))
```

# Circles to torus (⋆⋆)

In the Lecture 4 exercises, you defined a map from the Torus to S1 × S1.
In this problem, you will define a converse map.  The goal is for these
two maps to be part of an equivalence, but we won't prove that in these
exercises.  

You will need to state and prove a lemma characterizing a path over a
path in a path fibration.  Then, to define the map S1 × S1 → Torus, you
will want to curry it and use S1-rec and/or S1-elim on each circle.  

```
PathOver-path≡ : ∀ {A B : Type} {g : A → B} {f : A → B}
                          {a a' : A} {p : a ≡ a'}
                          {q : (f a) ≡ (g a)}
                          {r : (f a') ≡ (g a')}
                        → q ∙ ap g p ≡ ap f p ∙ r
                        → q ≡ r [ (\ x → (f x) ≡ (g x)) ↓ p ]
PathOver-path≡ {p = (refl _)} h = path-to-pathover (h ∙ ∙unit-l _)

circles-to-torus : S1 → (S1 → Torus)
circles-to-torus = S1-rec (S1-rec baseT qT)
                          (λ≡ (S1-elim _
                                       pT
                                       (PathOver-path≡ (ap (\ H → pT ∙ H) (S1-rec-loop _ _) ∙
                                                        sT ∙
                                                        ap (\ H → H ∙ pT) (! (S1-rec-loop _ _))))))

circles-to-torus' : S1 × S1 → Torus
circles-to-torus' (x , y) = circles-to-torus x y
```

# H space 

The multiplication operation on the circle discussed in lecture is part
of what is called an "H space" structure on the circle.  One part of
this structure is that the circle's basepoint is a unit element for
multiplication.

(⋆) Show that base is a left unit.
```
mult-unit-l : (y : S1) → mult base y ≡ y
mult-unit-l y = refl _
```

(⋆⋆⋆) Show that base is a right unit.

```
PathOver-endo≡ : ∀ {A : Type} {f : A → A}
                 {a a' : A} {p : a ≡ a'}
                 {q : (f a) ≡ a}
                 {r : (f a') ≡ a'}
               → ! q ∙ ((ap f p) ∙ r) ≡ p
               → q ≡ r [ (\ x → f x ≡ x) ↓ p ]
PathOver-endo≡ {p = (refl _)} {q = q} {r} h =
  path-to-pathover (ap (\ H → q ∙ H) (! h) ∙
                       ( ∙assoc _ _ (refl _ ∙ r) ∙
                        (ap (\ H → H ∙ (refl _ ∙ r)) (!-inv-r q) ∙
                         (∙unit-l (refl _ ∙ r) ∙  ∙unit-l r )) ))

ap-∘ : ∀ {l1 l2 l3 : Level} {A : Type l1} {B : Type l2} {C : Type l3}
       (f : A → B) (g : B → C)
       {a a' : A}
       (p : a ≡ a')
     → ap (g ∘ f) p ≡ ap g (ap f p)
ap-∘ _ _ (refl _) = refl _

S1-rec-loop-1 : ∀ {A B : Type} {f : A → B} {h : f ≡ f} {a : A}
                     →  ap (\ x → S1-rec f h x a) loop ≡ app≡ h a
S1-rec-loop-1 {f = f}{h}{a} = (ap-∘ (S1-rec f h) (\ z → z a) loop) ∙ ap (ap (\ z → z a)) (S1-rec-loop _ _)

mult-unit-r : (x : S1) → mult x base ≡ x
mult-unit-r = S1-elim _ (refl _) (PathOver-endo≡ ((∙unit-l _) ∙ (S1-rec-loop-1 ∙ (λ≡β _ _ ∙ refl _)) ))
```

# Suspensions and the 2-point circle

(⋆) Postulate the computation rules for the non-dependent susp-rec and
declare rewrites for the point reduction rules on the point constructors.  
```
postulate
  Susp-rec-north : {l : Level} {A : Type} {X : Type l}
                 (n : X) (s : X) (m : A → n ≡ s)
                 → Susp-rec n s m northS ≡ n
  Susp-rec-south : {l : Level} {A : Type} {X : Type l}
                   (n : X) (s : X) (m : A → n ≡ s)
                   → Susp-rec n s m southS ≡ s
{-# REWRITE Susp-rec-north #-}
{-# REWRITE Susp-rec-south #-}
postulate
  Susp-rec-merid : {l : Level} {A : Type} {X : Type l}
                   (n : X) (s : X) (m : A → n ≡ s)
                 → (x : A) → ap (Susp-rec n s m) (merid x) ≡ m x
```

(⋆) Postulate the dependent elimination rule for suspensions:

```
postulate 
  Susp-elim : {A : Type} (P : Susp A → Type)
            → (n : P northS)
            → (s : P southS)
            → (m : (x : A) → n ≡ s [ P ↓ merid x ])
            → (x : Susp A) → P x
```

(⋆⋆) Show that the maps s2c and c2s from the Lecture 4 exercises are mutually inverse:

```
c2s2c : (x : Circle2) → s2c (c2s x) ≡ x
c2s2c = Circle2-elim _ (refl _) (refl _)
                    (PathOver-roundtrip≡ s2c c2s _
                     (∙unit-l _ ∙ (ap (ap s2c) (Circle2-rec-west _ _ _ _) ∙ Susp-rec-merid _ _ _ _)))
                    (PathOver-roundtrip≡ s2c c2s _
                     (∙unit-l _ ∙ (ap (ap s2c) (Circle2-rec-east _ _ _ _) ∙ Susp-rec-merid _ _ _ _)))

s2c2s : (x : Susp Bool) → c2s (s2c x) ≡ x
s2c2s = Susp-elim _ (refl _) (refl _) \ { true → PathOver-roundtrip≡ c2s s2c _
                                                 (∙unit-l _ ∙
                                                  (ap (ap c2s) (Susp-rec-merid _ _ _ _)
                                                  ∙ Circle2-rec-west _ _ _ _)) ;
                                          false → PathOver-roundtrip≡ c2s s2c _
                                                  (∙unit-l _ ∙
                                                  (ap (ap c2s) (Susp-rec-merid _ _ _ _)
                                                  ∙ Circle2-rec-east _ _ _ _))}
```

(⋆) Conclude that Circle2 is equivalent to Susp Bool:

```
Circle2-Susp-Bool : Circle2 ≃ Susp Bool
Circle2-Susp-Bool = improve (Isomorphism c2s (Inverse s2c c2s2c s2c2s)) 
```

# Functoriality of suspension (⋆⋆)

In the Lecture 4 exercises, we defined functoriality for the suspension
type, which given a function X → Y gives a function Σ X → Σ Y.  Show
that this operation is functorial, meaning that it preserves identity
and composition of functions:
```
susp-func-id : ∀ {X : Type} → susp-func {X} id ∼ id
susp-func-id = Susp-elim _ (refl _) (refl _)
                           (\x → PathOver-endo≡ (∙unit-l _ ∙ (Susp-rec-merid _ _ _ _)) )

susp-func-∘ : ∀ {X Y Z : Type} (f : X → Y) (g : Y → Z)
            → susp-func {X} (g ∘ f) ∼ susp-func g ∘ susp-func f
susp-func-∘ f g = Susp-elim _
                            (refl _)
                            (refl _)
                            (\x → PathOver-path≡ (∙unit-l _ ∙
                                                 ap-∘ (susp-func f)  (susp-func g) _ ∙
                                                 ap (ap (susp-func g)) (Susp-rec-merid _ _ _ _) ∙
                                                 Susp-rec-merid _ _ _ _ ∙
                                                 ! (Susp-rec-merid _ _ _ _)))
```



