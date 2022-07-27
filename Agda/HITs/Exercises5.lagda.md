
```agda
{-# OPTIONS --rewriting --without-K --allow-unsolved-metas #-}

open import new-prelude
open import Lecture5-notes
open import Solutions4 using (ap-!; to-from-base; to-from-loop; s2c; c2s; susp-func)

module Exercises5 where
```

# 1 point and 2 point circles are equivalent (⋆)

In lecture, we defined maps between the one point circle (S1) and the
two point circle (Circle2) and checked that the round-trip on Circle2 is
the identity.

Prove that the round-trip on S1 is the identity (use to-from-base
and to-from-loop from the Lecture 4 exercises), and package all of
these items up as an equivalence S1 ≃ Circle2.  

```agda
to-from : (x : S1) → from (to x) ≡ x
to-from = {!!}

circles-equivalent : S1 ≃ Circle2
circles-equivalent = {!!}
```

# Reversing the circle (⋆⋆) 

Define a map S1 → S1 that "reverses the orientation of the circle",
i.e. sends loop to ! loop.

```agda
rev : S1 → S1
rev = {!!}
```

Prove that rev is an equivalence.  Hint: you will need to state and prove
one new generalized "path algebra" lemma and to use one of the lemmas from
the "Functions are group homomorphism" section of Lecture 4's exercises.  
```agda
rev-equiv : is-equiv rev
rev-equiv = {!!}
```


# Circles to torus (⋆⋆)

In the Lecture 4 exercises, you defined a map from the Torus to S1 × S1.
In this problem, you will define a converse map.  The goal is for these
two maps to be part of an equivalence, but we won't prove that in these
exercises.  

You will need to state and prove a lemma characterizing a path over a
path in a path fibration.  Then, to define the map S1 × S1 → Torus, you
will want to curry it and use S1-rec and/or S1-elim on each circle.  

```agda
PathOver-path≡ : ∀ {A B : Type} {g : A → B} {f : A → B}
                          {a a' : A} {p : a ≡ a'}
                          {q : (f a) ≡ (g a)}
                          {r : (f a') ≡ (g a')}
                        → {!!}
                        → q ≡ r [ (\ x → (f x) ≡ (g x)) ↓ p ]
PathOver-path≡ {A}{B}{g}{f}{a}{a'}{p}{q}{r} h = {!!}

circles-to-torus : S1 → (S1 → Torus)
circles-to-torus = {!!}

circles-to-torus' : S1 × S1 → Torus
circles-to-torus' (x , y) = circles-to-torus x y
```

**Below are some "extra credit" exercise if you want more to do.  These
are (even more) optional: nothing in the next lecture will depend on you
understanding them.  The next section (H space) is harder code but uses
only the circle, whereas the following sections are a bit easier code
but require understanding the suspension type, which we haven't talked
about too much yet.**

# H space 

The multiplication operation on the circle discussed in lecture is part
of what is called an "H space" structure on the circle.  One part of
this structure is that the circle's basepoint is a unit element for
multiplication.

(⋆) Show that base is a left unit.
```agda
mult-unit-l : (y : S1) → mult base y ≡ y
mult-unit-l y = {!!}
```

(⋆) Because we'll need it in a second, show that ap distributes over
function composition:
```agda
ap-∘ : ∀ {l1 l2 l3 : Level} {A : Type l1} {B : Type l2} {C : Type l3}
       (f : A → B) (g : B → C)
       {a a' : A}
       (p : a ≡ a')
     → ap (g ∘ f) p ≡ ap g (ap f p)
ap-∘ = {!!}
```

(⋆⋆) Suppose we have a curried function f : S1 → A → B.  Under the
equivalence between paths in S1 × A and pairs of paths discussed in
Lecture 3, we can then "apply" (the uncurried version of) f to a pair of
paths (p : x ≡ y [ S1 ] , q : z ≡ w [ A ]) to get a path (f x z ≡ f y w
[ B ]).  In the special case where q is reflexivity on a, this
application to p and q can be simplified to ap (\ x → f x a) p : f x a ≡
f y a [ B ].

Now, suppose that f is defined by circle recursion.  We would expect
some kind of reduction for applying f to the pair of paths (loop , q) ---
i.e. we should have reductions for *nested* pattern matching on HITs.
In the case where q is reflexivity, applying f to the pair (loop , refl)
can reduce like this:
```agda
S1-rec-loop-1 : ∀ {A B : Type} {f : A → B} {h : f ≡ f} {a : A}
                     →  ap (\ x → S1-rec f h x a) loop ≡ app≡ h a
S1-rec-loop-1 {A}{B}{f}{h}{a} = {!!}
```
Prove this reduction using ap-∘ and the reduction rule for S1-rec on the loop.  

(⋆⋆⋆) Show that base is a right unit for multiplication.  You will need
a slightly different path-over lemma than before.

```agda
PathOver-endo≡ : ∀ {A : Type} {f : A → A}
                 {a a' : A} {p : a ≡ a'}
                 {q : (f a) ≡ a}
                 {r : (f a') ≡ a'}
               → {!!}
               → q ≡ r [ (\ x → f x ≡ x) ↓ p ]
PathOver-endo≡ {p = (refl _)} {q = q} {r} h = {!!}

mult-unit-r : (x : S1) → mult x base ≡ x
mult-unit-r = {!!}
```

# Suspensions and the 2-point circle

(⋆) Postulate the computation rules for the non-dependent susp-rec and
declare rewrites for the reduction rules on the point constructors.  
```agda
postulate
  Susp-rec-north : {l : Level} {A : Type} {X : Type l}
                 (n : X) (s : X) (m : A → n ≡ s)
                 → Susp-rec n s m northS ≡ {!!}
  Susp-rec-south : {l : Level} {A : Type} {X : Type l}
                   (n : X) (s : X) (m : A → n ≡ s)
                   → Susp-rec n s m southS ≡ {!!}
-- {-# REWRITE Susp-rec-north #-}
-- {-# REWRITE Susp-rec-south #-}
postulate
  Susp-rec-merid : {l : Level} {A : Type} {X : Type l}
                   (n : X) (s : X) (m : A → n ≡ s)
                 → (x : A) → ap (Susp-rec n s m) (merid x) ≡ {!!}
```

(⋆) Postulate the dependent elimination rule for suspensions:

```agda
postulate 
  Susp-elim : {l : Level} {A : Type} (P : Susp A → Type l)
            → (n : {!!})
            → (s : {!!})
            → (m : {!!})
            → (x : Susp A) → P x
```

(⋆⋆) Show that the maps s2c and c2s from the Lecture 4 exercises are mutually inverse:

```agda
c2s2c : (x : Circle2) → s2c (c2s x) ≡ x
c2s2c = {!!}

s2c2s : (x : Susp Bool) → c2s (s2c x) ≡ x
s2c2s = {!!}
```

(⋆) Conclude that Circle2 is equivalent to Susp Bool:

```agda
Circle2-Susp-Bool : Circle2 ≃ Susp Bool
Circle2-Susp-Bool = {!!}
```

# Functoriality of suspension (⋆⋆)

In the Lecture 4 exercises, we defined functoriality for the suspension
type, which given a function X → Y gives a function Σ X → Σ Y.  Show
that this operation is functorial, meaning that it preserves identity
and composition of functions:
```agda
susp-func-id : ∀ {X : Type} → susp-func {X} id ∼ id
susp-func-id = {!!}

susp-func-∘ : ∀ {X Y Z : Type} (f : X → Y) (g : Y → Z)
            → susp-func {X} (g ∘ f) ∼ susp-func g ∘ susp-func f
susp-func-∘ f g = {!!}
```



