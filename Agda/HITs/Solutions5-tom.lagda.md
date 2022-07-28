

**To make this file typecheck, you will need to uncomment two REWRITE
  rules, see (†) below. (They are commented because of idiosyncrasies in
  building corresponding GitHub pages.)**

For this week we have two solution files for the exercises.  Tom de
Jong's solutions below.  Dan Licata's solutions are in
Solutions5-dan.lagda.md.  We are providing both to illustrate slightly
different ways of using Agda.  Tom's are a little more verbose and
easier for a person to read non-interactively.  Dan's are a little more
inlined and meant to show you roughly the minimum text you need to get
Agda to check the proofs, but are harder to read unless you do so
interactively (by putting holes around sub-expressions and getting Agda
to tell you what the types are supposed to be).  It's sometimes nice to
code in the terse style when you are coding for yourself, and then to
clean it up more like the more verbose solution when writing it up for
other people.

Note: Agda will get confused if you make a single file that imports both
our solutions and your solutions in Exercises5.  The reason is that
rewrite rules are installed globally, and both files declare rewrites
for the reduction rules for suspension types (if you get that far), and
Agda won't let you install a rewrite for something that already reduces.
(For a similar reason, Solutions5-tom has the rewrites commented out to
make our build scripts for github work, so you will need to uncomment
those in your copy to load the file.)


```agda
{-# OPTIONS --rewriting --without-K #-}

open import new-prelude
open import Lecture5-notes
open import Solutions4 using (ap-!; to-from-base; to-from-loop; s2c; c2s; susp-func)

module Solutions5-tom where
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
to-from = S1-elim (\x → from (to x) ≡ x) to-from-base p
 where
  p : to-from-base ≡ to-from-base [ (\ x → from (to x) ≡ x) ↓ loop ]
  p = PathOver-roundtrip≡ from to loop q
   where
    q : ! to-from-base ∙ (ap from (ap to loop) ∙ to-from-base)
      ≡ loop
    q = ! to-from-base ∙ (ap from (ap to loop) ∙ to-from-base) ≡⟨ refl _ ⟩
        refl _ ∙ (ap from (ap to loop)) ∙ refl _               ≡⟨ refl _ ⟩
        refl _ ∙ (ap from (ap to loop))                        ≡⟨ ∙unit-l (ap from (ap to loop)) ⟩
        ap from (ap to loop)                                   ≡⟨ to-from-loop ⟩
        loop                                                   ∎

circles-equivalent : S1 ≃ Circle2
circles-equivalent = improve (Isomorphism to (Inverse from to-from from-to))
```

# Reversing the circle (⋆⋆)

Define a map S1 → S1 that "reverses the orientation of the circle",
i.e. sends loop to ! loop.

```agda
rev : S1 → S1
rev = S1-rec base (! loop)
```

Prove that rev is an equivalence.  Hint: you will need to state and prove
one new generalized "path algebra" lemma and to use one of the lemmas from
the "Functions are group homomorphism" section of Lecture 4's exercises.
```agda
rev-loop : ap rev loop ≡ ! loop
rev-loop = S1-rec-loop base (! loop)

!-involutive : {X : Type} {x y : X} (p : x ≡ y) → ! (! p) ≡ p
!-involutive (refl _) = refl _

rev-equiv : is-equiv rev
rev-equiv = Inverse rev h rev h
 where
  h : rev ∘ rev ∼ id
  h = S1-elim (\ x → rev (rev x) ≡ x) (refl base) p
   where
    p : refl base ≡ refl base [ (\x -> rev (rev x) ≡ x) ↓ loop ]
    p = PathOver-roundtrip≡ rev rev loop q
     where
      q = refl base ∙ ap rev (ap rev loop) ≡⟨ ∙unit-l _ ⟩
          ap rev (ap rev loop)             ≡⟨ ap (ap rev) rev-loop ⟩
          ap rev (! loop)                  ≡⟨ ap-! loop ⟩
          ! (ap rev loop)                  ≡⟨ ap ! rev-loop ⟩
          ! (! loop)                       ≡⟨ !-involutive loop ⟩
          loop                             ∎
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
                        → q ∙ ap g p ≡ ap f p ∙ r
                        → q ≡ r [ (\ x → (f x) ≡ (g x)) ↓ p ]
PathOver-path≡ {g = g} {f = f} {p = refl a} {q} {r} e = to-prove
 where
  to-prove : q ≡ r [ (\ x → (f x) ≡ (g x)) ↓ (refl a) ]
  to-prove = path-to-pathover (q              ≡⟨ e ⟩
                               refl (f a) ∙ r ≡⟨ ∙unit-l r ⟩
                               r              ∎)

circles-to-torus : S1 → (S1 → Torus)
circles-to-torus = S1-rec f e
 where
  f : S1 → Torus
  f = S1-rec baseT pT
  e : f ≡ f
  e = λ≡ (S1-elim (λ x → f x ≡ f x) qT p)
   where
    p : qT ≡ qT [ (\ x → f x ≡ f x) ↓ loop ]
    p = PathOver-path≡ (qT ∙ ap f loop ≡⟨ ap (qT ∙_) lemma ⟩
                        qT ∙ pT        ≡⟨ ! sT ⟩
                        pT ∙ qT        ≡⟨ ap (_∙ qT) (! lemma) ⟩
                        ap f loop ∙ qT ∎)
     where
      lemma : ap f loop ≡ pT
      lemma = S1-rec-loop baseT pT

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
mult-unit-l y = refl _ -- Choosing (refl _) here helps later on.
```

(⋆) Because we'll need it in a second, show that ap distributes over
function composition:
```agda
ap-∘ : ∀ {l1 l2 l3 : Level} {A : Type l1} {B : Type l2} {C : Type l3}
       (f : A → B) (g : B → C)
       {a a' : A}
       (p : a ≡ a')
     → ap (g ∘ f) p ≡ ap g (ap f p)
ap-∘ _ _ (refl _) = refl _
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
S1-rec-loop-1 {f = f} {h} {a} = ap (\ x → S1-rec f h x a) loop        ≡⟨ ap-∘ (S1-rec f h) (\ f → f a) loop ⟩
                                ap (\ f → f a) (ap (S1-rec f h) loop) ≡⟨ ap (ap (\ f → f a)) (S1-rec-loop f h) ⟩
                                ap (\ f → f a) h                      ≡⟨ refl _ ⟩
                                app≡ h a                              ∎
```
Prove this reduction using ap-∘ and the reduction rule for S1-rec on the loop.

(⋆⋆⋆) Show that base is a right unit for multiplication.  You will need
a slightly different path-over lemma than before.
```agda
PathOver-endo≡ : ∀ {A : Type} {f : A → A}
                 {a a' : A} {p : a ≡ a'}
                 {q : (f a) ≡ a}
                 {r : (f a') ≡ a'}
               → ! q ∙ ((ap f p) ∙ r) ≡ p
               → q ≡ r [ (\ x → f x ≡ x) ↓ p ]
PathOver-endo≡ {f = f} {p = (refl a)} {q = q} {r} h = to-show
 where
  to-show : q ≡ r [ (\ x → f x ≡ x) ↓ refl a ]
  to-show = path-to-pathover (q                          ≡⟨ refl _ ⟩
                              q ∙ refl a                 ≡⟨ ap (q ∙_) (! h) ⟩
                              q ∙ (! q ∙ (refl _ ∙ r))   ≡⟨ ap (\ - → q ∙ (! q ∙ -)) (∙unit-l r) ⟩
                              q ∙ (! q ∙ r)              ≡⟨ ∙assoc q (! q) r ⟩
                              (q ∙ ! q) ∙ r              ≡⟨ ap (_∙ r) (!-inv-r q) ⟩
                              refl _ ∙ r                 ≡⟨ ∙unit-l r ⟩
                              r ∎)

mult-unit-r : (x : S1) → mult x base ≡ x
mult-unit-r = S1-elim (\ x → mult x base ≡ x) (mult-unit-l base) p
 where
  p : mult-unit-l base ≡ mult-unit-l base [ (\ x → mult x base ≡ x) ↓ loop ]
  p = PathOver-endo≡ q
   where
    q = ! (mult-unit-l base) ∙ (ap (\ x → mult x base) loop ∙ mult-unit-l base)   ≡⟨ refl _ ⟩
        ! (refl _) ∙ (ap (\ x → mult x base) loop ∙ refl _)                       ≡⟨ refl _ ⟩
        ! (refl _) ∙ ap (\ x → mult x base) loop                                  ≡⟨ ∙unit-l _ ⟩
        ap (\ x → mult x base) loop                                               ≡⟨ S1-rec-loop-1 ⟩
        app≡ (λ≡ m) base                                                          ≡⟨ λ≡β m base ⟩
        loop ∎
     where
      m : (x : S1) → x ≡ x
      m = S1-elim _ loop (PathOver-path-loop (refl (loop ∙ loop)))
```

# Suspensions and the 2-point circle

(⋆) Postulate the computation rules for the non-dependent susp-rec and
declare rewrites for the point reduction rules on the point constructors.
```agda
postulate
  Susp-rec-north : {l : Level} {A : Type} {X : Type l}
                 (n : X) (s : X) (m : A → n ≡ s)
                 → Susp-rec n s m northS ≡ n
  Susp-rec-south : {l : Level} {A : Type} {X : Type l}
                   (n : X) (s : X) (m : A → n ≡ s)
                   → Susp-rec n s m southS ≡ s
```

**(†) Uncomment these REWRITE rules to make the file typecheck.
      (They are commented because of idiosyncrasies in building corresponding
      GitHub pages.)**
```
-- {-# REWRITE Susp-rec-north #-}
-- {-# REWRITE Susp-rec-south #-}

postulate
  Susp-rec-merid : {l : Level} {A : Type} {X : Type l}
                   (n : X) (s : X) (m : A → n ≡ s)
                 → (x : A) → ap (Susp-rec n s m) (merid x) ≡ m x
```

(⋆) Postulate the dependent elimination rule for suspensions:

```agda
postulate
  Susp-elim : {A : Type} (P : Susp A → Type)
            → (n : P northS)
            → (s : P southS)
            → (m : (x : A) → n ≡ s [ P ↓ merid x ])
            → (x : Susp A) → P x
```

(⋆⋆) Show that the maps s2c and c2s from the Lecture 4 exercises are mutually inverse:

```agda
c2s2c : (x : Circle2) → s2c (c2s x) ≡ x
c2s2c = Circle2-elim _ pₙ pₛ pʷ pᵉ
 where
  pₙ : s2c (c2s north) ≡ north
  pₙ = refl _
  pₛ : s2c (c2s south) ≡ south
  pₛ = refl _
  pʷ : pₙ ≡ pₛ [ (\ x → s2c (c2s x) ≡ x) ↓ west ]
  pʷ = PathOver-roundtrip≡ s2c c2s west
        (refl _ ∙ ap s2c (ap c2s west) ≡⟨ ∙unit-l _ ⟩
         ap s2c (ap c2s west)          ≡⟨ ap (ap s2c) (Circle2-rec-west _ _ _ _) ⟩
         ap s2c (merid true)           ≡⟨ Susp-rec-merid _ _ _ _ ⟩
         west                          ∎)
  pᵉ : pₙ ≡ pₛ [ (\ x → s2c (c2s x) ≡ x) ↓ east ]
  pᵉ = PathOver-roundtrip≡ s2c c2s east
        (refl _ ∙ ap s2c (ap c2s east) ≡⟨ ∙unit-l _ ⟩
         ap s2c (ap c2s east)          ≡⟨ ap (ap s2c) (Circle2-rec-east _ _ _ _) ⟩
         ap s2c (merid false)          ≡⟨ Susp-rec-merid _ _ _ _ ⟩
         east                          ∎)

s2c2s : (x : Susp Bool) → c2s (s2c x) ≡ x
s2c2s = Susp-elim _ pₙ pₛ q
 where
  pₙ : c2s (s2c northS) ≡ northS
  pₙ = refl _
  pₛ : c2s (s2c southS) ≡ southS
  pₛ = refl _
  q : (b : Bool) → PathOver (\ x → c2s (s2c x) ≡ x) (merid b) pₙ pₛ
  q true  = PathOver-roundtrip≡ c2s s2c (merid true)
             (refl _ ∙ ap c2s (ap s2c (merid true)) ≡⟨ ∙unit-l _ ⟩
              ap c2s (ap s2c (merid true))          ≡⟨ ap (ap c2s) (Susp-rec-merid _ _ _ _) ⟩
              ap c2s west                           ≡⟨ Circle2-rec-west _ _ _ _ ⟩
              merid true                            ∎)
  q false = PathOver-roundtrip≡ c2s s2c (merid false)
             (refl _ ∙ ap c2s (ap s2c (merid false)) ≡⟨ ∙unit-l _ ⟩
              ap c2s (ap s2c (merid false))          ≡⟨ ap (ap c2s) (Susp-rec-merid _ _ _ _) ⟩
              ap c2s east                            ≡⟨ Circle2-rec-east _ _ _ _ ⟩
              merid false                            ∎)
```

(⋆) Conclude that Circle2 is equivalent to Susp Bool:

```agda
Circle2-Susp-Bool : Circle2 ≃ Susp Bool
Circle2-Susp-Bool = improve (Isomorphism c2s (Inverse s2c c2s2c s2c2s))
```

# Functoriality of suspension (⋆⋆)

In the Lecture 4 exercises, we defined functoriality for the suspension
type, which given a function X → Y gives a function Σ X → Σ Y.  Show
that this operation is functorial, meaning that it preserves identity
and composition of functions:
```agda
susp-func-id : ∀ {X : Type} → susp-func {X} id ∼ id
susp-func-id = Susp-elim _ (refl _) (refl _)
                           (\x → PathOver-endo≡ (∙unit-l _ ∙ (Susp-rec-merid _ _ _ _)) )

susp-func-∘ : ∀ {X Y Z : Type} (f : X → Y) (g : Y → Z)
            → susp-func {X} (g ∘ f) ∼ susp-func g ∘ susp-func f
susp-func-∘ {X = X} f g = Susp-elim _ (refl _) (refl _) h
 where
  h : (x : X)
    → refl _ ≡ refl _ [ (\s → susp-func (g ∘ f) s ≡ (susp-func g ∘ susp-func f) s) ↓ merid x ]
  h x = PathOver-path≡ (refl _ ∙ ap (susp-func g ∘ susp-func f) (merid x) ≡⟨ ∙unit-l _ ⟩
                        ap (susp-func g ∘ susp-func f) (merid x)          ≡⟨ ap-∘ (susp-func f) (susp-func g) (merid x) ⟩
                        ap (susp-func g) (ap (susp-func f) (merid x))     ≡⟨ ap (ap (susp-func g)) (Susp-rec-merid _ _ _ x) ⟩
                        ap (susp-func g) (merid (f x))                    ≡⟨ Susp-rec-merid _ _ _ (f x) ⟩
                        merid (g (f x))                                   ≡⟨ ! (Susp-rec-merid _ _ _ x) ⟩
                        ap (susp-func (g ∘ f)) (merid x)                  ∎)
```
