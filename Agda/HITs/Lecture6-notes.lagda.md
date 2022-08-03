```agda

{-# OPTIONS --rewriting --without-K #-}

open import new-prelude

open import Lecture4-notes
open import Lecture5-notes
open import Solutions5-dan using (PathOver-path≡)

module Lecture6-notes where

```

In this class, we will go over the proof that the fundamental group of
the circle is the integers.  Mike Shulman first proved this theorem in
HoTT; the proof below is my simplified version of his proof.

# Univalence

Univalence says that paths in the universe are equivalences.  We'll
start with just the ability to turn an equivalence into a path.  

```agda
postulate 
  ua  : ∀ {l : Level} {X Y : Type l} → X ≃ Y → X ≡ Y
```

There is already a converse to this map: to turn a path X ≡ Y into and
equivalence, we can do path induction to contract X to Y, and then
return the identity equivalence X ≃ X.  Call this path-to-equiv:

```agda
id≃ : ∀ {A : Type} → A ≃ A
id≃ = Equivalence ((\ x → x)) (Inverse (\ x → x) (\ _ → refl _) (\ x → x) (\ _ → refl _))

path-to-equiv : ∀ {A B : Type} → A ≡ B → A ≃ B
path-to-equiv (refl _) = id≃
```

Note that fwd (path-to-equiv p) is equal to transport (\ X → X) p):
```agda 
fwd-path-to-equiv : ∀ {A B : Type} (p : A ≡ B) → fwd (path-to-equiv p) ≡ transport (\ X → X) p 
fwd-path-to-equiv (refl _) = refl _
```

In full, the univalence axiom says that this map path-to-equiv is an
equivalence between equivalences and paths.  For our purposes today, we
will only need one more bit of that equivalence, which says that
transport (\ X → X) after ua is the identity:

```agda
postulate
  uaβ : ∀{l : Level} {X Y : Type l} (e : X ≃ Y) {x : X}
      → transport (\ X → X) (ua e) x ≡ fwd e x
```
(This extra bit actually turns out to imply the full univalence axiom,
using the fact that is-equiv is a proposition, and the fundamental
theorem of identity types (see the HoTT track).)

# Lemma library

Here are a bunch of general facts that are provable from path induction.
In class, we will prove these as they come up in the proof, but they
need to be lifted outside of the AssumeInts module for the exercises
code to work, since they don't actually depend on those assumptions.  

```agda
transport-ap-assoc : {A : Type} (C : A → Type) {a a' : A} (p : a ≡ a') {x : C a}
                       → transport C p x ≡ transport (\ X → X) (ap C p) x
transport-ap-assoc C (refl _) = refl _

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

# Fundamental group of the circle

Next we will work towards characterizing the fundamental group of the
circle.  The homotopy groups of a space are (roughly) the groups of
paths, paths-between-paths, etc. with path concatenation as the group
operation.  The homotopy groups are almost defined as iterated identity
types like this:

```agda
Ω¹S1 : Type
Ω¹S1 = base ≡ base

Ω²S1 : Type
Ω²S1 = refl base ≡ refl base [ base ≡ base ] 
```

The almost is because you also need to use truncations (which we haven't
talked about yet) to remove the higher structure of these path types.
The iterated identity types represent what is called the n-fold loop
space of a type, Ω^n A, which is the whole space of loops,
loops-between-refls, etc. 

"Calculating a loops space (or homotopy group)" means proving an
equivalence between the specified loop space and some more explicit
description of a group.  E.g. Ω¹S1 turns out to be the integers ℤ.

We can enumerate ℤ many paths on the circle: … -2 (! loop ∙ ! loop), -1
(! loop), 0 (refl _), 1 (loop), 2 (loop ∙ loop), …  Of course, there are
others, like loop ∙ ! loop, but that has a path-between-paths to
refl --- we're counting paths "up to homotopy" or "up to the higher
identity types".  So, intuitively, every loop on the circle is homotopic
to one of the above form.  The other way this equivalence could fail is if
e.g. loop ≡ refl _, so there wouldn't be as many paths as it looks like.
But we didn't add any path-between-path constructors to S1,
so intuitively in the "least" type generated by base and loop,
there are no such identifications.  

To prove this in HoTT, we will use the universal cover of the circle,
which is a fibration (type family) over the circle whose fiber over each
point is ℤ, and where going around the loop in the base goes up one
level.  This can be pictured as a helix.  But in type theory we just
define it by saying what the fibers are and what happens when you go
around the loop.  To do this, we need a definition of the integers.  

For now, we'll just assume a definition of the integers that supplies
exactly what we need to do this proof.  Much of an implementation is
below.

First, we have a type ℤ with 0 and successor functions.  Just that would
define ℕ; to get ℤ, we also want successor to be an equivalence -- with
the inverse being the predecessor.

Next, the universal property of the integers is that it's the
"least"/"initial" type with a point and an equivalence: you can map into
any other type with a point and an equivalence.
Intuitively, this sends 0 to b, +n to (fwd s)^n b
and -b to (bwd s)^n b.  Moreover, this map is unique, in the sense that
any other map that sends 0 to some point z and successor to some equivalence s
is equal to the map determined by ℤ-rec.  

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
```

Using ℤ-rec, we define a map "loop to the nth power", which maps an integer n to
a loop on the circle as indicated above:
… -2 (! loop ∙ ! loop), -1 (! loop), 0 (refl _), 1 (loop), 2 (loop ∙ loop), …

```agda
  loop^ : ℤ → base ≡ base
  loop^ = ℤ-rec (refl _)
                (improve (Isomorphism (\ p → p ∙ loop)
                                      (Inverse (\ p → p ∙ (! loop))
                                               (\ p → ! (∙assoc _ loop (! loop)) ∙
                                                      ap (\ H → p ∙ H) (!-inv-r loop) )
                                               (\ p → ! (∙assoc _ (! loop) loop) ∙
                                                      ap (\ H → p ∙ H) (!-inv-l loop)))))
```

But mapping loops to ints is harder.  The trick is to define a type
family/fibrations over S1, where transporting in that type family
converts paths to ints.  This is where the universal cover of the
circle/the helix comes in:

```agda
  Cover : S1 → Type
  Cover = S1-rec ℤ (ua succℤ)
```

For example, we can calculate that transporting in the Cover on the loop
adds one:

```agda
  transport-Cover-loop : (x : ℤ) → transport Cover loop x ≡ fwd succℤ x
  transport-Cover-loop x = transport-ap-assoc Cover loop ∙
                           ap (\ H → transport id H x) (S1-rec-loop _ _) ∙
                           (uaβ  succℤ)

  PathOver-Cover-loop : (x : ℤ) → x ≡ fwd succℤ x [ Cover ↓ loop ]
  PathOver-Cover-loop x = fwd (transport-to-pathover _ _ _ _) (transport-Cover-loop x)
```

Now we can define

```agda
  encode : (x : S1) → base ≡ x → Cover x
  encode x p = transport Cover p 0ℤ
```

For the other direction, we need to use S1-elim:

```agda
  decode : (x : S1) → Cover x → base ≡ x
  decode = S1-elim _
                   loop^
                   (PathOver-→ (\ a →
                    PathOver-path-to (! (ℤ-rec-succℤ _ _ a) ∙
                                      ! (ap loop^ (transport-Cover-loop _)))))
```

One composite is easy by path induction:

```agda
  encode-decode : (x : S1) (p : base ≡ x) → decode x (encode x p) ≡ p
  encode-decode .base (refl base) = ℤ-rec-0ℤ _ _
```

(This composite can actually be abstracted into a general lemma; see the
fundamental theorem of identity types in the HoTT track.)

For the other composite, we do circle induction, use the uniqueness
principle for maps out of ℤ, and use the fact that ℤ is a set to easily
finish the final goal:

```agda
  endo-ℤ-is-id : (f : ℤ → ℤ)
               → f 0ℤ ≡ 0ℤ
               → (f ∘ fwd succℤ) ∼ (fwd succℤ ∘ f)
               → f ∼ id
  endo-ℤ-is-id f f0 fsucc x = ℤ-rec-unique f 0ℤ succℤ f0 fsucc x ∙
                           ! (ℤ-rec-unique (\ x → x) 0ℤ succℤ (refl _) (\ _ → refl _) x)  

  transport-Cover-then-loop : {x : S1} (p : x ≡ base) (y : Cover x)
                            → transport Cover (p ∙ loop) y ≡ fwd succℤ (transport Cover p y)
  transport-Cover-then-loop (refl _) y = ap (\ Z → transport Cover (Z) y) (∙unit-l loop) ∙
                                         transport-Cover-loop _
  
  decode-encode-base : (x : ℤ) → encode base (loop^ x) ≡ x
  decode-encode-base x = endo-ℤ-is-id encode-loop^ encode-loop^-zero encode-loop^-succ x where
    encode-loop^ : ℤ → ℤ
    encode-loop^ x = encode base (loop^ x)
  
    encode-loop^-zero : encode-loop^ 0ℤ ≡ 0ℤ
    encode-loop^-zero = ap (\ H → transport Cover H 0ℤ) (ℤ-rec-0ℤ _ _)
  
    encode-loop^-succ : (encode-loop^ ∘ fwd succℤ) ∼ (fwd succℤ ∘ encode-loop^)
    encode-loop^-succ x = ap (\ H → encode base H) (ℤ-rec-succℤ _ _ x) ∙
                          transport-Cover-then-loop (loop^ x) 0ℤ 


  decode-encode : (x : S1) (p : Cover x) → encode x (decode x p) ≡ p
  decode-encode = S1-elim _
                          decode-encode-base 
                          (PathOver-Π \ aa' → fwd (transport-to-pathover _ _ _ _) (hSetℤ _ _ _ _)) 
```

Here's most of an implementation of integers:

```agda
module ImplementInts where

  fix : ∀ {l1 l2 : Level} {A : Type l1} {B : Type l2}
    → A ≃ B
    → A ≃ B
  fix (Equivalence f (Inverse g fg g' fg')) =
    Equivalence f (Inverse g fg g
                  (\x → ! (ap f (ap g (fg' x))) ∙ (ap f (fg (g' x)) ∙ fg' x)))

  fwd-bwd : ∀ {l1 l2 : Level} {A : Type l1} {B : Type l2}
          → (e : A ≃ B) 
          → fwd e ∘ bwd e ∼ id
  fwd-bwd e = is-equiv.is-pre-inverse (_≃_.is-equivalence (fix e))

  bwd-fwd : ∀ {l1 l2 : Level} {A : Type l1} {B : Type l2}
          → (e : A ≃ B) 
          → bwd e ∘ fwd e ∼ id
  bwd-fwd e = is-equiv.is-post-inverse (_≃_.is-equivalence (fix e))

  data ℤ : Type where
    Pos : ℕ → ℤ
    Zero : ℤ
    Neg : ℕ → ℤ

  0ℤ : ℤ
  0ℤ = Zero

  succ-fn : ℤ → ℤ
  succ-fn (Pos x) = Pos (suc x)
  succ-fn Zero = Pos zero
  succ-fn (Neg zero) = Zero
  succ-fn (Neg (suc x)) = Neg x

  pred-fn : ℤ → ℤ
  pred-fn (Pos zero) = Zero
  pred-fn (Pos (suc x)) = Pos x
  pred-fn Zero = Neg zero
  pred-fn (Neg x) = Neg (suc x)

  succ-pred : (x : ℤ) → succ-fn (pred-fn x) ≡ x
  succ-pred (Pos zero) = refl _
  succ-pred (Pos (suc x)) = refl _
  succ-pred Zero = refl _
  succ-pred (Neg zero) = refl _
  succ-pred (Neg (suc x)) = refl _

  pred-succ : (x : ℤ) → pred-fn (succ-fn x) ≡ x
  pred-succ (Pos zero) = refl _
  pred-succ (Pos (suc x)) = refl _
  pred-succ Zero = refl _
  pred-succ (Neg zero) = refl _
  pred-succ (Neg (suc x)) = refl _

  succℤ : ℤ ≃ ℤ
  succℤ = improve (Isomorphism succ-fn (Inverse pred-fn pred-succ succ-pred))

  ℤ-rec : {X : Type}
          (b : X)
          (s : X ≃ X)
         → ℤ → X
  ℤ-rec b s (Pos zero) = fwd s b
  ℤ-rec b s (Pos (suc x)) = fwd s (ℤ-rec b s (Pos x))
  ℤ-rec b s Zero = b
  ℤ-rec b s (Neg zero) = bwd s b
  ℤ-rec b s (Neg (suc x)) = bwd s (ℤ-rec b s (Neg x))

  ℤ-rec-0ℤ : {X : Type}
                (b : X)
                (s : X ≃ X)
              → ℤ-rec b s 0ℤ ≡ b
  ℤ-rec-0ℤ b s = refl _

  ℤ-rec-succℤ : {X : Type}
                (b : X)
                (s : X ≃ X)
                (a : ℤ) → ℤ-rec b s (fwd succℤ a) ≡ fwd s (ℤ-rec b s a)
  ℤ-rec-succℤ b s (Pos x) = refl _
  ℤ-rec-succℤ b s Zero = refl _
  ℤ-rec-succℤ b s (Neg zero) = ! (fwd-bwd s b)
  ℤ-rec-succℤ b s (Neg (suc zero)) = ! (fwd-bwd s _)
  ℤ-rec-succℤ b s (Neg (suc (suc x))) = ! (fwd-bwd s _)

  f-pred : {X : Type}
           (f : ℤ → X)
           (s : X ≃ X)
         → ((f ∘ fwd succℤ) ∼ (fwd s ∘ f))
         → f ∘ bwd succℤ ∼ bwd s ∘ f
  f-pred f s h x = ! (bwd-fwd s _) ∙
                   ! (ap (bwd s) (h (bwd succℤ x))) ∙
                   ap (bwd s) (ap f (fwd-bwd succℤ x))

  ℤ-rec-unique : {X : Type}
                 (f : ℤ → X)
                 (z : X)
                 (s : X ≃ X)
               → f 0ℤ ≡ z
               → ((f ∘ fwd succℤ) ∼ (fwd s ∘ f))
               → (x : ℤ) → f x ≡ ℤ-rec z s x
  ℤ-rec-unique f z s p q (Pos zero) = q 0ℤ ∙ ap (fwd s) p 
  ℤ-rec-unique f z s p q (Pos (suc x)) = q (Pos x) ∙ ap (fwd s) (ℤ-rec-unique f z s p q (Pos x))
  ℤ-rec-unique f z s p q Zero = p
  ℤ-rec-unique f z s p q (Neg zero) = f-pred f s q Zero ∙ ap (bwd s) p
  ℤ-rec-unique f z s p q (Neg (suc x)) = f-pred f s q (Neg x) ∙ ap (bwd s) ((ℤ-rec-unique f z s p q (Neg x))) 
    
  -- the fact that ℤ is a set can be proved using Hedberg's theorem,
  -- see ../Lecture-Notes/Hedbergs-Theorem.lagda.md
  -- and ../Lecture-Notes/decidability.lagda.md
  -- ℤ has decidable equality because it is equivalent to the coproduct ℕ + 1 + ℕ
  -- and ℕ has decidable equality and coproducts preserve decidable equality


  module Instantiate = AssumeInts ℤ 0ℤ succℤ ℤ-rec ℤ-rec-0ℤ ℤ-rec-succℤ ℤ-rec-unique 

```
