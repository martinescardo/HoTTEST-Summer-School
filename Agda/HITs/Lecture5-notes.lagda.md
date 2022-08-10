```agda
{-# OPTIONS --rewriting --without-K #-}

open import new-prelude

module Lecture5-notes where

open import Lecture4-notes hiding (to; from; from-to-north; from-to-south; from-to-west; from-to-east; q) public

```

# Equivalences

In this lecture, we will start proving some type equivalences, so we
need to code a definition of equivalence.  In the Lecture 3 exercies, we
saw the definition of a bijection/isomorphism/quasi-equivalence in Agda:
a record consisting of maps back and forth with homotopies showing that
they compose to the identity.  In the HoTT track, we saw the definition
of equivalence of types as a bi-invertible map.  We can code this
similarly in Agda:

```agda
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
```

Here are some short names for projecting the the forward and (one of
the) backward maps:

```agda
fwd : ∀ {l1 l2 : Level} {A : Type l1} {B : Type l2} → A ≃ B → A → B
fwd e = _≃_.map e

bwd : ∀ {l1 l2 : Level} {A : Type l1} {B : Type l2} → A ≃ B → B → A
bwd e = is-equiv.post-inverse (_≃_.is-equivalence e)
```

An isomorphism can be improved to an equivalence by using the same
function as the pre-inverse and post-inverse:

```agda
improve : ∀ {l1 l2 : Level} {A : Type l1} {B : Type l2} → A ≅ B → A ≃ B
improve (Isomorphism f (Inverse g gf fg)) = Equivalence f (Inverse g gf g fg)

```

# Path over a path

Next, we will work towards stating the dependent elimination rules /
induction principles for HITs.  To do this, we will need the notion of a
"dependent path" or "path over a path".

Suppose you have a type A with elements a1 and a2 and a type family B :
A → Type with elements b1 : B a1 and b2 : B a2.  It doesn't type check
to ask if b1 ≡ b2 because b1 and b2 have different types.  But if we
also have a path p : a1 ≡ a2 then we can ask whether b1 ≡ b2 "up to"
that path.

Using topological terminology, we can think about the *total space* of
B, type Σ x ∶ A , B, which has a map pr₁ : (Σ x ∶ A , B) → A.  When b :
B x, we say that b is "in the fiber over x", because the element (x , b)
: (Σ x ∶ A , B) projects to x by pr₁.  One way to compare elements in
different fibres is to ask for a path in the total space, i.e. a path
(a1 , b1) ≡ (a2 , b2) [ Σ x ∶ A , B ].  Using the characterization of
paths in Σ types from Lecture 3 as pairs of paths, such a path has a
first component path a1 ≡ a2 [ A ].  We are often interested in paths in
the total space whose first component is a specified path p : a1 ≡ a2 [
A ].  This can be represented by a pair of a path q : (a1 , b1) ≡ (a2 ,
b2) [ Σ x ∶ A , B ] with a path fst (from-Σ-≡ q) ≡ p [ a1 ≡ a2 ].
However, there are a couple of more direct ways to represent this in
type theory.

The first way to represent a path over p is with a new inductive definition:

```agda
data PathOver {l1 l2 : Level} {A : Type l1} (B : A → Type l2) :
              {a1 a2 : A} (p : a1 ≡ a2)
              (b1 : B a1) (b2 : B a2) → Type (l1 ⊔ l2) where
  reflo : {x : A} {y : B x} → PathOver B (refl x) y y 

syntax PathOver B p b1 b2 = b1 ≡ b2 [ B ↓ p ]
```

This is an "inductive family" with one constructor that says that any y
: B x is equal to itself over reflexivity.  

Another way to represent a path over p is as a homogeneous path
transport B p b1 ≡ b2 [ B a2 ].  Semantically, this is because dependent
types are fibrations, which includes that any path-over b1 ≡ b2 [ B ↓ p
] factors uniquely into a heterogeneous path b1 ≡ transport B p b1 [ B ↓
p ] composed with a homogeneous path transport B p b1 ≡ b2 [ B a2 ].

In type theory, we can prove that these are equivalent by path induction:

```
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

ap of a dependent function naturally creates a path-over:
```agda
apd : {l1 l2 : Level} {A : Type l1} {B : A → Type l2}
      (f : (x : A) → B x) {a1 a2 : A} (p : a1 ≡ a2)
    → f a1 ≡ f a2 [ B ↓ p ]
apd f (refl _) = reflo
```

We'll use the inductive family definition mainly because it will be
closer to what you'll see in Lectures 7,8,9 on Cubical Agda.

# Dependent elims/induction for HITs

We're finally in a position to state the dependent elimination rules for
HITs.  Let's start with Circle2 because it's a little easier to see
what's going on.

```agda
postulate
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
                    → apd (Circle2-elim X n s w e) west ≡ w
  Circle2-elim-east : (X : Circle2 → Type) (n : X north) (s : X south)
                      (w : n ≡ s [ X ↓ west ]) (e : n ≡ s [ X ↓ east ])
                    → apd (Circle2-elim X n s w e) east ≡ e
```

# Proving equivalences

One common reason dependent elims get used is to prove that functions
are mutually inverse.

```agda
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

```agda
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

```agda
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
postulate
  S1-elim-loop : (X : S1 → Type)
                 (x : X base)
                 (p : x ≡ x [ X ↓ loop ])
               → apd (S1-elim X x p) loop ≡ p
```

# Multiplication on the circle

Classically, if you think of the points on the circle as complex
numbers, you can multiply two points, and the result will represent a
point on the circle.  There is a synthetic version of this operation in
type theory.  Defining it uses S1-elim and *function extensionality*,
which says that paths between functions are homotopies.  

```agda
PathOver-path-loop : ∀ {A : Type} 
                     {a a' : A} {p : a ≡ a'}
                     {q : a ≡ a}
                     {r : a' ≡ a'}
                   → q ∙ p ≡ p ∙ r
                   → q ≡ r [ (\ x → x ≡ x) ↓ p ]
PathOver-path-loop {p = (refl _)} h = path-to-pathover (h ∙ (∙unit-l _)) 

mult : S1 → S1 → S1
mult = S1-rec ((\ y → y)) (λ≡ (S1-elim (λ z → z ≡ z) loop (PathOver-path-loop (refl _))))
```

Note that it is also possible to do this without funext by binding the
second input before doing the S1-rec on the first input (thanks Ulrik!):
```agda
mult-nofunext : S1 → S1 → S1
mult-nofunext x y = S1-rec y (S1-elim (λ z → z ≡ z) loop (PathOver-path-loop (refl _)) y) x
```

Above, we used the main part of function extensionality: a homotopy
induces a path between functions.  The full form of the function
extensionality axiom (mentioned briefly in HoTT Lecture 5) is that
homotopies are equivalent to paths between functions, and in particular
that the map from paths to homotopies that you can define by path
induction is an equivalence.

```agda
app≡ : {l1 l2 : Level} {A : Type l1} {B : A → Type l2} {f g : (x : A) → B x} → f ≡ g → f ∼ g
app≡ p x = ap (\ f → f x) p 

postulate
  λ≡βinv : {l1 l2 : Level} {A : Type l1} {B : A → Type l2} {f g : (x : A) → B x} → (h : f ∼ g) 
      → app≡ (λ≡ h) ≡ h

-- it's often more useful to have this as a homotopy
λ≡β : {l1 l2 : Level} {A : Type l1} {B : A → Type l2} {f g : (x : A) → B x} → (h : f ∼ g) 
      → app≡ (λ≡ h) ∼ h
λ≡β h = app≡ (λ≡βinv h)

full-funext : {l1 l2 : Level} {A : Type l1} {B : A → Type l2} {f g : (x : A) → B x}
            → is-equiv {A = f ≡ g} {B = f ∼ g} app≡
full-funext = Inverse λ≡' λ≡η λ≡ λ≡βinv where
  postulate
    λ≡' : _
    λ≡η : _
```


