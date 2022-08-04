```agda

{-# OPTIONS --rewriting --without-K --allow-unsolved-metas #-}

open import new-prelude

open import Lecture6-notes
open import Lecture5-notes hiding (S1; base; loop)

module Solutions6-wedge-of-circles where
```

We need finite types

```agda
data Fin : ℕ → Type where
 zero : {n : ℕ} → Fin (suc n)
 suc  : {n : ℕ} → Fin n → Fin (suc n)
```

We postulate the HIT representing the wedge of k circles

```agda
postulate
  Wedge-S1 : ℕ → Type

module _ {n : ℕ} where

  postulate
    base : Wedge-S1 n
    loop : Fin n → base ≡ base
    Wedge-S1-elim : {l : Level}
                  → (A : Wedge-S1 n → Type l)
                  → (a : A base)
                  → ((k : Fin n) → a ≡ a [ A ↓ loop k ])
                  → (x : Wedge-S1 n) → A x
    Wedge-S1-elim-base : {l : Level}
                       → {A : Wedge-S1 n → Type l}
                       → {a : A base}
                       → {p : (k : Fin n) → a ≡ a [ A ↓ loop k ]}
                       → Wedge-S1-elim A a p base ≡ a
  {-# REWRITE Wedge-S1-elim-base #-}

  postulate
    Wedge-S1-elim-loop : {l : Level}
                       → {A : Wedge-S1 n → Type l}
                       → {a : A base}
                       → {p : (k : Fin n) → a ≡ a [ A ↓ loop k ]}
                       → (k : Fin n) → apd (Wedge-S1-elim A a p) (loop k) ≡ p k
```

We prove the recursion principle

```agda
PathOver-constant : {l1 l2 : Level} {A : Type l1} {B : Type l2}
                  → {a1 a2 : A}
                  → (p : a1 ≡ a2)
                  → {b1 b2 : B}
                  → b1 ≡ b2
                  → b1 ≡ b2 [ (\ _ → B) ↓ p ]
PathOver-constant (refl _) (refl _) = reflo

PathOver-constant-inverse : {l1 l2 : Level} {A : Type l1} {B : Type l2}
                          → {a1 a2 : A}
                          → (p : a1 ≡ a2)
                          → {b1 b2 : B}
                          → b1 ≡ b2 [ (\ _ → B) ↓ p ]
                          → b1 ≡ b2
PathOver-constant-inverse (refl _) reflo = refl _

PathOver-constant-inverse-cancel1 : {l1 l2 : Level} {A : Type l1} {B : Type l2}
                          → {a1 a2 : A}
                          → (p : a1 ≡ a2)
                          → {b1 b2 : B}
                          → (q : b1 ≡ b2)
                          → PathOver-constant-inverse p (PathOver-constant p q) ≡ q
PathOver-constant-inverse-cancel1 (refl _) (refl _) = refl _

PathOver-constant-inverse-cancel2 : {l1 l2 : Level} {A : Type l1} {B : Type l2}
                          → {a1 a2 : A}
                          → (p : a1 ≡ a2)
                          → {b1 b2 : B}
                          → (q : b1 ≡ b2 [ _ ↓ p ])
                          → PathOver-constant p (PathOver-constant-inverse p q) ≡ q
PathOver-constant-inverse-cancel2 (refl _) reflo = refl _

PathOver-constant-equiv : {l1 l2 : Level} {A : Type l1} {B : Type l2}
                          → {a1 a2 : A}
                          → (p : a1 ≡ a2)
                          → {b1 b2 : B}
                          → (b1 ≡ b2) ≃ (b1 ≡ b2 [ (\ _ → B) ↓ p ])
PathOver-constant-equiv p = improve (Isomorphism (PathOver-constant p)
                                    (Inverse (PathOver-constant-inverse p)
                                             (PathOver-constant-inverse-cancel1 p)
                                             (PathOver-constant-inverse-cancel2 p)))

ap-apd-constant : {l1 l2 : Level} {A : Type l1} {B : Type l2}
                → {a1 a2 : A}
                → (p : a1 ≡ a2)
                → (f : A → B)
                → ap f p ≡ PathOver-constant-inverse p (apd f p)
ap-apd-constant (refl _) f = refl _
```

```agda
module _ {n : ℕ} where

  Wedge-S1-rec : {l : Level}
               → {A : Type l}
               → (a : A)
               → ((k : Fin n) → a ≡ a)
               → Wedge-S1 n → A
  Wedge-S1-rec {A = A} a p =
    Wedge-S1-elim
      (λ _ → A)
      (a)
      (λ k → PathOver-constant (loop k) (p k))

  Wedge-S1-rec-loop : {l : Level}
                    → {A : Type l}
                    → {a : A}
                    → {p : (k : Fin n) → a ≡ a}
                    → (k : Fin n) → ap (Wedge-S1-rec a p) (loop k) ≡ p k
  Wedge-S1-rec-loop {A = A} {a} {p} k =
    ap (Wedge-S1-rec a p) (loop k)                                       ≡⟨ ap-apd-constant (loop k) (Wedge-S1-rec a p) ⟩
    PathOver-constant-inverse (loop k) (apd (Wedge-S1-rec a p) (loop k)) ≡⟨ ap (PathOver-constant-inverse (loop k))
                                                                                 (Wedge-S1-elim-loop k) ⟩
    PathOver-constant-inverse (loop k) (PathOver-constant (loop k) (p k))  ≡⟨ PathOver-constant-inverse-cancel1 (loop k) (p k) ⟩
    p k                                                                    ∎
```

We will now calculate the loop space of the wedge of circles

```agda
concat-equiv : ∀ {A : Type} (a : A) {a' a'' : A}
                     → (p : a' ≡ a'')
                     → (a ≡ a') ≃ (a ≡ a'')
concat-equiv a p =
  improve
    (Isomorphism (_∙ p)
    (Inverse
      (_∙ ! p)
      (λ q → ! (∙assoc q p (! p)) ∙ ap (q ∙_) (!-inv-r p))
      (λ q → ! (∙assoc q (! p) p) ∙ ap (q ∙_) (!-inv-l p))))

transport-∙ : {l1 l2 : Level} {A : Type l1} {B : A → Type l2}
            → {a1 a2 a3 : A} (p : a1 ≡ a2) (q : a2 ≡ a3)
            → transport B (p ∙ q) ∼ transport B q ∘ transport B p
transport-∙ (refl _) (refl _) _ = refl _
```

We assume we have the free group on k generators

```agda
module AssumeFreeGroup (n : ℕ)
  (FreeGroup : Type)
  (one : FreeGroup)
  (mult : (k : Fin n) → FreeGroup ≃ FreeGroup)
  (FreeGroup-rec : {A : Type}
                 → (a : A)
                 → ((k : Fin n) → A ≃ A)
                 → FreeGroup → A)
  (FreeGroup-rec-one : {A : Type}
                     → {a : A}
                     → {p : (k : Fin n) → A ≃ A}
                     → FreeGroup-rec a p one ≡ a)
  (FreeGroup-rec-mult : {A : Type}
                      → {a : A}
                      → {p : (k : Fin n) → A ≃ A}
                      → (k : Fin n) → FreeGroup-rec a p ∘ fwd (mult k) ∼ fwd (p k) ∘ FreeGroup-rec a p)
  (FreeGroup-rec-unique : {A : Type}
                        → {a : A}
                        → {p : (k : Fin n) → A ≃ A}
                        → (f : FreeGroup → A)
                        → f one ≡ a
                        → ((k : Fin n) → f ∘ fwd (mult k) ∼ fwd (p k) ∘ f)
                        → f ∼ FreeGroup-rec a p)
  (FreeGroup-is-set : is-set FreeGroup) where

  Cover : Wedge-S1 n → Type
  Cover = Wedge-S1-rec FreeGroup (λ k → ua (mult k))

  encode : (x : Wedge-S1 n) → base ≡ x → Cover x
  encode x p = transport Cover p one

  decode-base : FreeGroup → base ≡ base [ Wedge-S1 n ]
  decode-base = FreeGroup-rec (refl base) (λ k → concat-equiv base (loop k))

  transport-Cover-loop : (k : Fin n) (x : FreeGroup) → transport Cover (loop k) x ≡ fwd (mult k) x
  transport-Cover-loop k x =
    transport Cover (loop k) x                ≡⟨ transport-ap-assoc Cover (loop k) ⟩
    transport (λ X → X) (ap Cover (loop k)) x ≡⟨ ap (λ P → transport (λ X → X) P x) (Wedge-S1-rec-loop k) ⟩
    transport (λ X → X) (ua (mult k)) x       ≡⟨ uaβ (mult k) ⟩
    fwd (mult k) x                            ∎

  decode-loop : (k : Fin n) → decode-base ≡ decode-base [ (λ x → Cover x → base ≡ x) ↓ loop k ]
  decode-loop k = PathOver-→ (λ x → PathOver-path-to (decode-loop-lma x)) where

    decode-loop-lma : (x : FreeGroup) → decode-base x ∙ loop k ≡ decode-base (transport (λ z → Cover z) (loop k) x)
    decode-loop-lma x =
      decode-base x ∙ loop k                           ≡⟨ refl _ ⟩
      fwd (concat-equiv base (loop k)) (decode-base x) ≡⟨ ! (FreeGroup-rec-mult k x) ⟩
      decode-base (fwd (mult k) x)                     ≡⟨ ap decode-base (! (transport-Cover-loop k x)) ⟩
      decode-base (transport Cover (loop k) x)         ∎

  decode : (x : Wedge-S1 n) → Cover x → base ≡ x
  decode =
    Wedge-S1-elim
      (λ x → Cover x → base ≡ x)
      decode-base
      decode-loop

  encode-decode : (x : Wedge-S1 n) (p : base ≡ x) → decode x (encode x p) ≡ p
  encode-decode .base (refl base) =
    decode base (encode base (refl base)) ≡⟨ refl _ ⟩
    decode base one                       ≡⟨ FreeGroup-rec-one ⟩
    refl base                             ∎

  endo-FreeGroup-is-id : (f : FreeGroup → FreeGroup)
                       → f one ≡ one
                       → ((k : Fin n) → f ∘ fwd (mult k) ∼ fwd (mult k) ∘ f)
                       → f ∼ id
  endo-FreeGroup-is-id f fone=one f∘mult∼mult∘f x =
    f x                      ≡⟨ FreeGroup-rec-unique f fone=one f∘mult∼mult∘f x ⟩
    FreeGroup-rec one mult x ≡⟨ ! (FreeGroup-rec-unique id (refl one) (λ k x' → refl _) x) ⟩
    x                        ∎

  decode-encode-base : (p : FreeGroup) → encode base (decode base p) ≡ p
  decode-encode-base =
    endo-FreeGroup-is-id
      (encode base ∘ decode base)
      decode-encode-base-one
      decode-encode-base-mult where

    decode-encode-base-one : encode base (decode base one) ≡ one
    decode-encode-base-one =
      encode base (decode base one) ≡⟨ ap (encode base) FreeGroup-rec-one ⟩
      encode base (refl base)       ≡⟨ refl _ ⟩
      one                           ∎

    decode-encode-base-mult : (k : Fin n) (x : FreeGroup)
                            → encode base (decode base (fwd (mult k) x))
                            ≡ fwd (mult k) (encode base (decode base x))
    decode-encode-base-mult k x =
      encode base (decode base (fwd (mult k) x))                     ≡⟨ ap (encode base) (FreeGroup-rec-mult k x) ⟩
      encode base (fwd (concat-equiv base (loop k)) (decode base x)) ≡⟨ refl _ ⟩
      encode base (decode base x ∙ loop k)                           ≡⟨ refl _ ⟩
      transport Cover (decode base x ∙ loop k) one                   ≡⟨ transport-∙ (decode base x) (loop k) one ⟩
      transport Cover (loop k) (transport Cover (decode base x) one) ≡⟨ refl _ ⟩
      transport Cover (loop k) (encode base (decode base x))         ≡⟨ transport-Cover-loop k (encode base (decode base x)) ⟩
      fwd (mult k) (encode base (decode base x))                     ∎

  decode-encode-loop : (k : Fin n)
                     → decode-encode-base ≡ decode-encode-base [ (λ x → (p : Cover x) → encode x (decode x p) ≡ p) ↓ loop k ]
  decode-encode-loop k = PathOver-Π (λ q → fwd (transport-to-pathover _ _ _ _) (FreeGroup-is-set _ _ _ _))

  decode-encode : (x : Wedge-S1 n) (p : Cover x) → encode x (decode x p) ≡ p
  decode-encode =
    Wedge-S1-elim
      (λ x → (p : Cover x) → encode x (decode x p) ≡ p)
      decode-encode-base
      decode-encode-loop

  ΩWedge-S1≃FreeGroup : (base ≡ base [ Wedge-S1 n ]) ≃ FreeGroup
  ΩWedge-S1≃FreeGroup = improve (Isomorphism (encode base) (Inverse (decode base) (encode-decode base) (decode-encode base)))
```

