{-# OPTIONS --rewriting --without-K #-}

open import new-prelude

open import Lecture6-notes
open import Lecture5-notes

module Solutions6-Astra where

private
  variable
    ℓ ℓ₁ ℓ₂ : Level

postulate
  𝑓𝑖𝑔₈ : Type
  𝑝𝑡 : 𝑓𝑖𝑔₈
  𝑙₁ : 𝑝𝑡 ≡ 𝑝𝑡
  𝑙₂ : 𝑝𝑡 ≡ 𝑝𝑡
  𝑓𝑖𝑔₈-elim : (X : 𝑓𝑖𝑔₈ → Type ℓ)
    (x : X 𝑝𝑡) (p : x ≡ x [ X ↓ 𝑙₁ ]) (q : x ≡ x [ X ↓ 𝑙₂ ])
      (x : 𝑓𝑖𝑔₈) → X x
  𝑓𝑖𝑔₈-elim-𝑝𝑡 : (X : 𝑓𝑖𝑔₈ → Type ℓ)
    (x : X 𝑝𝑡) (p : x ≡ x [ X ↓ 𝑙₁ ]) (q : x ≡ x [ X ↓ 𝑙₂ ]) →
      𝑓𝑖𝑔₈-elim X x p q 𝑝𝑡 ≡ x
{-# REWRITE 𝑓𝑖𝑔₈-elim-𝑝𝑡 #-}

postulate
  𝑓𝑖𝑔₈-elim-𝑙₁ : (X : 𝑓𝑖𝑔₈ → Type ℓ)
    (x : X 𝑝𝑡) (p : x ≡ x [ X ↓ 𝑙₁ ]) (q : x ≡ x [ X ↓ 𝑙₂ ]) →
      apd (𝑓𝑖𝑔₈-elim X x p q) 𝑙₁ ≡ p
  𝑓𝑖𝑔₈-elim-𝑙₂ : (X : 𝑓𝑖𝑔₈ → Type ℓ)
    (x : X 𝑝𝑡) (p : x ≡ x [ X ↓ 𝑙₁ ]) (q : x ≡ x [ X ↓ 𝑙₂ ]) →
      apd (𝑓𝑖𝑔₈-elim X x p q) 𝑙₂ ≡ q

Path→PathP : {A : Type ℓ₁} {B : Type ℓ₂} {a₁ a₂ : A} {b₁ b₂ : B}
  (p : a₁ ≡ a₂) → b₁ ≡ b₂ → b₁ ≡ b₂ [ (λ _ → B) ↓ p ]
Path→PathP (refl _) (refl _) = reflo

PathP→Path : {A : Type ℓ₁} {B : Type ℓ₂} {a₁ a₂ : A}
  {b₁ b₂ : B} (p : a₁ ≡ a₂) → b₁ ≡ b₂ [ (λ _ → B) ↓ p ] → b₁ ≡ b₂
PathP→Path (refl _) reflo = refl _

Path-η : {A : Type ℓ₁} {B : Type ℓ₂}
  {a1 a2 : A} {b1 b2 : B} (p : a1 ≡ a2) (q : b1 ≡ b2) →
    PathP→Path p (Path→PathP p q) ≡ q
Path-η (refl _) (refl _) = refl _

ap-apd : {A : Type ℓ₁} {B : Type ℓ₂} {a1 a2 : A}
  (p : a1 ≡ a2) (f : A → B) →
    Path→PathP p (ap f p) ≡ apd f p
ap-apd (refl _) f = refl reflo

𝑓𝑖𝑔₈-rec : {X : Type ℓ} (x : X) (p : x ≡ x [ X ]) (q : x ≡ x [ X ]) →
  𝑓𝑖𝑔₈ → X
𝑓𝑖𝑔₈-rec {X = X} x p q =
  𝑓𝑖𝑔₈-elim (λ _ → X) x (Path→PathP 𝑙₁ p) (Path→PathP 𝑙₂ q)

𝑓𝑖𝑔₈-rec-𝑝𝑡 : {X : Type ℓ} (x : X) (p : x ≡ x [ X ]) (q : x ≡ x [ X ]) →
  𝑓𝑖𝑔₈-rec x p q 𝑝𝑡 ≡ x
𝑓𝑖𝑔₈-rec-𝑝𝑡 _ _ _ = refl _

𝑓𝑖𝑔₈-rec-𝑙₁ : {X : Type ℓ} (x : X) (p : x ≡ x [ X ]) (q : x ≡ x [ X ]) →
  ap (𝑓𝑖𝑔₈-rec x p q) 𝑙₁ ≡ p
𝑓𝑖𝑔₈-rec-𝑙₁ {X = X} x p q =
  ! (Path-η 𝑙₁ (ap (𝑓𝑖𝑔₈-rec x p q) 𝑙₁))
    ∙ ap (PathP→Path 𝑙₁)
      (ap-apd 𝑙₁ (𝑓𝑖𝑔₈-rec x p q)
        ∙ 𝑓𝑖𝑔₈-elim-𝑙₁ (λ _ → X) x (Path→PathP 𝑙₁ p) (Path→PathP 𝑙₂ q))
    ∙ Path-η 𝑙₁ p

𝑓𝑖𝑔₈-rec-𝑙₂ : {X : Type ℓ} (x : X) (p : x ≡ x [ X ]) (q : x ≡ x [ X ]) →
  ap (𝑓𝑖𝑔₈-rec x p q) 𝑙₂ ≡ q
𝑓𝑖𝑔₈-rec-𝑙₂ {X = X} x p q =
  ! (Path-η 𝑙₂ (ap (𝑓𝑖𝑔₈-rec x p q) 𝑙₂))
    ∙ ap (PathP→Path 𝑙₂)
      (ap-apd 𝑙₂ (𝑓𝑖𝑔₈-rec x p q)
        ∙ 𝑓𝑖𝑔₈-elim-𝑙₂ (λ _ → X) x (Path→PathP 𝑙₁ p) (Path→PathP 𝑙₂ q))
    ∙ Path-η 𝑙₂ q

concat-equiv : {A : Type} {x y z : A} →
  y ≡ z → (x ≡ y) ≃ (x ≡ z)
concat-equiv p =
  Equivalence
    (λ q → q ∙ p)
    (Inverse
      (λ q → q ∙ ! p)
      (λ q →
        ! (∙assoc q p (! p)) ∙ ap (q ∙_) (!-inv-r p))
      (λ q → q ∙ ! p)
      (λ q →
        ! (∙assoc q (! p) p) ∙ ap (q ∙_) (!-inv-l p)))

transport-∙ : {A : Type ℓ₁} {B : A → Type ℓ₂}
  {x y z : A} (p : x ≡ y) (q : y ≡ z) →
    transport B (p ∙ q) ∼ transport B q ∘ transport B p
transport-∙ (refl _) (refl _) α = refl α

module AssumeF₂ 
  (F₂ : Type)
  (𝑒 : F₂)
  (𝑠ℎ₁ : F₂ ≃ F₂)
  (𝑠ℎ₂ : F₂ ≃ F₂)
  (F₂-rec : {ℓ : Level} {X : Type ℓ} (x : X) (m1 : X ≃ X) (m2 : X ≃ X) →
    F₂ → X)
  (F₂-rec-𝑒 : {ℓ : Level} {X : Type ℓ} (x : X) (m1 : X ≃ X) (m2 : X ≃ X) →
    F₂-rec x m1 m2 𝑒 ≡ x)
  (F₂-rec-𝑠ℎ₁ : {ℓ : Level} {X : Type ℓ} (x : X) (m1 : X ≃ X) (m2 : X ≃ X)
    (a : F₂) → F₂-rec x m1 m2 (fwd 𝑠ℎ₁ a) ≡ fwd m1 (F₂-rec x m1 m2 a))
  (F₂-rec-𝑠ℎ₂ : {ℓ : Level} {X : Type ℓ} (x : X) (m1 : X ≃ X) (m2 : X ≃ X)
    (a : F₂) → F₂-rec x m1 m2 (fwd 𝑠ℎ₂ a) ≡ fwd m2 (F₂-rec x m1 m2 a))
  (F₂-rec-unique : {ℓ : Level} {X : Type ℓ} (f : F₂ → X) (x : X)
    (m1 : X ≃ X) (m2 : X ≃ X) → f 𝑒 ≡ x →
    ((f ∘ fwd 𝑠ℎ₁) ∼ (fwd m1 ∘ f)) → ((f ∘ fwd 𝑠ℎ₂) ∼ (fwd m2 ∘ f)) →
      (z : F₂) → f z ≡ F₂-rec x m1 m2 z)
  (hSetF : is-set F₂) where
  
  Cover : 𝑓𝑖𝑔₈ → Type
  Cover = 𝑓𝑖𝑔₈-rec F₂ (ua 𝑠ℎ₁) (ua 𝑠ℎ₂)

  encode : {x : 𝑓𝑖𝑔₈} → 𝑝𝑡 ≡ x → Cover x
  encode p = transport Cover p 𝑒

  loopify : F₂ → 𝑝𝑡 ≡ 𝑝𝑡
  loopify = F₂-rec (refl 𝑝𝑡) (concat-equiv 𝑙₁) (concat-equiv 𝑙₂)

  tr-Cover-𝑙₁ : (α : F₂) → transport Cover 𝑙₁ α ≡ fwd 𝑠ℎ₁ α
  tr-Cover-𝑙₁ α =
    transport Cover 𝑙₁ α
      ≡⟨ transport-ap-assoc Cover 𝑙₁ ⟩
    transport (λ X → X) (ap Cover 𝑙₁) α
      ≡⟨ ap (λ ϕ → transport (λ X → X) ϕ α)
        (𝑓𝑖𝑔₈-rec-𝑙₁ F₂ (ua 𝑠ℎ₁) (ua 𝑠ℎ₂)) ⟩
    transport (λ X → X) (ua 𝑠ℎ₁) α
      ≡⟨ uaβ 𝑠ℎ₁ ⟩
    fwd 𝑠ℎ₁ α
      ∎

  tr-Cover-𝑙₂ : (α : F₂) → transport Cover 𝑙₂ α ≡ fwd 𝑠ℎ₂ α
  tr-Cover-𝑙₂ α =
    transport Cover 𝑙₂ α
      ≡⟨ transport-ap-assoc Cover 𝑙₂ ⟩
    transport (λ X → X) (ap Cover 𝑙₂) α
      ≡⟨ ap (λ ϕ → transport (λ X → X) ϕ α)
        (𝑓𝑖𝑔₈-rec-𝑙₂ F₂ (ua 𝑠ℎ₁) (ua 𝑠ℎ₂)) ⟩
    transport (λ X → X) (ua 𝑠ℎ₂) α
      ≡⟨ uaβ 𝑠ℎ₂ ⟩
    fwd 𝑠ℎ₂ α
      ∎

  loopify-𝑙₁ : (α : F₂) →
    loopify (transport Cover 𝑙₁ α) ≡ loopify α ∙ 𝑙₁
  loopify-𝑙₁ α =
    loopify (transport Cover 𝑙₁ α)
      ≡⟨ ap loopify (tr-Cover-𝑙₁ α) ⟩
    loopify (fwd 𝑠ℎ₁ α)
      ≡⟨ F₂-rec-𝑠ℎ₁ (refl 𝑝𝑡) (concat-equiv 𝑙₁) (concat-equiv 𝑙₂) α ⟩
    loopify α ∙ 𝑙₁
      ∎

  loopify-𝑙₂ : (α : F₂) →
    loopify (transport Cover 𝑙₂ α) ≡ loopify α ∙ 𝑙₂
  loopify-𝑙₂ α =
    loopify (transport Cover 𝑙₂ α)
      ≡⟨ ap loopify (tr-Cover-𝑙₂ α) ⟩
    loopify (fwd 𝑠ℎ₂ α)
      ≡⟨ F₂-rec-𝑠ℎ₂ (refl 𝑝𝑡) (concat-equiv 𝑙₁) (concat-equiv 𝑙₂) α ⟩
    loopify α ∙ 𝑙₂
      ∎

  decode : {x : 𝑓𝑖𝑔₈} → Cover x → 𝑝𝑡 ≡ x
  decode {x} =
    𝑓𝑖𝑔₈-elim (λ α → Cover α → 𝑝𝑡 ≡ α)
      loopify
      (PathOver-→ (λ α → PathOver-path-to (! (loopify-𝑙₁ α))))
      (PathOver-→ (λ α → PathOver-path-to (! (loopify-𝑙₂ α))))
      x

  encode-decode : {x : 𝑓𝑖𝑔₈} (p : 𝑝𝑡 ≡ x) → decode (encode p) ≡ p
  encode-decode (refl .𝑝𝑡) =
    F₂-rec-𝑒 (refl 𝑝𝑡) (concat-equiv 𝑙₁) (concat-equiv 𝑙₂)

  𝑠ℎ₁-lem : (α : F₂) →
    encode (loopify (fwd 𝑠ℎ₁ α)) ≡ fwd 𝑠ℎ₁ (encode (loopify α))
  𝑠ℎ₁-lem α =
    encode (loopify (fwd 𝑠ℎ₁ α))
      ≡⟨ ap encode
        (F₂-rec-𝑠ℎ₁ (refl 𝑝𝑡) (concat-equiv 𝑙₁) (concat-equiv 𝑙₂) α) ⟩
    encode (loopify α ∙ 𝑙₁)
      ≡⟨ transport-∙ (loopify α) 𝑙₁ 𝑒 ⟩
    transport Cover 𝑙₁ (transport Cover (loopify α) 𝑒)
      ≡⟨ tr-Cover-𝑙₁ (transport Cover (loopify α) 𝑒) ⟩
    fwd 𝑠ℎ₁ (encode (loopify α))
      ∎

  𝑠ℎ₂-lem : (α : F₂) →
    encode (loopify (fwd 𝑠ℎ₂ α)) ≡ fwd 𝑠ℎ₂ (encode (loopify α))
  𝑠ℎ₂-lem α =
    encode (loopify (fwd 𝑠ℎ₂ α))
      ≡⟨ ap encode
        (F₂-rec-𝑠ℎ₂ (refl 𝑝𝑡) (concat-equiv 𝑙₁) (concat-equiv 𝑙₂) α) ⟩
    encode (loopify α ∙ 𝑙₂)
      ≡⟨ transport-∙ (loopify α) 𝑙₂ 𝑒 ⟩
    transport Cover 𝑙₂ (transport Cover (loopify α) 𝑒)
      ≡⟨ tr-Cover-𝑙₂ (transport Cover (loopify α) 𝑒) ⟩
    fwd 𝑠ℎ₂ (encode (loopify α))
      ∎

  encode-loopify : (α : F₂) → encode (loopify α) ≡ α
  encode-loopify α =
    F₂-rec-unique (encode ∘ loopify) 𝑒 𝑠ℎ₁ 𝑠ℎ₂
      (ap encode (encode-decode (refl 𝑝𝑡))) 𝑠ℎ₁-lem 𝑠ℎ₂-lem α
    ∙ ! (F₂-rec-unique (λ β → β) 𝑒 𝑠ℎ₁ 𝑠ℎ₂
      (refl 𝑒) (λ _ → refl _) (λ _ → refl _) α)

  decode-encode : {x : 𝑓𝑖𝑔₈} (p : Cover x) → encode (decode {x} p) ≡ p
  decode-encode {x} =
    𝑓𝑖𝑔₈-elim (λ x → (p : Cover x) → encode (decode {x} p) ≡ p)
      encode-loopify
      (PathOver-Π (λ {y} {z} q →
        fwd (transport-to-pathover _ _ _ _) (hSetF _ _ _ _)))
      (PathOver-Π (λ {y} {z} q →
        fwd (transport-to-pathover _ _ _ _) (hSetF _ _ _ _)))
      x

