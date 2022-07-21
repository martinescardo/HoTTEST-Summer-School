```agda

{-# OPTIONS --rewriting --without-K  #-}

open import new-prelude

module Devel where

  {-# BUILTIN REWRITE _≡_ #-}

  ∙unit-r : {A : Type} {x y : A} → (p : x ≡ y) → (p ∙ refl _) ≡ p
  ∙unit-r p = refl _

  ∙unit-l : {A : Type} {x y : A} → (p : x ≡ y) → (refl _ ∙ p) ≡ p
  ∙unit-l (refl _) = refl _

  ∙assoc : {A : Type} {x y z w : A} (p : x ≡ y) (q : y ≡ z) (r : z ≡ w)
          → p ∙ (q ∙ r) ≡ (p ∙ q) ∙ r
  ∙assoc p (refl _) (refl _) = (refl _)

  !-inv-l : {A : Type} {x y : A} → (p : x ≡ y) → (! p ∙ p) ≡ refl _
  !-inv-l (refl _) = refl _

  !-inv-r : {A : Type} {x y : A} → (p : x ≡ y) → (p ∙ ! p) ≡ refl _
  !-inv-r (refl _) = refl _

  ap-∙ : {A B : Type} {f : A → B} {x y z : A} (p : x ≡ y) (q : y ≡ z)
       → ap f (p ∙ q) ≡ ap f p ∙ ap f q
  ap-∙ (refl _) (refl _) = refl _

  -- EXERCISE
  !-∙ : {A : Type} {x y z : A} (p : x ≡ y) (q : y ≡ z)
      → ! (p ∙ q) ≡ ! q ∙ ! p
  !-∙ (refl _) (refl _) = refl _

  -- EXERCISE
  ap-! : {A B : Type} {f : A → B} {x y : A} (p : x ≡ y) 
       → ap f (! p) ≡ ! (ap f p)
  ap-! (refl _) = refl _

  -- EXERCISE
  !-invol : {A : Type} {x y : A} → (p : x ≡ y) → (! (! p)) ≡ p
  !-invol (refl _) = refl _

  -- EXERCISE 
  compose-pair≡ : {A B : Type} {x1 x2 x3 : A} {y1 y2 y3 : B}
                (p12 : x1 ≡ x2) (p23 : x2 ≡ x3) (q12 : y1 ≡ y2) (q23 : y2 ≡ y3)
              → (pair≡ p12 q12) ∙ (pair≡ p23 q23) ≡ pair≡ (p12 ∙ p23) (q12 ∙ q23)
  compose-pair≡ (refl _) (refl _) (refl _) (refl _) = refl _

  postulate
    S1 : Type
    base : S1
    loop : base ≡ base
    S1-rec : {l : Level} {X : Type l} (x : X) (p : x ≡ x) → S1 → X
    S1-rec-base : {l : Level} {X : Type l} (x : X) (p : x ≡ x)
                  → S1-rec {l} {X} x p base ≡ x
  {-
    S1-rec-loop : {l : Level} {X : Type l} (x : X) (p : x ≡ x)
                   → ap (S1-rec x p) loop ≡ (S1-rec-base x p) ∙ p ∙ ! (S1-rec-base x p)  
  -}
  
  {-# REWRITE S1-rec-base #-}
  postulate
    S1-rec-loop : {l : Level} {X : Type l} (x : X) (p : x ≡ x)
                  → ap (S1-rec x p) loop ≡ p

  example : loop ∙ ! loop ∙ loop ∙ ! loop  ∙ loop ≡ loop
  example = loop ∙ ! loop ∙ loop ∙ ! loop  ∙ loop  ≡⟨ refl _ ⟩
            (((loop ∙ ! loop) ∙ loop) ∙ ! loop)  ∙ loop  ≡⟨ ap (\ H → H ∙ loop ∙ ! loop ∙ loop) (!-inv-r loop)  ⟩
            refl _ ∙ loop ∙ ! loop ∙ loop  ≡⟨  ap (\ H → H ∙ ! loop ∙ loop) (∙unit-l (loop))  ⟩
            loop ∙ ! loop ∙ loop   ≡⟨  ! (∙assoc _ (! loop) loop)  ⟩
            loop ∙ (! loop ∙ loop)  ≡⟨  ap (\ H → loop ∙ H) (!-inv-l loop)  ⟩
            loop ∙ (refl _)  ≡⟨ refl _  ⟩
            loop ∎  
  
  double : S1 → S1
  double = S1-rec base (loop ∙ loop)

  calculate-double-loop : ap double loop ≡ (loop ∙ loop)
  calculate-double-loop = S1-rec-loop _ _

  calculate-double-2-loops : ap double (loop ∙ loop) ≡ loop ∙ loop ∙ loop ∙ loop
  calculate-double-2-loops = 
    ap double (loop ∙ loop) ≡⟨ ap-∙ loop loop ⟩
    ap double loop ∙ ap double loop ≡⟨ ap₂ (\ p q → p ∙ q) (S1-rec-loop _ _) (S1-rec-loop _ _)  ⟩
    (loop ∙ loop) ∙ (loop ∙ loop) ≡⟨  (∙assoc (loop ∙ loop) loop loop )  ⟩
    ((loop ∙ loop) ∙ loop) ∙ loop ∎

  exercise : ap double (! loop) ≡ ! loop ∙ ! loop
  exercise = ap-! loop ∙ ap ! (S1-rec-loop _ _) ∙ !-∙ loop _

  calculate-double-example : ap double (loop ∙ ! loop ∙ loop ∙ ! loop  ∙ loop)
                             ≡ (loop ∙ loop)
  calculate-double-example =
    ap double (loop ∙ ! loop ∙ loop ∙ ! loop  ∙ loop) ≡⟨ ap (ap double) example  ⟩
    ap double loop ≡⟨ S1-rec-loop _ _  ⟩
    (loop ∙ loop) ∎
    
  postulate
    Circle2 : Type
    north : Circle2
    south : Circle2
    west  : north ≡ south
    east  : north ≡ south
    Circle2-rec : {X : Type} (n : X) (s : X) (w : n ≡ s) (e : n ≡ s)
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
  from = Circle2-rec base base (refl base) loop

  to-from-base : from (to base) ≡ base
  to-from-base = refl _

  to-from-loop : ap from (ap to loop) ≡ loop
  to-from-loop = ap from (ap to loop) ≡⟨ ap (ap from) (S1-rec-loop _ _) ⟩
                 ap from (east ∙ ! west) ≡⟨ ap-∙ east (! west) ⟩
                 ap from east ∙ ap from (! west) ≡⟨ ap₂ _∙_ (Circle2-rec-east _ _ _ _)
                                                            (ap-! west  ∙ ap ! (Circle2-rec-west _ _ _ _)) ⟩
                 loop ∙ ! (refl base) ≡⟨ refl _  ⟩
                 loop ∎

  from-to-north : to (from north) ≡ north
  from-to-north = refl _
  
  from-to-south : to (from south) ≡ south
  from-to-south = west
  
  from-to-west : ap to (ap from west) ∙ from-to-south ≡ west
  from-to-west = ap to (ap from west) ∙ west ≡⟨ ap (\ H → ap to H ∙ west) (Circle2-rec-west _ _ _ _) ⟩
                 ap to (refl base) ∙ west ≡⟨ ∙unit-l west ⟩
                 west ∎ 
  
  from-to-east : ap to (ap from east) ∙ from-to-south ≡ east
  from-to-east = ap to (ap from east) ∙ west ≡⟨ ap (\ H → ap to H ∙ west) (Circle2-rec-east _ _ _ _) ⟩
                 ap to loop ∙ west  ≡⟨ ap (\ H → H ∙ west) (S1-rec-loop _ _) ⟩
                 east ∙ ! west ∙ west   ≡⟨ ! (∙assoc _ (! west) west) ⟩
                 east ∙ (! west ∙ west) ≡⟨ ap (\ H → east ∙ H) (!-inv-l west) ⟩
                 east ∎

  data PathOver {A : Type} (B : A → Type) : {a1 a2 : A} (p : a1 ≡ a2) (b1 : B a1) (b2 : B a2) → Type where
    reflo : {x : A} {y : B x} → PathOver B (refl x) y y 

  syntax PathOver B p b1 b2 = b1 ≡ b2 [ B ↓ p ] 

  postulate
    Circle2-elim : (X : Circle2 → Type)
                   (n : X north)
                   (s : X south)
                   (w : n ≡ s [ X ↓ west ])
                   (e : n ≡ s [ X ↓ east ])
                 → (x : Circle2) → X x
    
    S1-elim : (X : S1 → Type)
              (x : X base)
              (p : x ≡ x [ X ↓ loop ])
            → (x : S1) → X x

    S1-elim-base : (X : S1 → Type)
                   (x : X base)
                   (p : x ≡ x [ X ↓ loop ])
                 → S1-elim X x p base ≡ x

  {-# REWRITE S1-elim-base #-}
  -- FIXME: S1-elim-loop

  path-to-pathover : ∀ {A : Type} {B : A → Type}
                   → {a : A} {x y : B a}
                   → (p : x ≡ y)
                   → x ≡ y [ B ↓ refl a ]
  path-to-pathover (refl _) = reflo

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

  PathOver-path≡ : ∀ {A B : Type} {g : A → B} {f : A → B}
                          {a a' : A} {p : a ≡ a'}
                          {q : (f a) ≡ (g a)}
                          {r : (f a') ≡ (g a')}
                        → q ∙ ap g p ≡ ap f p ∙ r
                        → q ≡ r [ (\ x → (f x) ≡ (g x)) ↓ p ]
  PathOver-path≡ {p = (refl _)} h = path-to-pathover (h ∙ ∙unit-l _)

  to-from : (x : S1) → from (to x) ≡ x
  to-from = S1-elim _
                    to-from-base
                    loop-case where
          loop-case : refl base ≡ refl base [ (λ z → from (to z) ≡ z) ↓ loop ] 
          loop-case = PathOver-roundtrip≡ from to loop (∙unit-l _ ∙ to-from-loop)

  -- FIXME make lemma for the rearrangement stuff 
  from-to : (y : Circle2) → to (from y) ≡ y
  from-to = Circle2-elim _
                         from-to-north
                         from-to-south
                         (PathOver-roundtrip≡ to from west (∙unit-l _ ∙ from-to-west))
                         (PathOver-roundtrip≡ to from east (∙unit-l _ ∙ from-to-east))

  circles-equivalent : S1 ≅ Circle2
  circles-equivalent = Isomorphism to (Inverse from to-from from-to)

                 

  module Torus where 
    postulate
      Torus : Type
      baseT : Torus
      pT : baseT ≡ baseT
      qT : baseT ≡ baseT
      sT : pT ∙ qT ≡ qT ∙ pT
      T-rec : {l : Level} {X : Type l} (x : X) (p : x ≡ x) (q : x ≡ x) (s : p ∙ q ≡ q ∙ p) → Torus → X
      T-rec-base : {l : Level} {X : Type l} (x : X) (p : x ≡ x) (q : x ≡ x) (s : p ∙ q ≡ q ∙ p)
                 → T-rec {l} {X} x p q s baseT ≡ x
      SQUARE : Type
      T-elim : (C : Torus → Type)
               (x : C baseT)
               (p : x ≡ x [ C ↓ pT ])
               (q : x ≡ x [ C ↓ qT ])
               (s : SQUARE)
               → (x : Torus) → C x
      T-elim-base : (C : Torus → Type)
                  (x : C baseT)
                  (p : x ≡ x [ C ↓ pT ])
                  (q : x ≡ x [ C ↓ qT ])
                  (s : SQUARE)
                  → T-elim C x p q s baseT ≡ x

               
    {-# REWRITE T-rec-base #-}
    {-# REWRITE T-elim-base #-}

    postulate
      T-rec-pT : {l : Level} {X : Type l} (x : X) (p : x ≡ x) (q : x ≡ x) (s : p ∙ q ≡ q ∙ p)
                 → ap (T-rec x p q s) pT ≡ p
      T-rec-qT : {l : Level} {X : Type l} (x : X) (p : x ≡ x) (q : x ≡ x) (s : p ∙ q ≡ q ∙ p)
                 → ap (T-rec x p q s) qT ≡ q

    torus-to-circles : Torus → S1 × S1
    torus-to-circles = T-rec (base , base)
                             (pair≡ (refl base) loop )
                             (pair≡ loop (refl base ))
                             (compose-pair≡ (refl _) loop loop (refl _) ∙
                              ap₂ pair≡ (∙unit-l loop) (! (∙unit-l loop)) ∙ 
                              ! (compose-pair≡ loop (refl _) (refl _) loop))

    circles-to-torus : S1 → (S1 → Torus)
    circles-to-torus = S1-rec (S1-rec baseT qT)
                              (λ≡ (S1-elim _
                                           pT
                                           (PathOver-path≡ (ap (\ H → pT ∙ H) (S1-rec-loop _ _) ∙
                                                            sT ∙
                                                            ap (\ H → H ∙ pT) (! (S1-rec-loop _ _))))))


  record is-equiv {A B : Type} (f : A → B) : Set where
    constructor Inverse
    field
      post-inverse    : B → A
      is-post-inverse : post-inverse ∘ f ∼ id
      pre-inverse     : B → A
      is-pre-inverse  : f ∘ pre-inverse ∼ id

  record _≃_ (A B : Type) : Type where
    constructor
      Equivalence
    field
      map : A → B
      is-equivalence : is-equiv map

  fwd : ∀ {A B : Type} → A ≃ B → A → B
  fwd e = _≃_.map e

  improve : ∀ {A B : Type} → A ≅ B → A ≃ B
  improve (Isomorphism f (Inverse g gf fg)) = Equivalence f (Inverse g gf g fg)


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
    (hSetℤ : is-set ℤ)
    where

    loop^ : ℤ → base ≡ base
    loop^ = ℤ-rec (refl _)
                  (improve (Isomorphism (\ p → p ∙ loop)
                                        (Inverse (\ p → p ∙ (! loop))
                                                 (\ p → ! (∙assoc _ loop (! loop)) ∙
                                                        ap (\ H → p ∙ H) (!-inv-r loop) )
                                                 (\ p → ! (∙assoc _ (! loop) loop) ∙
                                                        ap (\ H → p ∙ H) (!-inv-l loop)))))
    
    PathOver-→ : {X : Type}
                 (A : X → Type)
                 (B : X → Type)
                 {x x' : X} (p : x ≡ x')
                 {f1 : A x → B x}
                 {f2 : A x' → B x'}
               → ((a : A x) → f1 a ≡ f2 (transport A p a) [ B ↓ p ])
               → f1 ≡ f2 [ (\ z → A z → B z) ↓ p ]
    PathOver-→ F G p = {!!}
    
    PathOver-path-to : ∀ {A : Type} 
                         {a0 a a' : A} {p : a ≡ a'}
                         {q : a0 ≡ a}
                         {r : a0 ≡ a'}
                        → q ∙ p ≡ r
                        → q ≡ r [ (\ x → a0 ≡ x) ↓ p ]
    PathOver-path-to {p = refl _} {q = refl _} (refl _) = reflo
    
    transport-ap-assoc : {A : Type} (C : A → Type) {a a' : A} (p : a ≡ a') {x : C a}
                       → transport C p x ≡ transport (\ X → X) (ap C p) x
    transport-ap-assoc C (refl _) = refl _
    
    postulate 
      ua  : ∀ {X Y : Type} → X ≃ Y → X ≡ Y
      uaβ : ∀ {X Y : Type} (e : X ≃ Y) {x : X} → transport (\ X → X) (ua e) x ≡ fwd e x


    module Pi1S1 where

      Cover : S1 → Type
      Cover = S1-rec ℤ (ua succℤ)
      
      transport-Cover-loop : (x : ℤ) → transport Cover loop x ≡ fwd succℤ x
      transport-Cover-loop x = transport-ap-assoc Cover loop ∙
                               ap (\ H → transport id H x) (S1-rec-loop _ _) ∙ (uaβ  succℤ)
  
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
                       (PathOver-→ _ _ _ \ a →
                        PathOver-path-to (! (ℤ-rec-succℤ _ _ a) ∙ ! (ap loop^ (transport-Cover-loop _))))
      
      encode-decode : (x : S1) (p : base ≡ x) → decode x (encode x p) ≡ p
      encode-decode .base (refl base) = ℤ-rec-0ℤ _ _
      
      decode-encode : (x : S1) (p : Cover x) → encode x (decode x p) ≡ p
      decode-encode = S1-elim _
                              (\ x → ℤ-rec-unique encode-loop^ 0ℤ succℤ encode-loop^-zero encode-loop^-succ x ∙
                                     ! (ℤ-rec-unique (\ x → x) 0ℤ succℤ (refl _) (\ _ → refl _) x) ) 
                              {!!} where
        encode-loop^ : ℤ → ℤ
        encode-loop^ x = encode base (loop^ x)
  
        encode-loop^-zero : encode-loop^ 0ℤ ≡ 0ℤ
        encode-loop^-zero = ap (\ H → transport Cover H 0ℤ) (ℤ-rec-0ℤ _ _)
      
        encode-loop^-succ : (encode-loop^ ∘ fwd succℤ) ∼ (fwd succℤ ∘ encode-loop^)
        encode-loop^-succ x = ap (\ H → encode base H) (ℤ-rec-succℤ _ _ x) ∙
                             transport-Cover-then-loop (loop^ x) 0ℤ 

    

    module Pi1Torus where
      open Torus

      id≃ : ∀ {A : Type} → A ≃ A
      id≃ = Equivalence ((\ x → x)) (Inverse (\ x → x) (\ _ → refl _) (\ x → x) (\ _ → refl _))

      concat-equiv : ∀ {A : Type} (a : A) {a' a'' : A}
                         → (p : a' ≡ a'')
                         → (a ≡ a') ≃ (a ≡ a'')
      concat-equiv _ (refl _) = id≃ -- might be better to write out the maps... 

      concat-equiv-map : ∀ {A : Type} {a a' a'' : A}
                         → (p : a' ≡ a'')
                         → fwd (concat-equiv a p) ≡ \ q → q ∙ p 
      concat-equiv-map (refl _) = refl _

      _×≃_ : ∀ {A A' B B' : Type}
           → A ≃ A'
           → B ≃ B'
           → (A × B) ≃ (A' × B')
      Equivalence f (Inverse f' f-f' f'' f-f'') ×≃ Equivalence g (Inverse g' g-g' g'' g-g'') = 
        Equivalence (\ (a , b) → f a , g b)
                    (Inverse (\ (a' , b') →  f' a' , g' b' )
                             (\ (a , b) → pair≡ (f-f' a) (g-g' b))
                             (\ (a' , b') →  f'' a' , g'' b' )
                             (\ (a , b) → pair≡ (f-f'' a) (g-g'' b)))

      _→≃cod_ : (A : Type) {B B' : Type}
              → B ≃ B'
              → (A → B) ≃ (A → B')
      A →≃cod Equivalence g (Inverse g' g-g' g'' g-g'') =
        Equivalence (\ f → g ∘ f) (Inverse (\ f' → g' ∘ f' ) (\ f → λ≡ \ x → g-g' _) (\ f' → g'' ∘ f' ) (\ f → λ≡ \ x → g-g'' _))

      Cover : Torus → Type
      Cover = T-rec (ℤ × ℤ)
                    (ua (succℤ ×≃ id≃))
                    (ua (id≃ ×≃ succℤ))
                    {!!}

      encode : (x : Torus) → baseT ≡ x → Cover x
      encode x p = transport Cover p ((0ℤ , 0ℤ))

      transport-Cover-pT : (x y : ℤ) → transport Cover pT ((x , y)) ≡ (fwd succℤ x , y)
      transport-Cover-pT x y = transport-ap-assoc _ pT ∙
                               (ap (\ H → transport (\ X → X) H (x , y)) (T-rec-pT _ _ _ _) ∙
                               uaβ _)

      transport-Cover-qT : (x y : ℤ) → transport Cover qT ((x , y)) ≡ (x , fwd succℤ y)
      transport-Cover-qT x y = transport-ap-assoc _ qT ∙
                               (ap (\ H → transport (\ X → X) H (x , y)) (T-rec-qT _ _ _ _) ∙
                               uaβ _)

      decode-ints : ℤ → ℤ → baseT ≡ baseT
      decode-ints = ℤ-rec (ℤ-rec (refl _) (concat-equiv _ qT))
                          (ℤ →≃cod (concat-equiv _ pT))

      decode-ints-succ1 : (x y : ℤ) → decode-ints (fwd succℤ x) y ≡ decode-ints x y ∙ pT
      decode-ints-succ1 x y = ap (\ H → H y) (ℤ-rec-succℤ _ (ℤ →≃cod (concat-equiv _ pT)) _) ∙
                              (ap (\ H → H (decode-ints x y)) (concat-equiv-map pT))

      decode-ints-succ2 : (x y : ℤ) → decode-ints x (fwd succℤ y) ≡ decode-ints x y ∙ qT
      decode-ints-succ2 x y = {!ℤ-rec-succℤ _ _ _ ∙ ?!}

      decode : (x : Torus) → Cover x → baseT ≡ x
      decode = T-elim _
                      (\ (x , y) → decode-ints x y)
                      (PathOver-→ _ _ _
                        (\ (x , y) → PathOver-path-to
                        (! (decode-ints-succ1 x y) ∙  ! (ap (\ (x , y) → decode-ints x y) (transport-Cover-pT x y))  )))
                      ((PathOver-→ _ _ _
                        (\ (x , y) → PathOver-path-to
                        (! (decode-ints-succ2 x y) ∙  ! (ap (\ (x , y) → decode-ints x y) (transport-Cover-qT x y))  ))))
                      {!!}

      encode-decode : (x : Torus) (p : baseT ≡ x) → decode x (encode x p) ≡ p
      encode-decode .baseT (refl baseT) = ap (\ H → H 0ℤ) (ℤ-rec-0ℤ _ ((ℤ →≃cod (concat-equiv _ pT)))) ∙
                                          (ℤ-rec-0ℤ _ _)

      decode-encode : (x : Torus) (p : Cover x) → encode x (decode x p) ≡ p
      decode-encode = T-elim _
                             {!!}
                             {!HSet!}
                             {!HSet!}
                             {!HSet!}
      
    
    

```
