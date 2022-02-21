{-
This file is a variation on the library HoTT-Agda,
written by Leclerc L.
-}

{-# OPTIONS --without-K --warning ignore #-}

open import lib.Base
open import lib.Equivalence
open import lib.Equivalence2
open import lib.Function
open import lib.Funext
open import lib.Homogeneous
open import lib.NType
open import lib.NType2
open import lib.NConnected
open import lib.PathFunctor
open import lib.PathGroupoid
open import lib.PathOver
open import lib.PathSeq
open import lib.types.Nat
open import lib.types.TLevel
open import lib.types.Pointed
open import lib.types.LoopSpace
open import lib.types.Paths
open import lib.types.Pi
open import lib.types.Truncation
open import lib.types.Sigma

module lib.EM-spaces where

{- First, a result about Ω being an equivalence under
  suitable assumptions -}

-- Let (A , a) and (B , b) be two pointed types,
-- such that A is a n-type n-1-connected,
-- and B is a n-type with n > 1.
-- Then the looping map
--   Ω : (⊙[ A , a ] ⊙→ ⊙[ B , b ]) 
--     → (⊙Ω ⊙[ A , a ] → ⊙Ω ⊙[ B , b ])
-- is an equivalence.

private
  fold : ∀ {i j} {A : Type i} {B : Type j} {a : A} {x : A} 
    → (x == a)
    → {b y : B}
    → (h : x == a → y == b)
    → ⊙Ω ⊙[ A , a ] ⊙→ ⊙Ω ⊙[ B , b ]
  fold idp h =
    (λ ω → ! (h idp) ∙ h ω) ,
    !-inv-l (h idp)

module Ω-fiber {i j} {A : Type i} {B : Type j} 
  (a : A) (f : A → B)
  where

  ⊙A = ⊙[ A , a ]
  ⊙ΩA = ⊙Ω ⊙A
  ΩA = Ω ⊙A

  -- two definitions in order to
  -- shorten future statement

  D : {b : B} (⊙g : ⊙ΩA ⊙→ ⊙Ω ⊙[ B , b ]) → Type (lmax i j)
  D {b = b} ⊙g =
      (x : A)
    → Σ (x == a → f x == b) λ h 
    → (α : x == a)
    → (fold α h) == ⊙g

  -- We now define a map induced on paths
  -- from a pointed map ⊙[ A , a ] ⊙→ ⊙[ B , b ] and
  -- we show lemmas about it

  push : {b : B} {{f₀ : f a == b}} {x : A} → x == a → f x == b
  push {{f₀}} α = ap f α ∙' f₀

  fold-is-⊙Ωf : {b : B} {{f₀ : f a == b}}
    {x : A} (α : x == a)
    → fold α push == ⊙Ω-fmap (f , f₀)
  fold-is-⊙Ωf {{idp}} idp = idp

  fiber-lemma : {b : B} {{f₀ : f a == b}}
    → D (⊙Ω-fmap (f , f₀))
  fiber-lemma {b} {{f₀ = p}} x = 
    push , fold-is-⊙Ωf

  -- given a data of the previous form,
  -- we can reconstruct a pointed map
  -- ⊙[ A , a ] ⊙→ ⊙[ B , b ]

  module recover-pointed-map 
    {b : B} {⊙g : ⊙ΩA ⊙→ ⊙Ω ⊙[ B , b ]}
    (H : D ⊙g) 
    where

    private 
      g = fst ⊙g
      g₀ = snd ⊙g
      ⊙B = ⊙[ B , b ]
  
    f₀ : f a == b
    f₀ = fst (H a) idp

    ⊙f : ⊙A ⊙→ ⊙B
    ⊙f = f , f₀

    ⊙Ωf = ⊙Ω-fmap ⊙f
    Ωf = Ω-fmap ⊙f

    push-is-h : {x : A} (α : x == a)
      → push {{f₀}} α == fst (H x) α
    push-is-h idp = ∙'=∙ idp _

    in-fiber-⊙f : ⊙Ω-fmap ⊙f == ⊙g
    in-fiber-⊙f =
      -- ⊙Ω-fmap ⊙f
        ! (fold-is-⊙Ωf {{f₀}} idp)
      -- fold idp (push {{f₀}})
        ∙ ap (fold idp) (λ= push-is-h)
      -- fold idp (fst (H a))
        ∙ snd (H a) idp
      -- ⊙g =∎

  -- now we show that given f : A → B, 
  -- a : A, b : B and ⊙g : ⊙ΩA → ⊙ΩB,
  -- the two constructions defined
  -- above form an equivalence between
  --  [ Σ (f₀ : f a == b) 
  --      (⊙Ω-fmap (f , f₀) == ⊙g) ]
  -- and [ D ⊙g ].

  module Ω-fiber-equiv {b : B} 
    (⊙g : ⊙ΩA ⊙→ ⊙Ω ⊙[ B , b ])
    where

    F : Type (lmax i j)
    F = Σ (f a == b) λ f₀
        → (⊙Ω-fmap (f , f₀) == ⊙g)

    private
      ⊙B = ⊙[ B , b ]
      ⊙ΩB = ⊙Ω ⊙B
      ΩB = Ω ⊙B
      g = fst ⊙g
      g₀ = snd ⊙g

    to : F → D ⊙g
    to φ x =
      push {{f₀}} , 
      λ α → fold-is-⊙Ωf {{f₀}} α ∙ (snd φ)
      where f₀ = fst φ

    from : D ⊙g → F
    from ψ = f₀ , in-fiber-⊙f
      where open recover-pointed-map ψ

    to-from : (ψ : D ⊙g) → to (from ψ) == ψ
    to-from ψ =
      to (f₀ , in-fiber-⊙f)
        =⟨ idp ⟩
      (λ x → 
      ( push {{f₀}} 
      , λ α → fold-is-⊙Ωf {{f₀}} α 
            ∙ (in-fiber-⊙f)
      )) :> D ⊙g
        =⟨ λ= (λ x → pair= (eq-push-ψ x) (path-over x)) ⟩
      (λ x → fst (ψ x) , snd (ψ x))
        =⟨ idp ⟩
      ψ
        =∎
      where private

        open recover-pointed-map ψ

        eq-push-ψ : (x : A) → push {{f₀}} == fst (ψ x)
        eq-push-ψ x = λ= (λ α → push-is-h α)
        
        path-over : (x : A) → PathOver 
          (λ h → (α : x == a) → fold α h == ⊙g) 
          (eq-push-ψ x)
          (λ α → fold-is-⊙Ωf {{f₀}} α ∙ in-fiber-⊙f) (snd (ψ x))
        path-over x = ↓-Π-cst-app-in 
          λ α → ↓-app=cst-in (eq α)
            where
              eq : {x : A} (α : x == a) →
                fold-is-⊙Ωf {{f₀}} α ∙ in-fiber-⊙f ==
                ap (fold α) (λ= push-is-h) ∙ snd (ψ x) α
              eq idp =
                (fold-is-⊙Ωf {{f₀}} idp) ∙ in-fiber-⊙f
                  =⟨ ! (∙-assoc (fold-is-⊙Ωf {{f₀}} idp) _ _) ⟩
                ((fold-is-⊙Ωf {{f₀}} idp)
                  ∙ (! (fold-is-⊙Ωf {{f₀}} idp)))
                ∙ (ap (fold idp) (λ= push-is-h)) 
                ∙ (snd (ψ a) idp)
                  =⟨ ap (λ γ → γ ∙ (ap (fold idp) (λ= push-is-h)) ∙ (snd (ψ a) idp)) 
                    (!-inv-r (fold-is-⊙Ωf {{f₀}} idp)) ⟩
                (ap (fold idp) (λ= push-is-h)) 
                ∙ (snd (ψ a) idp)
                  =∎
    
    from-to : (φ : F) → from (to φ) == φ
    from-to φ =
      (f₀ , in-fiber-⊙f)
        =⟨ idp ⟩
      (fst ((to φ) a) idp) ,
      ! (fold-is-⊙Ωf {{f₀}} idp)
      ∙ (ap (fold idp) (λ= push-is-h))
      ∙ (snd ((to φ) a) idp)
        =⟨ idp ⟩
      idp ∙' fst φ ,
      ! (fold-is-⊙Ωf {{f₀}} idp)
      ∙ (ap (fold idp) (λ= push-is-h))
      ∙ (fold-is-⊙Ωf {{fst φ}} idp)
      ∙ (snd φ)
        =⟨ pair= (∙'-unit-l (fst φ)) path-over ⟩
      φ
        =∎
      where private

        eq : {b' : B} (f₀' : f a == b')
          {⊙g' : ⊙ΩA ⊙→ ⊙Ω ⊙[ B , b' ]}
          (in-fib : ⊙Ω-fmap (f , f₀') == ⊙g')
          → recover-pointed-map.in-fiber-⊙f 
            (λ x → push {{f₀'}} , λ α → fold-is-⊙Ωf {{f₀'}} α ∙ in-fib) 
            == ap (λ z → ⊙Ω-fmap (f , z)) 
            (∙'-unit-l f₀') ∙ in-fib
        eq idp idp = ((∙-unit-r _) 
          ∙ eq') 
          ∙ (∙-unit-r _)
          where
            eq'' : {x : A} (α : x == a) → 
              (recover-pointed-map.push-is-h
              (λ x → ap f , (λ β → fold-is-⊙Ωf {{idp}} β ∙ idp)) α)
              == idp
            eq'' idp = idp

            eq' : ap (fold idp)
              (λ= (recover-pointed-map.push-is-h
              (λ x → ap f , (λ α → fold-is-⊙Ωf {{idp}} α ∙ idp))))
              == idp
            eq' = ap (ap (fold idp)) (ap λ= (λ= λ α → eq'' α) ∙ ! (λ=-η idp))

        open recover-pointed-map (to φ)

        path-over : PathOver 
          (λ f₁ → ⊙Ω-fmap (f , f₁) == ⊙g) 
          (∙'-unit-l (fst φ))
          in-fiber-⊙f 
          (snd φ)
        path-over = ↓-app=cst-in (eq (fst φ) (snd φ))

    FD-equiv : F ≃ D ⊙g
    FD-equiv = equiv to from to-from from-to

module is-contr-Ω-fiber 
  {i} {A : Type i} {a : A} 
  {j} {B : Type j} {b : B}
  {n} (0<n : 0 < n)
  (lA : has-level ⟨ 1 + n ⟩ A)
  (cA : is ⟨ n ⟩ connected A)
  (lB : has-level ⟨ n *2 ⟩ B)
  (⊙g : ⊙Ω ⊙[ A , a ] ⊙→ ⊙Ω ⊙[ B , b ])
  where

  private
    ⊙A = ⊙[ A , a ]
    ⊙B = ⊙[ B , b ]
    g = fst ⊙g
    g₀ = snd ⊙g

  C : (x : A) → Type (lmax i j)
  C x = 
      Σ B λ y
    → Σ (x == a → y == b) λ h
    → Π (x == a) λ α
    → fold α h == ⊙g

  reformulating-Ω-fiber :
    (hfiber ⊙Ω-fmap ⊙g) ≃ Π A C
  reformulating-Ω-fiber = 
    Σ (Σ (A → B) (λ f → f a == b))
       (λ ⊙f → ⊙Ω-fmap ⊙f == ⊙g)
      ≃⟨ Σ-assoc ⟩
    ( Σ (A → B) λ f 
    → Σ (f a == b) λ f₀ 
    → ⊙Ω-fmap (f , f₀) == ⊙g )
      ≃⟨ Σ-emap-r (λ f → Ω-fiber.Ω-fiber-equiv.FD-equiv a f ⊙g) ⟩
    ( Σ (A → B) λ f
    → Π A λ x
    → Σ (x == a → f x == b) λ h
    → Π (x == a) λ α
    → fold α h == ⊙g )
      ≃⟨ choice ⁻¹ ⟩
    Π A C
      ≃∎

  !-inv-l-nulhomotop-inversion : ∀ {i}
    → {X : Type i} {x y : X} (α : y == x)
    → (ω : x == x) (H : ω == idp)
    → Σ (y == x) λ p
    → Σ (! p ∙ p == ω) λ eq
    → PathOver (_== idp) eq (!-inv-l p) H
  !-inv-l-nulhomotop-inversion 
    {x = x} {y = .x} idp idp idp = 
      idp , idp , idp

  simplify-C : {x : A} (α₀ : x == a) 
    → C x ≃ 
    ( Σ B λ y
    → Σ (x == a → y == b) λ h
    → fold α₀ h == ⊙g )
  simplify-C α₀ = Σ-emap-r λ y
    → Σ-emap-r λ h
    → (_ ,
      lemma-1-0-2 _
        (λ α → fold α h == ⊙g) α₀ 
        ⟨ n ⟩₋₂ (snd cA _ a)
        (λ α → has-level-apply (
          lemma-1-0-3 _ _ _ _ _ _ 
          (snd cA a a) λ _ → has-level-apply 
            (transport (λ m → has-level m B) (computation n) lB) 
            b b
        ) 
        (fold α h) ⊙g))
    where private
      computation : (k : ℕ) → ⟨ k *2 ⟩ == (S (S (⟨ k ⟩₋₂ +2+ ⟨ k ⟩₋₂)))
      computation 0 = idp
      computation (S k) = 
        ⟨ S (S (k *2)) ⟩
          =⟨ idp ⟩
        S (S ⟨ k *2 ⟩)
          =⟨ ap (λ q → S (S q)) (computation k) ⟩
        S (S (S (S (⟨ k ⟩₋₂ +2+ ⟨ k ⟩₋₂))))
          =⟨ idp ⟩
        S (S (S (S ⟨ k ⟩₋₂ +2+ ⟨ k ⟩₋₂)))
          =⟨ ap (λ q → S (S (S q))) (+2+-comm (S ⟨ k ⟩₋₂) ⟨ k ⟩₋₂) ⟩
        S (S (S (⟨ k ⟩₋₂ +2+ S ⟨ k ⟩₋₂)))
          =⟨ idp ⟩
        (S (S (⟨ S k ⟩₋₂ +2+ ⟨ S k ⟩₋₂)))
          =∎

  Cxy-pathto-equivalence : (x : A) (α : x == a) (y : B)
      (⊙g' : ⊙Ω ⊙A ⊙→ ⊙Ω ⊙B)
    → ( Σ (x == a → y == b) λ h
      → (fold α h == ⊙g' ) ) 
    ≃ ( y == b )
  Cxy-pathto-equivalence x α y ⊙g' = to α y ⊙g' , 
    contr-map-is-equiv λ β → is-contr-to-hfiber α y ⊙g' β
    where
      to : {x : A} (α : x == a) (y : B) (⊙g' : ⊙Ω ⊙A ⊙→ ⊙Ω ⊙B)
        → ( Σ (x == a → y == b) λ h
            → (fold α h == ⊙g' ) ) 
        → ( y == b )
      to α y _ = λ{ (h , _) → h α }

      is-contr-to-hfiber : {x : A} (α : x == a) (y : B) 
        (⊙g' : ⊙Ω ⊙A ⊙→ ⊙Ω ⊙B) (β : y == b)
        → is-contr (hfiber (to α y ⊙g') β)
      is-contr-to-hfiber idp .b ⊙g' idp = 
        has-level-in (((g' , lemma-1-0-4-2 (is-homogeneous-Ω ⊙B) idp idp (λ ω → ! (g' idp) ∙ (g' ω)) g' (λ= λ ω → ap (λ p → ! p ∙ g' ω) g₀') (!-inv-l (g' idp)) g₀') , g₀') 
        , λ{ ((h , foldh=⊙g') , eq) → {!   !} })
          where private
            g' = fst ⊙g'
            g₀' = snd ⊙g'

      -- private
      --   lemma : {x : B} (ω : x == x) (H : ω == idp)
      --     → !-inv-l ω ==
      --       ap (λ p → ! p ∙ ω) H ∙ H
      --   lemma .idp idp = idp

      -- from : {x : A} (α : x == a) {y : B} (⊙g' : ⊙Ω ⊙A ⊙→ ⊙Ω ⊙B)
      --   → (y == b) 
      --   → ( Σ (x == a → y == b) λ h
      --      → (fold α h == ⊙g' ) )
      -- from idp ⊙g' idp = 
      --   g' , ⊙λ=
      --     ((λ ω → ap (λ p → ! p ∙ g' ω) g₀') 
      --     , ↓-idf=cst-in (lemma (g' idp) g₀'))
      --   where 
      --     g' = fst ⊙g'
      --     g₀' = snd ⊙g'

      -- from-to : {x : A} {α : x == a} {y : B}
      --   → (h : x == a → y == b) 
      --   → (⊙g' : ⊙Ω ⊙A ⊙→ ⊙Ω ⊙B)
      --   → (eq : fold α h == ⊙g')
      --   → from α ⊙g' (to α y ⊙g' (h , eq)) == (h , eq)
      -- from-to {α = idp} h .(fold idp h) idp =
      --   from idp (fold idp h) (to idp _ (fold idp h) (h , idp))
      --     =⟨ idp ⟩
      --   from idp (fold idp h) (h idp)
      --     =⟨ pair= (λ= λ ω → {!   !}) {!   !} ⟩
      --   {!   !}
      --     =⟨ {!   !} ⟩
      --   h , idp
      --     =∎
      --   where
      --     from-idp-β : {y : B}
      --       → (β : y == b)
      --       → (h : a == a → y == b)
      --       → from idp (fold idp h) β == h , idp
      --     from-idp-β idp h =
      --       from idp (fold idp h) idp
      --         =⟨ idp ⟩
      --       fst (fold idp h) , _
      --         =⟨ {!   !} ⟩
      --       {!   !}
      --         =⟨ {!   !} ⟩
      --       h , idp
      --         =∎
      
      -- to-from : {x : A} (α : x == a) (⊙g' : ⊙Ω ⊙A ⊙→ ⊙Ω ⊙B)
      --   {y : B} (β : y == b) →
      --   to α y ⊙g' (from α ⊙g' β) == β
      -- to-from idp ⊙g' idp = snd ⊙g'

  -- Cay-pathto-equivalence y = (λ{ (f , _) -> f idp }) , 
  --   is-eq _ 
  --     (from y)
  --     (λ{ idp -> g₀ }) 
  --     λ{ (h , eq) → pair= (λ= λ ω → to-from-β y (h idp) ω 
  --       ∙ (ap (h idp ∙_) (! (fst (⊙app= eq) ω)) 
  --       ∙ (! (∙-assoc (h idp) (! (h idp)) (h ω)))) 
  --       ∙ (ap (_∙ h ω) (!-inv-r (h idp)))) 
  --       (↓-app=cst-in {!   !}) }
  --   where private
  --     lemma : {x : B} (ω : x == x) (H : ω == idp)
  --       → !-inv-l ω ==
  --         ap (λ p → ! p ∙ ω) H ∙ H
  --     lemma .idp idp = idp

  --     from : (y : B) → y == b → 
  --       ( Σ (a == a → y == b) λ h
  --         → (fold idp h == ⊙g ))
  --     from y α = ( (λ ω → α ∙ g ω) , 
  --       ⊙λ= ((λ ω → 
  --         ap (λ p → p ∙ α ∙ g ω) (!-∙ α (g idp)) 
  --         ∙ ap (λ p → (! p ∙ ! α) ∙ α ∙ g ω) g₀
  --         ∙ ! (∙-assoc (! α) α (g ω))
  --         ∙ ap (_∙ g ω) (!-inv-l α)) , 
  --       ↓-idf=cst-in {!   !}) )

  --     to-from-β : (y : B) (α : y == b) (ω : a == a)
  --       → fst (from y α) ω == α ∙ g ω
  --     to-from-β .b idp _ = idp

      -- to-from-β' : (y : B) (α : y == b) (ω : a == a)
      --   → snd (from y α) ==
            --  ⊙λ= ((λ ω → ap (λ p → ! p ∙ α ∙ g ω) g₀) , ↓-idf=cst-in ((lemma (g idp) g₀))))

      -- technical_lemma : {y : B} (α : y == b) (ω : a == a)
      --   → snd (from y α) ==
      --     ap (λ z → (λ ω → ! (z idp) ∙ z ω) , !-inv-l (z idp))
      --       (λ=
      --         (λ ω →
      --           to-from-β y α ω ∙
      --           (ap (α ∙_) (! (ap (λ u → u ω) (ap fst eq))) ∙
      --           ! (∙-assoc α (! α) (h ω)))
      --           ∙ ap (_∙ h ω) (!-inv-r α)))
      --         ∙ eq
      -- technical_lemma idp ω = ?
    
  is-contr-C : (x : A) → is-contr (C x)
  is-contr-C x = ∥⋅∥-rec is-contr-is-prop (λ p → transport _ p is-contr-Ca) (fst (snd cA a x))
    where abstract
      private
        lemma : {x : B} (ω : x == x) (H : ω == idp)
          → !-inv-l ω ==
            ap (λ p → ! p ∙ ω) H ∙ H
        lemma .idp idp = idp

      is-contr-Ca : is-contr (C a)
      is-contr-Ca = equiv-preserves-level (simplify-C idp ⁻¹ ∘e (Σ-emap-r (λ y → Cxy-pathto-equivalence a idp y ⊙g ⁻¹)))
        {{ pathto-is-contr b }}

  is-contr-fiber : is-contr (hfiber ⊙Ω-fmap ⊙g)
  is-contr-fiber = equiv-preserves-level (reformulating-Ω-fiber ⁻¹) 
    {{weak-λ= λ x → is-contr-C x}}  