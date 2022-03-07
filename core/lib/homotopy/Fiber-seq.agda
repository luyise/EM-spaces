{-# OPTIONS --without-K --warning ignore #-}

open import lib.Base
open import lib.Equivalence
open import lib.Function
open import lib.Funext
open import lib.NConnected
open import lib.NType
open import lib.NType2
open import lib.PathFunctor
open import lib.PathGroupoid
open import lib.PathOver
open import lib.groups.Homomorphism
open import lib.groups.LoopSpace
open import lib.types.LoopSpace
open import lib.types.Nat
open import lib.types.Paths
open import lib.types.Pi
open import lib.types.Pointed
open import lib.types.TLevel
open import lib.types.Truncation
open import lib.types.Sigma

module lib.homotopy.Fiber-seq where

module exact-seq {i : ULevel}
  (A B C : Type i)
  (a : A) (b : B) (c : C)
  (lA : has-level ⟨ 1 ⟩ A)
  (lB : has-level ⟨ 1 ⟩ B)
  (lC : has-level ⟨ 1 ⟩ C)
  (cA : is ⟨ 0 ⟩ connected A)
  (cB : is ⟨ 0 ⟩ connected B)
  (cC : is ⟨ 0 ⟩ connected C)
  (⊙f : ⊙[ A , a ] ⊙→ ⊙[ B , b ])
  (⊙g : ⊙[ B , b ] ⊙→ ⊙[ C , c ])
  where
  
  private
    ⊙A = ⊙[ A , a ]
    ⊙B = ⊙[ B , b ]
    ⊙C = ⊙[ C , c ]

    instance 
      lA' = lA
      lB' = lB
      lC' = lC

    f = fst ⊙f
    g = fst ⊙g
    gf = g ∘ f
    ⊙gf = ⊙g ⊙∘ ⊙f

    f₀ : f a == b
    f₀ = snd ⊙f
    g₀ : g b == c
    g₀ = snd ⊙g
    gf₀ = snd (⊙gf)

    ⊙ΩA = ⊙Ω ⊙A
    ⊙ΩB = ⊙Ω ⊙B
    ⊙ΩC = ⊙Ω ⊙C
    ΩA = de⊙ ⊙ΩA
    ΩB = de⊙ ⊙ΩB
    ΩC = de⊙ ⊙ΩC
    ΩA-gp = Ω^S-group 0 ⊙A
    ΩB-gp = Ω^S-group 0 ⊙B
    ΩC-gp = Ω^S-group 0 ⊙C

    Ωf = Ω-fmap ⊙f
    Ωg = Ω-fmap ⊙g
    Ωgf = Ω-fmap (⊙g ⊙∘ ⊙f)
    Ωf-β : (ω : ΩA) → Ωf ω == ! f₀ ∙ ap f ω ∙' f₀
    Ωf-β = Ω-fmap-β ⊙f
    Ωg-β : (ω : ΩB) → Ωg ω == ! g₀ ∙ ap g ω ∙' g₀
    Ωg-β = Ω-fmap-β ⊙g
    Ωgf-β : (ω : ΩA) → Ωgf ω == ! gf₀ ∙ ap g (ap f ω) ∙' gf₀
    Ωgf-β ω =
      Ω-fmap (⊙g ⊙∘ ⊙f) ω
        =⟨ Ω-fmap-β ⊙gf ω ⟩
      ! gf₀ ∙ (ap (g ∘ f) ω) ∙' gf₀
        =⟨ ap (λ p → (! gf₀) ∙ p ∙' gf₀) (ap-∘ g f ω) ⟩
      ! gf₀ ∙ ap g (ap f ω) ∙' gf₀
        =∎

    Ωf-gp = Ω^S-group-fmap 0 ⊙f
    Ωg-gp = Ω^S-group-fmap 0 ⊙g

  -- If g ∘ f is constant, then so is the induced map on paths

  module _ 
    (γ : (x : A) → g (f x) == c)
    where

    Ωgf=1 : Ωgf == cst idp
    Ωgf=1 = λ= λ ω →
       Ωgf-β ω 
       ∙ ap (λ p → (! gf₀) ∙ p ∙' gf₀) 
            (lemma ω ∙ (!-inv-r (γ a))) 
       ∙ ap (! gf₀ ∙_) (∙'-unit-l _) 
       ∙ !-inv-l gf₀
      where private
        lemma : {x : A} (α : a == x)
          → ap g (ap f α) == (γ a) ∙ ! (γ x)
        lemma idp = ! (!-inv-r (γ a))

    -- now let's assume that g f form a fibration, which means that
    -- the canonical map from A to the fiber of g over c is
    -- an equivalence.

    fiber = hfiber g c

    canonical-map : A → fiber
    canonical-map x = (f x , γ x)

    is-fibration : Type i
    is-fibration = is-equiv canonical-map

    -- is-fibration : Type (lsucc i)
    -- is-fibration =
    --   (⊙A , ⊙f) 
    --     == 
    --   (( ⊙[ Σ B (λ y → g y == c) , (b , g₀) ] 
    --   , (fst , idp) )
    --     :> Σ (Ptd i) (λ ⊙X → (⊙X ⊙→ ⊙B))
    --   )

  -- then we may show that the group sequence induced on path space is exact

  module _
    (γ : (x : A) → g (f x) == c)
    (is-fib : is-fibration γ)
    where

    -- We first notice that pushing any path from x₀ to x₁ in X by g∘f
    -- gives the path γ x₀ ∙ ! (γ x₁).

    
