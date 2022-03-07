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
    Ωgf-is-Ωg∘Ωf : Ωgf == Ωg ∘ Ωf
    Ωgf-is-Ωg∘Ωf = ap fst (⊙Ω-fmap-∘ ⊙g ⊙f)
    Ωgf~Ωg∘Ωf : Ωgf ~ Ωg ∘ Ωf
    Ωgf~Ωg∘Ωf = app= Ωgf-is-Ωg∘Ωf

    Ωf-gp = Ω^S-group-fmap 0 ⊙f
    Ωg-gp = Ω^S-group-fmap 0 ⊙g

  -- If g ∘ f is constant, then so is the induced map on paths

  module _ 
    (γ : (x : A) → g (f x) == c)
    where

    Ωgf~1 : Ωgf ~ cst idp
    Ωgf~1 ω =
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

  -- then we may show that the group sequence induced on path space is left-exact

  module _
    (γ : (x : A) → g (f x) == c)
    (is-fib : is-fibration γ)
    where

    -- first we get a fibration sequence on loop spaces :

    private
      Γ : (α : ΩA) → (Ωg (Ωf α)) == idp
      Γ α =
        Ωg (Ωf α)
          =⟨ ! (Ωgf~Ωg∘Ωf α) ⟩
        Ωgf α
          =⟨ Ωgf~1 γ α ⟩
        idp
          =∎

      abstract
        π : PathOver (λ x → g x == c) f₀ (γ (pt ⊙A)) (! (ap g f₀) ∙ γ a)
        π = (↓-app=cst-in (ap (_∙ γ a) (! (!-inv-r (ap g f₀))) ∙ (∙-assoc ((ap g f₀)) (! (ap g f₀)) (γ a))))

      ⊙can-map : ⊙A ⊙→ ⊙[ fiber γ , (b , ! (ap g f₀) ∙ γ a) ]
      ⊙can-map = canonical-map γ ,
        pair= f₀ π

      Ωfγ = Ω-fmap ⊙can-map
      is-equiv-Ωfγ : is-equiv Ωfγ
      is-equiv-Ωfγ = Ω-isemap ⊙can-map is-fib

      Ωfγ-β : (α : ΩA) → Ωfγ α == ! (pair= f₀ π) ∙ (ap (λ x → (f x , γ x)) α) ∙' (pair= f₀ π)
      Ωfγ-β = Ω-fmap-β ⊙can-map

      fst=Ωfγ : fst= ∘ Ωfγ ~ Ωf
      fst=Ωfγ α =
        ap fst (Ωfγ α)
          =⟨ ap (ap fst) (Ωfγ-β α) ⟩
        ap fst (! (pair= f₀ π) ∙ (ap (λ x → (f x , γ x)) α) ∙' (pair= f₀ π))
          =⟨ ap-∙ fst (! (pair= f₀ π)) _ ∙ ap (ap fst (! (pair= f₀ π)) ∙_) (ap-∙' fst _ (pair= f₀ π)) ⟩
        ap fst (! (pair= f₀ π))
        ∙ ap fst (ap (λ x → (f x , γ x)) α)
        ∙' ap fst (pair= f₀ π)
          =⟨ ap (λ u → u ∙ ap fst (ap (λ x → (f x , γ x)) α) ∙' ap fst (pair= f₀ π)) (ap-! fst _) ⟩
        ! (ap fst (pair= f₀ π))
        ∙ ap fst (ap (λ x → (f x , γ x)) α)
        ∙' ap fst (pair= f₀ π)
          =⟨ ap (λ u → ! u ∙ ap fst (ap (λ x → (f x , γ x)) α) ∙' u) (fst=-β f₀ π) ⟩
        ! f₀ ∙ ap fst (ap (λ x → (f x , γ x)) α) ∙' f₀
          =⟨ ap (λ u → ! f₀ ∙ u ∙' f₀) (! (ap-∘ fst (λ x → (f x , γ x)) α)) ⟩
        ! f₀ ∙ ap f α ∙' f₀
          =⟨ ! (Ωf-β α) ⟩
        Ωf α
          =∎

    -- So we get that Ωf is injective.

    private
      Ωfγ-inj→Ωf-inj : ∀ {α₀ α₁}
        → (Ωf α₀ == Ωf α₁)
        → (Ωfγ α₀ == Ωfγ α₁)
      Ωfγ-inj→Ωf-inj {α₀} {α₁} ζ = 
        equiv-is-inj (snd ((=Σ-econv (b , ! (ap g f₀) ∙ γ a) (b , ! (ap g f₀) ∙ γ a)) ⁻¹)) 
        _ _ (pair= ( fst=Ωfγ α₀ ∙ ζ ∙ ! (fst=Ωfγ α₁)) 
        (from-transp (λ p → PathOver (λ v → fst ⊙g v == c) p (! (ap g f₀) ∙ γ a) (! (ap g f₀) ∙ γ a)) 
          _ (prop-path (equiv-preserves-level ((to-transp-equiv _ _) ⁻¹) {{has-level-apply (has-level-apply lC _ _) _ _}}) _ _)))

    abstract
      is-inj-Ωf : is-inj Ωf
      is-inj-Ωf α₁ α₂ ζ = 
        equiv-is-inj is-equiv-Ωfγ α₁ α₂ (Ωfγ-inj→Ωf-inj ζ)

    private abstract
      Ωg=1→apg=1 : {β : ΩB}
        → (Ωg β == idp)
        → (ap g β == idp)
      Ωg=1→apg=1 {β} ζ =
        ap g β
          =⟨ ap (ap g β ∙'_) (! (!-inv'-r g₀)) ⟩
        ap g β ∙' (g₀ ∙' ! g₀)
          =⟨ ap (_∙ ap g β ∙' g₀ ∙' ! g₀) (! (!-inv-r g₀)) ⟩
        (g₀ ∙ ! g₀) ∙ ap g β ∙' g₀ ∙' ! g₀
          =⟨ ∙-assoc g₀ (! g₀) (ap g β ∙' g₀ ∙' ! g₀) ⟩
        g₀ ∙ (! g₀ ∙ (ap g β ∙' (g₀ ∙' ! g₀)))
          =⟨ ap (g₀ ∙_) (! (∙∙'-assoc (! g₀) (ap g β) _) ∙ (! (∙'-assoc (! g₀ ∙ ap g β) g₀ (! g₀))))  ⟩
        g₀ ∙ ((! g₀ ∙ ap g β) ∙' g₀) ∙' ! g₀
          =⟨ ap (λ u → g₀ ∙ u ∙' ! g₀) (∙∙'-assoc (! g₀) (ap g β) g₀) ⟩
        g₀ ∙ (! g₀ ∙ ap g β ∙' g₀) ∙' ! g₀
          =⟨ ap (λ u → g₀ ∙ u ∙' ! g₀) (! (Ωg-β β)) ⟩
        g₀ ∙ Ωg β ∙' ! g₀
          =⟨ ap (λ u → g₀ ∙ u ∙' ! g₀) ζ ⟩
        g₀ ∙ idp ∙' ! g₀
          =⟨ ap (g₀ ∙_) (∙'-unit-l (! g₀)) ⟩
        g₀ ∙ ! g₀
          =⟨ !-inv-r g₀ ⟩
        idp
          =∎

    private
      ker-g-to-ΩΣ : (β : ΩB) → (Ωg β == idp)
        → Ω (⊙[ fiber γ , (b , ! (ap g f₀) ∙ γ a) ])
      ker-g-to-ΩΣ β ζ = pair= β
        (↓-app=cst-in (ap (_∙ ! (ap g f₀) ∙ γ a) (! (Ωg=1→apg=1 ζ))))

    abstract
      ker-g-to-im-f : (β : ΩB) → (Ωg β == idp)
        → Σ ΩA λ α → Ωf α == β
      ker-g-to-im-f β ζ = <– (Ωfγ , is-equiv-Ωfγ) (ker-g-to-ΩΣ β ζ) , 
        ! (fst=Ωfγ _) ∙ eq
        where private
          eq : (fst= ∘ Ωfγ) (<– (Ωfγ , is-equiv-Ωfγ) (ker-g-to-ΩΣ β ζ)) == β
          eq =
            fst= (Ωfγ ((<– (Ωfγ , is-equiv-Ωfγ)) (ker-g-to-ΩΣ β ζ)))
              =⟨ (ap (λ u → fst= u) (<–-inv-r (_ , is-equiv-Ωfγ) (ker-g-to-ΩΣ β ζ))) ⟩
            fst= (ker-g-to-ΩΣ β ζ)
              =⟨ fst=-β _ _ ⟩
            β
              =∎
 