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
open import lib.types.TLevel
open import lib.types.Truncation
open import lib.types.Sigma
open import lib.groups.Homomorphism
open import lib.groups.LoopSpace

module lib.OmegaEquivO where

{- a result about Ω being an equivalence under
  suitable assumptions, in the case n = O -}

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
    → Ω ⊙[ A , a ] → Ω ⊙[ B , b ]
  fold α h =
    (λ ω → ! (h α) ∙ h (α ∙ ω))

module Ω-fiber {i j} {A : Type i} {B : Type j} 
  (a : A) (f : A → B)
  where

  ⊙A = ⊙[ A , a ]
  ⊙ΩA = ⊙Ω ⊙A
  ΩA = Ω ⊙A

  -- two definitions in order to
  -- shorten future statement

  D : {b : B} (g : ΩA → Ω ⊙[ B , b ]) → Type (lmax i j)
  D {b = b} g =
      (x : A)
    → Σ (x == a → f x == b) λ h 
    → (α : x == a)
    → (fold α h) == g

  -- We now define a map induced on paths
  -- from a pointed map ⊙[ A , a ] ⊙→ ⊙[ B , b ] and
  -- we show lemmas about it

  push : {b : B} {{f₀ : f a == b}} {x : A} → x == a → f x == b
  push {{f₀}} α = ap f α ∙' f₀

  fold-is-Ωf : {b : B} {{f₀ : f a == b}}
    {x : A} (α : x == a)
    → fold α push == Ω-fmap (f , f₀)
  fold-is-Ωf {{idp}} idp = idp

  fiber-lemma : {b : B} {{f₀ : f a == b}}
    → D (Ω-fmap (f , f₀))
  fiber-lemma {b} {{f₀ = p}} x = 
    push , fold-is-Ωf

  -- given a data of the previous form,
  -- we can reconstruct a pointed map
  -- ⊙[ A , a ] ⊙→ ⊙[ B , b ]

  module recover-pointed-map 
    {b : B} 
    (lA : has-level ⟨ 1 ⟩ A)
    (lB : has-level ⟨ 1 ⟩ B)
    {mg : Ω^S-group O (⊙[ A , a ]) {{lA}} →ᴳ Ω^S-group O (⊙[ B , b ]) {{lB}}}
    (H : D (GroupHom.f mg)) 
    where

    private
      ⊙B = ⊙[ B , b ]
      Ω-fmap-gp : ⊙A ⊙→ ⊙B → Ω^S-group O ⊙A {{lA}} →ᴳ Ω^S-group O ⊙B {{lB}}
      Ω-fmap-gp = (Ω^S-group-fmap O {{lA}} {{lB}})
      g = GroupHom.f mg
  
    f₀ : f a == b
    f₀ = fst (H a) idp

    ⊙f : ⊙A ⊙→ ⊙B
    ⊙f = f , f₀

    Ωf = Ω-fmap ⊙f

    push-is-h : {x : A} (α : x == a)
      → push {{f₀}} α == fst (H x) α
    push-is-h idp = ∙'=∙ idp _

    in-fiber-⊙f : Ω-fmap-gp ⊙f == mg
    in-fiber-⊙f = group-hom= 
      (
        ! (fold-is-Ωf {{f₀}} idp) 
        ∙ ap (fold idp) (λ= push-is-h) 
        ∙ snd (H a) idp
      )

  -- now we show that given f : A → B, 
  -- a : A, b : B and mg : ⊙ΩA → ⊙ΩB 
  -- a group morphism,
  -- the two constructions defined
  -- above form an equivalence between
  --  [ Σ (f₀ : f a == b) 
  --      (Ω-fmap-gp (f , f₀) == mg) ]
  -- and [ D g ].

  module Ω-fiber-equiv {b : B} 
    (lA : has-level ⟨ 1 ⟩ A)
    (lB : has-level ⟨ 1 ⟩ B)
    (mg : Ω^S-group O (⊙[ A , a ]) {{lA}} →ᴳ Ω^S-group O (⊙[ B , b ]) {{lB}})
    where

    private
      ⊙B = ⊙[ B , b ]
      ⊙ΩB = ⊙Ω ⊙B
      ΩB = Ω ⊙B
      Ω-fmap-gp : ⊙A ⊙→ ⊙B → Ω^S-group O ⊙A {{lA}} →ᴳ Ω^S-group O ⊙B {{lB}}
      Ω-fmap-gp = (Ω^S-group-fmap O {{lA}} {{lB}})
      g = GroupHom.f mg

    F : Type (lmax i j)
    F = Σ (f a == b) λ f₀
        → (Ω-fmap-gp (f , f₀) == mg)

    to : F → D g
    to φ x =
      push {{f₀}} , 
      λ α → fold-is-Ωf {{f₀}} α ∙ ap GroupHom.f (snd φ)
      where f₀ = fst φ

    from : D g → F
    from ψ = f₀ , in-fiber-⊙f
      where open recover-pointed-map lA lB ψ

    to-from : (ψ : D g) → to (from ψ) == ψ
    to-from ψ =
      to (f₀ , in-fiber-⊙f)
        =⟨ idp ⟩
      (λ x → 
      ( push {{f₀}} 
      , λ α → fold-is-Ωf {{f₀}} α 
            ∙ _
      )) :> D g
        =⟨ λ= (λ x → pair= (eq-push-ψ x) (path-over x)) ⟩
      (λ x → fst (ψ x) , snd (ψ x))
        =⟨ idp ⟩
      ψ
        =∎
      where private

        open recover-pointed-map lA lB ψ

        eq-push-ψ : (x : A) → push {{f₀}} == fst (ψ x)
        eq-push-ψ x = λ= (λ α → push-is-h α)
        
        path-over : (x : A) → 
          PathOver (λ h → (α : x == a) → fold α h == g) (eq-push-ψ x)
            (λ α →
              fold-is-Ωf {{f₀}} α ∙
              ap GroupHom.f (recover-pointed-map.in-fiber-⊙f lA lB ψ))
            (snd (ψ x))
        path-over x = ↓-Π-cst-app-in 
          λ α → ↓-app=cst-in (eq α)
            where
              eq : {x : A} (α : x == a) →
                fold-is-Ωf {{f₀}} α ∙ 
                ap GroupHom.f
                (group-hom= (
                  ! (fold-is-Ωf {{f₀}} idp) 
                  ∙ ap (fold idp) (λ= push-is-h) 
                  ∙ snd (ψ a) idp
                ))
                ==
                ap (fold α) (λ= push-is-h) ∙ snd (ψ x) α
              eq idp =
                (fold-is-Ωf {{f₀}} idp) ∙ _
                  =⟨ ap ((fold-is-Ωf {{f₀}} idp) ∙_) (group-hom=-β _) ⟩
                _
                  =⟨ ! (∙-assoc (fold-is-Ωf {{f₀}} idp) _ _) ⟩
                ((fold-is-Ωf {{f₀}} idp)
                  ∙ (! (fold-is-Ωf {{f₀}} idp)))
                ∙ (ap (fold idp) (λ= push-is-h)) 
                ∙ (snd (ψ a) idp)
                  =⟨ ap (λ γ → γ ∙ (ap (fold idp) (λ= push-is-h)) ∙ (snd (ψ a) idp)) 
                    (!-inv-r (fold-is-Ωf {{f₀}} idp)) ⟩
                (ap (fold idp) (λ= push-is-h)) 
                ∙ (snd (ψ a) idp)
                  =∎
    
    from-to : (φ : F) → from (to φ) == φ
    from-to φ =
      (f₀ , in-fiber-⊙f)
        =⟨ idp ⟩
      idp ∙' fst φ ,
      group-hom= (
        ! (fold-is-Ωf {{f₀}} idp)
        ∙ (ap (fold idp) (λ= push-is-h))
        ∙ (fold-is-Ωf {{fst φ}} idp)
        ∙ (ap GroupHom.f (snd φ))
      )
        =⟨ pair= (∙'-unit-l (fst φ)) (↓-app=cst-in (eq (fst φ) (snd φ))) ⟩
      φ
        =∎
      where

        eq : {b' : B} (f₀' : f a == b')
          {mg' : Ω^S-group O (⊙[ A , a ]) {{lA}} →ᴳ Ω^S-group O (⊙[ B , b' ]) {{lB}}}
          (in-fib : (Ω^S-group-fmap O {{lA}} {{lB}}) (f , f₀') == mg')
          → recover-pointed-map.in-fiber-⊙f lA lB
            (λ x → push {{f₀'}} , λ α → fold-is-Ωf {{f₀'}} α ∙ (ap GroupHom.f in-fib)) 
            == ap (λ z → (Ω^S-group-fmap O {{lA}} {{lB}}) (f , z)) 
            (∙'-unit-l f₀') ∙ in-fib
        eq idp idp =
          (ap group-hom= (∙-unit-r _) 
          ∙ eq')
          ∙ (∙-unit-r _)
          where
            eq' : group-hom= (ap (fold idp)
              (λ= (recover-pointed-map.push-is-h lA lB
              (λ x → ap f , (λ α → fold-is-Ωf {{idp}} α ∙ idp)))))
              == idp
            eq' = prop-path (has-level-apply GroupHom-level _ _) _ _

        open recover-pointed-map lA lB (to φ)

    FD-equiv : F ≃ D g
    FD-equiv = equiv to from to-from from-to

-- We now show that the fiber of Ω is contractible,
-- so it will be an equivalence

{-

module is-contr-Ω-fiber-O 
  {i} {A : Type i} {a : A} 
  {j} {B : Type j} {b : B}
  (cA : is ⟨ O ⟩ connected A)
  (lA : has-level ⟨ 1 ⟩ A)
  (lB : has-level ⟨ 1 ⟩ B)
  (mg : Ω^S-group O (⊙[ A , a ]) {{lA}} →ᴳ Ω^S-group O (⊙[ B , b ]) {{lB}})
  where

  private
    ⊙A = ⊙[ A , a ]
    ⊙B = ⊙[ B , b ]
    ⊙g = GroupHom.⊙f mg
    g = fst ⊙g
    Ω-fmap-gp : ⊙A ⊙→ ⊙B → Ω^S-group O ⊙A {{lA}} →ᴳ Ω^S-group O ⊙B {{lB}}
    Ω-fmap-gp = (Ω^S-group-fmap O {{lA}} {{lB}})

  C : (x : A) → Type (lmax i j)
  C x = 
      Σ B λ y
    → Σ (x == a → y == b) λ h
    → Π (x == a) λ α
    → fst (fold α h) == g

  reformulating-Ω-fiber :
    (hfiber Ω-fmap-gp mg) ≃ Π A C
  reformulating-Ω-fiber =
    Σ (Σ (A → B) (λ f → f a == b))
       (λ ⊙f → Ω-fmap-gp ⊙f == mg)
      ≃⟨ Σ-assoc ⟩
    ( Σ (A → B) λ f
    → Σ (f a == b) λ f₀
    → Ω-fmap-gp (f , f₀) == mg )
      ≃⟨ Σ-emap-r (λ f → {!   !}) ⟩
    ( Σ (A → B) λ f
    → Π A λ x
    → Σ (x == a → f x == b) λ h
    → Π (x == a) λ α
    → fst (fold α h) == g )
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
    → {!   !}

  Cxy-pathto-equivalence : (x : A) (α : x == a) (y : B)
    → ( Σ (x == a → y == b) λ h
      → (fold α h == ⊙g) )
    ≃ ( y == b )
  Cxy-pathto-equivalence x α y = to α y , 
    contr-map-is-equiv λ β → is-contr-to-hfiber α y β
    where
      to : {x : A} (α : x == a) (y : B)
        → ( Σ (x == a → y == b) λ h
            → (fold α h == ⊙g) )
        → ( y == b )
      to α y = λ{ (h , _) → h α }

      is-contr-to-hfiber : {x : A} (α : x == a)
        → (y : B) (β : y == b)
        → is-contr (hfiber (to α y) β)
      is-contr-to-hfiber idp .b idp =
        equiv-preserves-level
          (Σ₂-×-comm
          ∘e Σ-emap-r (
            λ{ (h , h₀) → 
              pre∙-equiv
              (lemma-1-0-4-2 
                (is-homogeneous-Ω ⊙B) 
                idp idp (fst (fold idp h)) h 
                (λ= λ ω → ap (λ p → ! p ∙ h ω) h₀) 
                (snd (fold idp h)) h₀) 
              }
            )
          ) 
          {{pathto-is-contr ⊙g}}
    
  is-contr-C : (x : A) → is-contr (C x)
  is-contr-C x = ∥⋅∥-rec is-contr-is-prop (λ p → transport _ p is-contr-Ca) (fst (snd cA a x))
    where abstract
      private
        lemma : {x : B} (ω : x == x) (H : ω == idp)
          → !-inv-l ω ==
            ap (λ p → ! p ∙ ω) H ∙ H
        lemma .idp idp = idp

      is-contr-Ca : is-contr (C a)
      is-contr-Ca = equiv-preserves-level (simplify-C idp ⁻¹ ∘e (Σ-emap-r (λ y → Cxy-pathto-equivalence a idp y ⁻¹)))
        {{ pathto-is-contr b }}

  is-contr-fiber : is-contr (hfiber Ω-fmap-gp mg)
  is-contr-fiber = equiv-preserves-level (reformulating-Ω-fiber ⁻¹) 
    {{weak-λ= λ x → is-contr-C x}}

-- And we export the following result

module _ 
  {i} {⊙A : Ptd i}
  {j} {⊙B : Ptd j}
  (cA : is ⟨ O ⟩ connected (de⊙ ⊙A))
  (lA : has-level ⟨ 1 ⟩ (de⊙ ⊙A))
  (lB : has-level ⟨ 1 ⟩ (de⊙ ⊙B))
  where

  private
    Ω-fmap-gp : ⊙A ⊙→ ⊙B → Ω^S-group O ⊙A {{lA}} →ᴳ Ω^S-group O ⊙B {{lB}}
    Ω-fmap-gp = (Ω^S-group-fmap O {{lA}} {{lB}})

  is-equiv-Ω-fmap-gp : 
    is-equiv Ω-fmap-gp
  is-equiv-Ω-fmap-gp = contr-map-is-equiv
    λ mg → is-contr-Ω-fiber-O.is-contr-fiber cA lA lB mg

-}   