{-
This file is a variation on the library HoTT-Agda,
written by Leclerc L.
-}

{-# OPTIONS --without-K --warning ignore #-}

open import lib.Base
open import lib.Equivalence
open import lib.Funext
open import lib.PathOver
open import lib.PathGroupoid
open import lib.PathFunctor
open import lib.PathSeq
open import lib.types.Paths
open import lib.types.LoopSpace
open import lib.Function
open import lib.types.Pointed
open import lib.types.Sigma

module lib.Homogeneous where

{- Definition of homogeneous types -}

is-homogeneous : ∀ {i} (A : Type i) → Type (lsucc i)
is-homogeneous A = (a₀ a₁ : A) → ⊙[ A , a₀ ] == ⊙[ A , a₁ ]

is-homogeneous-Ω : ∀ {i} (A : Ptd i) → is-homogeneous (Ω A)
is-homogeneous-Ω A p q = 
  (! (lemma (de⊙ A) (pt A) (pt A) p)) 
  ∙ (lemma (de⊙ A) (pt A) (pt A) q)
  where private
    lemma : ∀ {i} (A : Type i) (a b : A) (p : a == b) → ⊙[ a == a , idp ] == ⊙[ a == b , p ]
    lemma A a .a idp = idp
    
{- proofs of several lemmas about homogeneous types,
  adapted from the paper
  "Synthetic Cohomology Theory in Cubical Agda" -}

lemma-1-0-4-0 : ∀ {i j} {A : Type i} (B : Type j)
  → (a₀ a₁ : A) (p : a₀ == a₁) (f : A → B)
  → PathOver (λ a → f a₀ == f a) p idp (ap f p)
lemma-1-0-4-0 B a₀ .a₀ idp b = idp

lemma-1-0-4-1 : ∀ {i} {A : Type i}
  → (hA : is-homogeneous A)
  → (a₀ a₁ : A) (p : a₀ == a₁)
  → ap ⊙[ A ,_] p == ! (hA a₀ a₀) ∙ (hA a₀ a₁) 
lemma-1-0-4-1 {A = A} hA a₀ .a₀ idp = ! (!-inv-l (hA a₀ a₀))

lemma-1-0-4-2 : ∀ {i} {A : Type i}
  → is-homogeneous A
  → ∀ (a₀ : A) {j} {X : Type j} (x₀ : X) (f g : X → A)
  → (f == g)
  → ∀ (f₀ : f x₀ == a₀) (g₀ : g x₀ == a₀)
  → (f , f₀) == (g , g₀) :> (⊙[ X , x₀ ] ⊙→ ⊙[ A , a₀ ])
lemma-1-0-4-2 {A = A} hA .(f x₀) {X = X} x₀ f .f idp idp g₀ = equality
  module lemma-1-0-4-2-proof where
    a₀ = f x₀

    r : a₀ == a₀
    r = g₀

    P : ⊙[ A , a₀ ] == ⊙[ A , a₀ ]
    P = ap ⊙[ A ,_] r

    P==idp : P == idp
    P==idp = lemma-1-0-4-1 hA a₀ a₀ r ∙ (!-inv-l (hA a₀ a₀))

    ⊙coe-ap-⊙[A,_] : {a₁ : A} (p : a₀ == a₁) 
      → ⊙coe (ap ⊙[ A ,_] p) ⊙∘ (f , idp) == (f , p)
    ⊙coe-ap-⊙[A,_] {.a₀} idp = idp

    f₀==g₀-mod-P : transport (⊙[ X , x₀ ] ⊙→_) P (f , idp) == (f , g₀)
    f₀==g₀-mod-P = transport-post⊙∘ ⊙[ X , x₀ ] P (f , idp) ∙ (⊙coe-ap-⊙[A,_] r)

    equality : (f , idp) == (f , g₀) :> (⊙[ X , x₀ ] ⊙→ ⊙[ A , a₀ ])
    equality = transport
      (λ E → transport (⊙[ X , x₀ ] ⊙→_) E (f , idp) == (f , g₀)) 
      P==idp f₀==g₀-mod-P
      -- :> (transport (⊙[ X , x₀ ] ⊙→_) idp (f , idp) == (f , g₀))

module lemma-1-0-4-2-proof-idp 
  {i} {A : Type i} (hA : is-homogeneous A)
  {j} {X : Type j} (x₀ : X)
  (f : X → A)
  where
    P==idp-idp : lemma-1-0-4-2-proof.P==idp hA x₀ f idp == idp
    P==idp-idp = !-inv-l (!-inv-l (hA (f x₀) (f x₀)))

    open lemma-1-0-4-2-proof hA x₀ f idp
    abstract

      -- λ=-idp : ∀ {i j} {A : Type i}  {B : A → Type j} 
      --   → (f : (a : A) → B a)
      --   → λ= (λ (_ : A) → idp) == idp :> (f == f)
      -- λ=-idp _ = ! (λ=-η idp)

      -- equality-idp : equality == idp
      -- equality-idp = {!   !}
      --   transport 
      --   (λ E → transport (⊙[ X , x₀ ] ⊙→_) E (f , idp) == (f , idp)) 
      --   (P==idp idp idp) (f₀==g₀-mod-P idp idp)
      --     =⟨ ap 
      --         (λ γ → transport 
      --         (λ E → transport (⊙[ X , x₀ ] ⊙→_) E (f , idp) == (f , idp)) 
      --         γ (f₀==g₀-mod-P idp idp)) 
      --         P==idp-idp ⟩
      --   transport
      --     (λ E → transport (⊙[ X , x₀ ] ⊙→_) E (f , idp) == f , idp) idp
      --     (lemma-1-0-4-2-proof.f₀==g₀-mod-P hA (f x₀) x₀ f idp idp)
      --     =⟨ idp ⟩
      --   lemma-1-0-4-2-proof.f₀==g₀-mod-P hA (f x₀) x₀ f idp idp
      --     =⟨ idp ⟩
      --   transport-post⊙∘ ⊙[ X , x₀ ] (P idp idp) (f , idp) 
      --   ∙ (⊙coe-ap-⊙[A,_] idp idp idp) ∙ pair= idp (! (∙-assoc idp idp idp) ∙ ap ( _∙ idp) (!-inv-r idp))
      --     =⟨ {!   !} ⟩
      --   idp

-- lemma-1-0-4-3 : ∀ {i} {A : Type i}
--   → is-homogeneous A
--   → ∀ (a₀ : A) {j} {X : Type j} (x₀ : X) (f g : X → A)
--   → ∀ (f₀ : f x₀ == a₀) (g₀ : g x₀ == a₀)
--   → ((f , f₀) == (g , g₀)) ≃ (f == g)
-- lemma-1-0-4-3 {A = A} hA _ {X = X} x₀ f g idp g₀ = 
--   {!   !}
--     where private
--       f₀ = idp
--       a₀ = f x₀

--       to : (f , f₀) == (g , g₀) → f == g
--       to = fst= 

--       from : f == g → (f , f₀) == (g , g₀)
--       from eq = lemma-1-0-4-2 hA a₀ x₀ f g eq f₀ g₀

--       open lemma-1-0-4-2-proof

--       from-to : ∀ ptd-eq → from (to ptd-eq) == ptd-eq
--       from-to idp = 
--         from idp
--           =⟨ {!   !} ⟩
--         {!   !}
--           =⟨ {!   !} ⟩
--         idp

--       to-from : ∀ eq → to (from eq) == eq
--       to-from idp = {!   !}

-- fun-homogeneous : ∀ {i j} {⊙A : Ptd i} {B : Type j}
--   → (is-homogeneous B) → (b : B) 
--   → is-homogeneous (⊙A ⊙→ ⊙[ B , b ])
-- fun-homogeneous {⊙A = ⊙A} {B = B}
--   hB b ⊙f ⊙g = ptd= ( Σ= {!   !} {!   !}) {!   !}
--     where
--       A = de⊙ ⊙A
--       a = pt ⊙A
--       f = fst ⊙f
--       f₀ = snd ⊙f
--       g = fst ⊙g
--       g₀ = snd ⊙g

--       aut-f : (a : A) → ⊙[ B , b ] == ⊙[ B , f a ]
--       aut-f a = hB b (f a)

--       aut-g : (a : A) → ⊙[ B , b ] == ⊙[ B , g a ]
--       aut-g a = hB b (g a)

--       aut-fg : (a : A) → ⊙[ B , f a ] == ⊙[ B , g a ]
--       aut-fg a = ! (aut-f a) ∙ aut-g a

--       P : (⊙A ⊙→ ⊙[ B , b ]) == (⊙A ⊙→ ⊙[ B , b ])
--       P = {!   !}     