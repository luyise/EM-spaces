{-
This file is a variation on the library HoTT-Agda,
written by Leclerc L.
-}

{-# OPTIONS --without-K --warning ignore #-}

open import lib.Base
open import lib.PathOver
open import lib.PathGroupoid
open import lib.PathFunctor
open import lib.PathSeq
open import lib.types.Paths
open import lib.types.LoopSpace
open import lib.Function
open import lib.types.Pointed
open import lib.Funext
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
  → transport (λ X → ⊙[ A , a₀ ] == X) (! (hA a₀ a₀) ∙ (hA a₀ a₁)) idp 
    == ap ⊙[ A ,_] p
lemma-1-0-4-1 {A = A} hA a₀ .a₀ idp =
  ap (λ u → transport (λ X → ⊙[ A , a₀ ] == X) u idp) (!-inv-l (hA a₀ a₀))

lemma-1-0-4-2 : ∀ {i} {A : Type i}
  → is-homogeneous A
  → ∀ (a₀ : A) {j} {X : Type j} (x₀ : X) (f g : X → A)
  → (f == g)
  → ∀ (f₀ : f x₀ == a₀) (g₀ : g x₀ == a₀)
  → (f , f₀) == (g , g₀) :> (⊙[ X , x₀ ] ⊙→ ⊙[ A , a₀ ])
lemma-1-0-4-2 {A = A} hA a₀ {X = X} x₀ f .f idp f₀ g₀ = equality
  where private
    r : a₀ == a₀
    r = ! f₀ ∙ g₀

    P : ⊙[ A , a₀ ] == ⊙[ A , a₀ ]
    P = ap ⊙[ A ,_] r

    P==idp : idp == P
    P==idp = 
      ! (ap (λ u → transport (λ Y → ⊙[ A , a₀ ] == Y) u idp) (!-inv-l (hA a₀ a₀))) 
      ∙ lemma-1-0-4-1 hA a₀ a₀ r

    ⊙coe-ap-⊙[A,_] : {a₁ : A} (p : a₀ == a₁) 
      → ⊙coe (ap ⊙[ A ,_] p) ⊙∘ (f , f₀) == (f , f₀ ∙ p)
    ⊙coe-ap-⊙[A,_] {.a₀} idp = pair= idp (ap (_∙ idp) (ap-idf f₀))

    f₀==g₀-mod-P : transport (⊙[ X , x₀ ] ⊙→_) P (f , f₀) == (f , g₀)
    f₀==g₀-mod-P = transport-post⊙∘ ⊙[ X , x₀ ] P (f , f₀) 
      ∙ (⊙coe-ap-⊙[A,_] r) ∙ pair= idp (! (∙-assoc f₀ (! f₀) g₀) ∙ ap ( _∙ g₀) (!-inv-r f₀))
    
    equality : (f , f₀) == (f , g₀) :> (⊙[ X , x₀ ] ⊙→ ⊙[ A , a₀ ])
    equality = transport 
      (λ E → transport (⊙[ X , x₀ ] ⊙→_) E (f , f₀) == (f , g₀)) 
      (! P==idp) f₀==g₀-mod-P 
      :> (transport (⊙[ X , x₀ ] ⊙→_) idp (f , f₀) == (f , g₀))