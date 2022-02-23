{-
This file is a variation on the library HoTT-Agda,
written by Leclerc L.
-}

{-# OPTIONS --without-K --warning ignore #-}

open import lib.Base
open import lib.Equivalence
open import lib.Funext
open import lib.NConnected
open import lib.NType
open import lib.PathOver
open import lib.PathGroupoid
open import lib.PathFunctor
open import lib.PathSeq
open import lib.types.Nat
open import lib.types.Paths
open import lib.types.LoopSpace
open import lib.Function
open import lib.types.Pointed
open import lib.types.Sigma
open import lib.types.TLevel

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

{- Defining a weaker notion, maybe useful without ua -}

is-weakly-homogeneous : ∀ {i} (A : Type i) → Type i
is-weakly-homogeneous A = (a₀ a₁ : A) → ⊙[ A , a₀ ] ⊙≃ ⊙[ A , a₁ ]

is-homogeneous-is-weakly-homogeneous :
  ∀ {i} {A : Type i}
  → (is-homogeneous A) 
  → is-weakly-homogeneous A
is-homogeneous-is-weakly-homogeneous {A = A} hA a₀ a₁ =
  transport (λ ⊙X → ⊙[ A , a₀ ] ⊙≃ ⊙X) (hA a₀ a₁) (⊙ide _)

is-weakly-homogeneous-Ω : ∀ {i} (A : Ptd i) → is-weakly-homogeneous (Ω A)
is-weakly-homogeneous-Ω = is-homogeneous-is-weakly-homogeneous ∘ is-homogeneous-Ω

is-weakly-homogeneous-n-connected-Sn-type :
  ∀ {i} {A : Type i} {n : ℕ} (0<n : 0 < n)
  → (is (⟨ n ⟩) connected A)
  → (has-level (S ⟨ n ⟩) A)
  → is-weakly-homogeneous A
is-weakly-homogeneous-n-connected-Sn-type {A = A} {n} (ltS) cA lA a = 
  is-equiv.g (lemma-1-0-2 A 
    (λ (x : A) → ⊙[ A , a ] ⊙≃ ⊙[ A , x ])
    a ⟨ 0 ⟩ cA (λ x → is-set-⊙≃-n-connected-Sn-type cA lA a x)) 
    (⊙ide _)
is-weakly-homogeneous-n-connected-Sn-type {A = A} {n = _} (ltSR k) cA lA a = 
  is-equiv.g (lemma-1-0-2 A 
    (λ (x : A) → ⊙[ A , a ] ⊙≃ ⊙[ A , x ])
    a ⟨ 0 ⟩ (is-<T-connected (<T-ap-S (⟨⟩-monotone-< k)) cA) (λ x → is-set-⊙≃-n-connected-Sn-type cA lA a x)) 
    (⊙ide _)