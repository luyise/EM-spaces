{-
This file is a variation on the library HoTT-Agda,
written by Leclerc L.
-}

{-# OPTIONS --without-K --warning ignore #-}

open import lib.Base
open import lib.Equivalence
open import lib.Homogeneous
open import lib.NType
open import lib.NConnected
open import lib.types.Pointed
open import lib.types.Sigma

module lib.EM-Spaces where

-- As G-Torsor with G a group may be thought of G where
-- the origin as been "removed" in the sens that every point
-- of a G-Torsor is equivalent to an other one,
-- the following construction is about types that are isomorphic
-- to G, whatever the choice of the base point you make.
-- In particular, those higher torsors are (weakly) homogeneous

module higher-torsor {i : ULevel} {n : ℕ₋₂} (B : Type i)
  (b : B) (lB : has-level (S n) B) (cB : is n connected B)
  (hB : is-weakly-homogeneous B)
  where

  ⊙B = ⊙[ B , b ]

  Torsor : Type (lsucc i)
  Torsor = 
    Σ (Type i) λ A 
      → (has-level (S n) A) 
      × (is n connected A)
      × (Π A λ a → ⊙[ A , a ] ⊙≃ ⊙B)

  chart-of_at_ : (TA : Torsor) → (a : fst TA) → ⊙[ fst TA , a ] ⊙≃ ⊙B
  chart-of (_ , _ , _ , iso) at a = iso a

  torsors-are-weakly-homogeneous :
    (TA : Torsor) → is-weakly-homogeneous (fst TA)
  torsors-are-weakly-homogeneous TA a₀ a₁ =
    (chart-of TA at a₁)⊙⁻¹ ⊙∘e (chart-of TA at a₀)

  -- Since B is supposed to be homogenous, it is
  -- a B Torsor, namely the trivial one.

  trivial-torsor : Torsor
  trivial-torsor = B , lB , cB , λ b' → hB b' b

  TB = trivial-torsor

  -- Once a point of a B Torsor has been chosen,
  -- then this B Torsor is the trivial 
  -- torsor over B.

  -- pointed-torsors-are-trivial :
  --   (TA : Torsor) → (a : fst TA) 
  --   → (TA , a) == (TB , b) :> Σ Torsor fst
  -- pointed-torsors-are-trivial TA a = {!   !}
