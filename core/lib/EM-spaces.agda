{-
This file is a variation on the library HoTT-Agda,
written by Leclerc L.

This file uses univalence.
-}

{-# OPTIONS --without-K --warning ignore #-}

open import lib.Base
open import lib.Equivalence
open import lib.Homogeneous
open import lib.NConnected
open import lib.NType
open import lib.Univalence
open import lib.types.Nat
open import lib.types.TLevel

module lib.EM-spaces where

module _ {i : ULevel} {n : ℕ} (B : Type i)
  (b : B) (lB : has-level (⟨ 1 + n ⟩) B) 
  (cB : is (⟨ n ⟩) connected B)
  (hB : is-homogeneous B)
  where

  private
    leq⊙B : has-level (⟨ n ⟩) (⊙[ B , b ] == ⊙[ B , b ])
    leq⊙B = equiv-preserves-level {! ua-equiv !} {{{!   !}}}