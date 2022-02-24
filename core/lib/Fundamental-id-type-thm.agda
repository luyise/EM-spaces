{-# OPTIONS --without-K #-}

{- This is a fundamental result about identity types,
  borrowed from the agda-unimath library -}

open import lib.Base
open import lib.Equivalence
open import lib.Equivalence2
open import lib.NType
open import lib.types.Sigma

module lib.Fundamental-id-type-thm where

module _
  {i j} {A : Type i} {B : A → Type j} (a : A) (b : B a)
  where

  abstract
    fundamental-theorem-id :
      is-contr (Σ A B) → (f : (x : A) → a == x → B x) → ((x : A) → is-equiv (f x))
    fundamental-theorem-id is-contr-AB f =
      total-equiv-is-fiber-equiv f
        (contr-map-is-equiv λ s → 
          Σ-level 
            (pathfrom-is-contr _) 
            λ x → has-level-apply (raise-level _ is-contr-AB) _ _)

  -- abstract
  --   fundamental-theorem-id' :
  --     (f : (x : A) → Id a x → B x) → is-fiberwise-equiv f → is-contr (Σ A B)
  --   fundamental-theorem-id' f is-fiberwise-equiv-f =
  --     is-contr-is-equiv'
  --       ( Σ A (Id a))
  --       ( tot f)
  --       ( is-equiv-tot-is-fiberwise-equiv is-fiberwise-equiv-f)
  --       ( is-contr-total-path a)