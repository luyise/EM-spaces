{-
This file is a variation on the library HoTT-Agda,
written by Leclerc L.
-}

{-# OPTIONS --without-K --warning ignore #-}

open import lib.Base

open import lib.Equivalence
open import lib.Equivalence2
open import lib.Fundamental-id-type-thm
open import lib.Funext
open import lib.Homogeneous
open import lib.NConnected
open import lib.NType
open import lib.NType2
open import lib.PathGroupoid
open import lib.PathOver
open import lib.types.LoopSpace
open import lib.types.Pointed
open import lib.types.Sigma
open import lib.types.Truncation

module lib.EM-Spaces where

-- As G-Torsor with G a group may be thought of G where
-- the origin as been "removed" in the sens that every point
-- of a G-Torsor is equivalent to an other one,
-- the following construction is about types that are isomorphic
-- to G, whatever the choice of the base point you make.
-- In particular, those higher torsors are homogeneous

module higher-torsor {i : ULevel} {n : ℕ₋₂} (B : Type i)
  (b : B) (lB : has-level (S n) B) (cB : is n connected B)
  (hB : is-homogeneous B)
  (leq⊙B : has-level n (⊙[ B , b ] == ⊙[ B , b ]))
  where

  -- We begin by introducing a better behaved familly of equality over B,
  -- so that norm-hB b₀ b₀ == idp

  norm-hB : is-homogeneous B
  norm-hB =
    λ b₀ b₁ → ! (hB b₀ b₀) ∙ (hB b₀ b₁)

  normalised-norm-hB : (b₀ : B) →
    norm-hB b₀ b₀ == idp
  normalised-norm-hB b₀ = !-inv-l (hB b₀ b₀)

  ⊙B = ⊙[ B , b ]

  -- and we show that the hypothesis leq⊙B implies a stronger
  -- properties, thanks to the homogeneity of B.
  -- If n ≥ 0, we may use the n-connectedness of B to show this,
  -- maybe we could also derive it from weak-homogeneity of B.
  
  leq⊙B' : (x : B) → has-level n (⊙[ B , x ] == ⊙B)
  leq⊙B' x = transport (λ ⊙X → has-level n (⊙X == ⊙B)) (hB b x) leq⊙B

  Torsor : Type (lsucc i)
  Torsor = 
    Σ (Type i) λ A 
      → (has-level (S n) A) 
      × (is n connected A)
      × (Π A λ a → ⊙[ A , a ] == ⊙B)

  chart-of_at_ : (TA : Torsor) → (a : fst TA) → ⊙[ fst TA , a ] == ⊙B
  chart-of (_ , _ , _ , chart) at a = chart a

  torsors-are-homogeneous :
    (TA : Torsor) → is-homogeneous (fst TA)
  torsors-are-homogeneous TA a₀ a₁ =
    (chart-of TA at a₀) ∙ ! (chart-of TA at a₁) 

  -- Since B is supposed to be homogenous, it is
  -- a B Torsor, namely the trivial one.

  trivial-torsor : Torsor
  trivial-torsor = B , lB , cB , λ b' → norm-hB b' b

  TB = trivial-torsor

  -- Once a point of a B Torsor has been chosen,
  -- then this B Torsor is the trivial 
  -- torsor over B.

  module pointed-torsors-are-trivial-proof 
    where

    -- This is the result we aim to prove

    pointed-torsors-are-trivial =
      (TA : Torsor) → (a : fst TA) 
      → (TA , a) == (TB , b) :> Σ Torsor fst

    reformulation₁ =
      (⊙A : Ptd i) → (u : ⊙A == ⊙B)
      → (lA : has-level (S n) (de⊙ ⊙A))
      → (cA : is n connected (de⊙ ⊙A))
      → (chart : ((x : de⊙ ⊙A) → ⊙[ de⊙ ⊙A , x ] == ⊙B))
      → (u == chart (pt ⊙A))
      → ((de⊙ ⊙A , lA , cA , chart) , pt ⊙A) == (TB , b) :> Σ Torsor fst

    lemma₁ : reformulation₁ → pointed-torsors-are-trivial
    lemma₁ R₂ TA a = 
      let A = fst TA in
      let ⊙A = ⊙[ A , a ] in
      let lA = fst (snd TA) in
      let cA = fst (snd (snd TA)) in
      let chart = snd (snd (snd TA)) in
      R₂ ⊙A (chart a) lA cA _ idp

    lemma₂ : reformulation₁
    lemma₂ _ idp lB' cB' chart eq = 
      pair=
        (pair= idp
          (pair×= 
            (prop-path has-level-is-prop _ _) 
            (pair×=
              ((prop-path is-connected-is-prop _ _)) 
              (lemma₃ chart (! eq))
            )
          )
        )
        ( ↓-cst2-in idp _ idp )

      where
        -- We can retrieve from the fact that chart and norm-hB agree
        -- on one point that they agree everywhere.
        -- this comes from the fact that B is sufficiently connected,
        -- so its chart must be coherent in a strong way
        -- For this, we need to know that ⊙[ B , x ] == ⊙B is a n type,
        -- this is automatic if we admit univalence.
        is-prop-pointed-chart : {n : ℕ₋₂}
          → ((x : B) → has-level n (⊙[ B , x ] == ⊙B))
          → (is n connected B)
          → is-prop
            (Σ ((x : B) → ⊙[ B , x ] == ⊙B) λ chart
            → (chart b == idp))
        is-prop-pointed-chart {⟨-2⟩} leq⊙B' _ = 
          Σ-level (raise-level _ (weak-λ= leq⊙B')) 
          λ chart → has-level-apply (raise-level _ (raise-level _ (leq⊙B' _))) _ _
        is-prop-pointed-chart {S n} leq⊙B' cB =  
          lemma-1-0-3 B (λ x → ⊙[ B , x ] == ⊙B) b idp n _ cB leq⊙B'

        lemma₃ : 
          (chart : (x : B) → ⊙[ B , x ] == ⊙B)
          → (chart b == idp )
          → chart == (λ x → norm-hB x b)
        lemma₃ chart chart₀ = fst= 
          (prop-path (is-prop-pointed-chart leq⊙B' cB) (chart , chart₀) 
          ((λ b' → norm-hB b' b) , normalised-norm-hB b))
        
    abstract
      result : pointed-torsors-are-trivial
      result = lemma₁ lemma₂
 
  pointed-torsors-are-trivial :
    (TA : Torsor) → (a : fst TA) 
      → (TA , a) == (TB , b) :> Σ Torsor fst
  pointed-torsors-are-trivial =
    pointed-torsors-are-trivial-proof.result

  -- From this result we may derive the contractibility of
  -- the type of pointed B-Torsors.

  is-contr-ptd-torsor :
    is-contr (Σ Torsor fst)
  is-contr-ptd-torsor = has-level-in 
    ((TB , b) , 
    λ{ (TA , a) → ! (pointed-torsors-are-trivial TA a) })

  -- A corollary of this is that giving a point of a B-Torsor TA
  -- is the same as giving an equality TB == TA,
  -- so we have an isomorphism between A and TB == TA

  torsor-==-≃-space : (TA : Torsor) →
    is-equiv (λ (u : TB == TA) → transport fst u b)
  torsor-==-≃-space = fundamental-theorem-id _ b is-contr-ptd-torsor _

  -- As a specific case, 
  -- one get the loop space of B-Torsor from the previous result

  torsor-loop-space : Ω ⊙[ Torsor , TB ] ≃ B
  torsor-loop-space = _ , torsor-==-≃-space TB

  -- We then show that the type of Torsor is a (n+2)-type,
  -- which is also (n+1)-connected.

  -- is-connected-torsor : is (S n) connected Torsor
  -- is-connected-torsor = [ TB ] , 
  --   λ TA₁ TA₂ → {!   !}

  -- has-level-torsor : has-level (S (S n)) Torsor
  -- has-level-torsor = has-level-in 
  --   λ TA₁ TA₂ → {!   !}