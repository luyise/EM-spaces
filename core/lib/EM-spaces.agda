{-
This file is a variation on the library HoTT-Agda,
written by Leclerc L.

This file uses univalence.
-}

{-# OPTIONS --without-K --warning ignore #-}

open import lib.Base
open import lib.Equivalence
open import lib.Equivalence2
open import lib.Higher-torsor
open import lib.Homogeneous
open import lib.NConnected
open import lib.NType
open import lib.NType2
open import lib.PathFunctor
open import lib.PathGroupoid
open import lib.Univalence
open import lib.types.LoopSpace
open import lib.types.Nat
open import lib.types.TLevel

module lib.EM-spaces where

-- first we show several properties about the first Eilenberg-MacLane space
-- of a n-connected (n+1)-type which is homogeneous.

module EM {i : ULevel} {n : ℕ} (B : Type i)
  (b : B) (lB : has-level (⟨ 1 + n ⟩) B) 
  (cB : is (⟨ n ⟩) connected B)
  (hB : is-homogeneous B)
  where

  private
    leq⊙B : has-level (⟨ n ⟩) (⊙[ B , b ] == ⊙[ B , b ])
    leq⊙B = equiv-preserves-level ⊙ua-equiv 
      {{raise-level-≤T {m = 0} 
        (⟨⟩-monotone-≤ (O≤ n)) 
        (is-set-⊙≃-n-connected-Sn-type cB lB b b)}}
    
    ⊙B = ⊙[ B , b ]

  abstract
    ⊙K : Ptd (lsucc i)
    ⊙K = higher-torsor.⊙K B b lB cB hB leq⊙B
  
  K : Type (lsucc i)
  K = de⊙ ⊙K
  k₀ : K
  k₀ = pt ⊙K

  abstract
    ⊙K-up : ∀ {j} (⊙A : Ptd j)
      → (has-level ⟨ (S n) *2 ⟩ (de⊙ ⊙A))
      → (⊙K ⊙→ ⊙A) ≃ (⊙[ B , b ] ⊙→ ⊙Ω ⊙A)
    ⊙K-up ⊙A lA = universal-property.⊙K-universal-property
      n ⊙B lB cB ⊙A lA hB leq⊙B

    K-S-connected : is ⟨ S n ⟩ connected K
    K-S-connected = is-connected-torsor B b lB cB hB leq⊙B

    K-SS-type : has-level ⟨ S (S n) ⟩ K
    K-SS-type = has-level-torsor B b lB cB hB leq⊙B

    K-homogeneous : is-homogeneous K
    K-homogeneous = is-weakly-homogeneous-is-homogeneous 
      (is-weakly-homogeneous-n-connected-Sn-type (O<S n) 
      K-S-connected K-SS-type)

-- Then we define the iterated EM-space on suche types

private
  iterated-⊙K :
    {i : ULevel} {n : ℕ}
    → (B : Type i)
    → (b : B) 
    → (lB : has-level (⟨ 1 + n ⟩) B) 
    → (cB : is (⟨ n ⟩) connected B)
    → (hB : is-homogeneous B)
    → (k : ℕ)
    → Ptd (lsucc^ k i)

  iterated-⊙K B b _ _ _ O = ⊙[ B , b ]
  iterated-⊙K B b lB cB hB (S k) = 
    iterated-⊙K K k₀ 
      K-SS-type K-S-connected K-homogeneous k
      where open EM B b lB cB hB

  iterated-K :
    {i : ULevel} {n : ℕ}
    → (B : Type i)
    → (b : B) 
    → (lB : has-level (⟨ 1 + n ⟩) B) 
    → (cB : is (⟨ n ⟩) connected B)
    → (hB : is-homogeneous B)
    → (k : ℕ)
    → Type (lsucc^ k i)
  iterated-K B b lB cB hB k =
    de⊙ (iterated-⊙K B b lB cB hB k)

  iterated-K-connected : 
    {i : ULevel} {n : ℕ}
    → (B : Type i)
    → (b : B) 
    → (lB : has-level (⟨ 1 + n ⟩) B) 
    → (cB : is (⟨ n ⟩) connected B)
    → (hB : is-homogeneous B)
    → (k : ℕ)
    → is ⟨ k + n ⟩ connected
      (iterated-K B b lB cB hB k)
    
  iterated-K-connected {i} {n} _ _ _ cB _ O = cB
  iterated-K-connected {i} {n} B b lB cB hB (S k) =
    transport (λ q → is (⟨ q ⟩) connected 
      (iterated-K B b lB cB hB (S k)))
        (+-βr k n)
        (iterated-K-connected {lsucc i} {S n} K k₀
        K-SS-type K-S-connected K-homogeneous k)
    where open EM B b lB cB hB

  iterated-K-level : 
    {i : ULevel} {n : ℕ}
    → (B : Type i)
    → (b : B) 
    → (lB : has-level (⟨ 1 + n ⟩) B) 
    → (cB : is (⟨ n ⟩) connected B)
    → (hB : is-homogeneous B)
    → (k : ℕ)
    → has-level ⟨ k + S n ⟩
      (iterated-K B b lB cB hB k)
    
  iterated-K-level {i} {n} _ _ lB _ _ O = lB
  iterated-K-level {i} {n} B b lB cB hB (S k) =
    transport (λ q → has-level (⟨ q ⟩)
      (iterated-K B b lB cB hB (S k)))
        (+-βr k (S n))
        (iterated-K-level {lsucc i} {S n} K k₀
        K-SS-type K-S-connected K-homogeneous k)
    where open EM B b lB cB hB

  iterated-K-homogeneous :
    {i : ULevel} {n : ℕ}
    → (B : Type i)
    → (b : B) 
    → (lB : has-level (⟨ 1 + n ⟩) B) 
    → (cB : is (⟨ n ⟩) connected B)
    → (hB : is-homogeneous B)
    → (k : ℕ)
    → is-homogeneous
        (iterated-K B b lB cB hB k)

  iterated-K-homogeneous _ _ _ _ hB O = hB
  iterated-K-homogeneous {n = n} B b lB cB hB (S k) = 
    is-weakly-homogeneous-is-homogeneous 
    (is-weakly-homogeneous-n-connected-Sn-type (O<S (k + n)) 
    (iterated-K-connected B b lB cB hB (S k))
    (transport (λ q → has-level (⟨ q ⟩) (iterated-K B b lB cB hB (S k)))
      (ap S (+-βr k n))
      (iterated-K-level B b lB cB hB (S k))))

  iterated-⊙K-up :
    {i : ULevel} {n : ℕ}
    → (B : Type i)
    → (b : B) 
    → (lB : has-level (⟨ 1 + n ⟩) B) 
    → (cB : is (⟨ n ⟩) connected B)
    → (hB : is-homogeneous B)
    → (k : ℕ)
    → ∀ {j} (⊙A : Ptd j)
    → (has-level ⟨ 1 + k + (n *2) ⟩ (de⊙ ⊙A))
    → ((iterated-⊙K B b lB cB hB k) ⊙→ ⊙A) ≃ (⊙[ B , b ] ⊙→ ⊙Ω^ k ⊙A)
  iterated-⊙K-up _ _ _ _ _ O _ _ = ide _
  iterated-⊙K-up {n = n} B b lB cB hB (S k) ⊙A lA =
    (iterated-⊙K B b lB cB hB (S k) ⊙→ ⊙A)
      ≃⟨ iterated-⊙K-up K k₀ K-SS-type K-S-connected K-homogeneous k ⊙A 
        (transport (λ q → has-level (⟨ q ⟩) (de⊙ ⊙A)) 
        computation₁ (raise-level _ lA) ) ⟩
    (⊙[ K , k₀ ] ⊙→ ⊙Ω^ k ⊙A)
      ≃⟨ coe-equiv (ap (λ ⊙X → (⊙X ⊙→ ⊙Ω^ k ⊙A)) idp) ⟩
    (⊙K ⊙→ (⊙Ω^ k ⊙A))
      ≃⟨ ⊙K-up (⊙Ω^ k ⊙A) (transport (λ q → has-level (⟨ q ⟩) (de⊙ (⊙Ω^ k ⊙A))) 
      idp 
      (Ω^-level (S (S (S (S ⟨ n *2 ⟩₋₂)))) k ⊙A 
      ((transport (λ q → has-level q (de⊙ ⊙A)) computation₂ lA)))) ⟩
    (⊙[ B , b ] ⊙→ ⊙Ω (⊙Ω^ k ⊙A))
      ≃⟨ ide _ ⟩
    (⊙[ B , b ] ⊙→ ⊙Ω^ (S k) ⊙A)
      ≃∎
      where 
        open EM B b lB cB hB

        private
          computation₁ : S (S (S (k + n *2))) == S (k + S n *2)
          computation₁ = 
            ap (λ q → S (S q)) (! (+-βr k (n *2))) 
            ∙ ap S (! (+-βr k (S (n *2))))

          computation₂ : ⟨ S (S (k + n *2)) ⟩ == ⟨ k ⟩₋₂ +2+ S (S (S (S ⟨ n *2 ⟩₋₂)))
          computation₂ = 
            ap ⟨_⟩₋₂ (
              (ap (λ q → (S (S (S q)))) (! (+-βr k (n *2)))) 
              ∙ (ap (λ q → (S (S q))) (! (+-βr k (S (n *2))))) 
              ∙ (ap (λ q → S q) (! (+-βr k (S (S (n *2)))))) 
              ∙ (! (+-βr k (S (S (S (n *2))))))
            )
            ∙ (+-+2+ k (S (S (S (S (n *2))))))

module _ {i : ULevel} {n : ℕ} (B : Type i)
  (b : B) (lB : has-level (⟨ 1 + n ⟩) B) 
  (cB : is (⟨ n ⟩) connected B)
  (hB : is-homogeneous B)
  where
  
  is-EM-space : ∀ (j : ULevel) (K : Type j) 
    (k₀ : K) (k : ℕ)
    (lK : has-level ⟨ 1 + k + (n *2) ⟩ K)
    → Agda.Primitive.Setω
  is-EM-space j K k₀ k lK =
    ∀ {j'} (⊙A : Ptd j')
    → (has-level ⟨ 1 + k + (n *2) ⟩ (de⊙ ⊙A))
    → (⊙[ K , k₀ ] ⊙→ ⊙A) ≃ (⊙[ B , b ] ⊙→ ⊙Ω^ k ⊙A)


module iterated-EM {i : ULevel} {n : ℕ} (B : Type i)
  (b : B) (lB : has-level (⟨ 1 + n ⟩) B) 
  (cB : is (⟨ n ⟩) connected B)
  (hB : is-homogeneous B)
  where

  ⊙K[_] : (k : ℕ) → Ptd (lsucc^ k i)
  ⊙K[_] = iterated-⊙K B b lB cB hB
  K[_] : (k : ℕ) → Type (lsucc^ k i)
  K[ k ] = de⊙ (⊙K[ k ])

  abstract
    ⊙K-connected : 
      (k : ℕ) → is ⟨ k + n ⟩ connected K[ k ]
    ⊙K-connected k = 
      iterated-K-connected B b lB cB hB k

    ⊙K-level :
      (k : ℕ) → has-level ⟨ k + S n ⟩ K[ k ]
    ⊙K-level k =
      iterated-K-level B b lB cB hB k

    ⊙K-homogeneous :
      (k : ℕ) → is-homogeneous K[ k ]
    ⊙K-homogeneous = iterated-K-homogeneous B b lB cB hB

    ⊙K-up : (k : ℕ) → ∀ {j} (⊙A : Ptd j)
      → (has-level ⟨ 1 + k + (n *2) ⟩ (de⊙ ⊙A))
      → (⊙K[ k ] ⊙→ ⊙A) ≃ (⊙[ B , b ] ⊙→ ⊙Ω^ k ⊙A)
    ⊙K-up = iterated-⊙K-up B b lB cB hB

  is-EM-space-is-K :
    ∀ {j} (K : Type j)
    (k₀ : K) (k : ℕ)
    (lK : has-level ⟨ 1 + k + (n *2) ⟩ K)
    → (is-EM-space B b lB cB hB j K k₀ k lK)
    → ⊙K[ k ] ⊙≃ ⊙[ K , k₀ ]
  is-EM-space-is-K K k₀ k lK K-up = 
    ⊙to , 
    is-eq to from {!   !} {!   !}
    where private
      computation : ⟨ k + S n ⟩ ≤T ⟨ S (k + n *2) ⟩
      computation = {!   !}

      ⊙to : ⊙K[ k ] ⊙→ ⊙[ K , k₀ ]
      ⊙to = is-equiv.g (snd (⊙K-up k ⊙[ K , k₀ ] lK)) ((–> (K-up ⊙[ K , k₀ ] lK)) (⊙idf _))

      to : K[ k ] → K
      to = fst ⊙to

      from : K → K[ k ]
      from = fst ((<– (K-up _ (raise-level-≤T computation (⊙K-level k)))) 
        ((–> (⊙K-up k ⊙K[ k ] (raise-level-≤T computation (⊙K-level k)))) (⊙idf _)))

      to-from : to ∘ from == x
      to-from x = {!   !}
   