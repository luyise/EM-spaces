{-# OPTIONS --without-K #-}

open import lib.Base
open import lib.PathGroupoid
open import lib.PathFunctor
open import lib.Equivalence
open import lib.Equivalence2
open import lib.NType
open import lib.NType2
open import lib.PathOver
open import lib.types.Paths
open import lib.types.Pi
open import lib.types.Pointed
open import lib.types.Sigma


module lib.Univalence where

{- We postulate the univalence axiom as three separate axioms because it’s more
natural this way. But it doesn’t change anything in practice. -}

postulate  -- Univalence axiom
  ua : ∀ {i} {A B : Type i} → (A ≃ B) → A == B
  coe-equiv-β : ∀ {i} {A B : Type i} (e : A ≃ B) → coe-equiv (ua e) == e
  ua-η : ∀ {i} {A B : Type i} (p : A == B) → ua (coe-equiv p) == p

ua-equiv : ∀ {i} {A B : Type i} → (A ≃ B) ≃ (A == B)
ua-equiv = equiv ua coe-equiv ua-η coe-equiv-β

{- Reductions for coercions along a path constructed with the univalence axiom -}

coe-β : ∀ {i} {A B : Type i} (e : A ≃ B) (a : A)
  → coe (ua e) a == –> e a
coe-β e a = ap (λ e → –> e a) (coe-equiv-β e)

coe!-β : ∀ {i} {A B : Type i} (e : A ≃ B) (b : B)
  → coe! (ua e) b == <– e b
coe!-β e a = ap (λ e → <– e a) (coe-equiv-β e)

{- Paths over a path in a universe in the identity fibration reduces -}

↓-idf-ua-out : ∀ {i} {A B : Type i} (e : A ≃ B) {u : A} {v : B}
  → u == v [ (λ x → x) ↓ (ua e) ]
  → –> e u == v
↓-idf-ua-out e p = ! (coe-β e _) ∙ ↓-idf-out (ua e) p

↓-idf-ua-in : ∀ {i} {A B : Type i} (e : A ≃ B) {u : A} {v : B}
  → –> e u == v
  → u == v [ (λ x → x) ↓ (ua e) ]
↓-idf-ua-in e p = ↓-idf-in (ua e) (coe-β e _ ∙ p)

{- Induction along equivalences
If [P] is a predicate over all equivalences in a universe [Type i] and [d] is a
proof of [P] over all [ide A], then we get a section of [P]
-}

equiv-induction : ∀ {i j} (P : {A B : Type i} (f : A ≃ B) → Type j)
  (d : (A : Type i) → P (ide A)) {A B : Type i} (f : A ≃ B)
  → P f
equiv-induction {i} {j} P d f =
  transport P (coe-equiv-β f)
    (aux P d (ua f)) where

  aux : ∀ {j} (P : {A : Type i} {B : Type i} (f : A ≃ B) → Type j)
    (d : (A : Type i) → P (ide A)) {A B : Type i} (p : A == B)
    → P (coe-equiv p)
  aux P d idp = d _

{- Univalence for pointed types -}
abstract
  ⊙ua : ∀ {i} {X Y : Ptd i} → X ⊙≃ Y → X == Y
  ⊙ua ((f , p) , ie) = ptd= (ua (f , ie)) (↓-idf-ua-in (f , ie) p)

  ⊙ua-equiv : ∀ {i} {X Y : Ptd i} → (X ⊙≃ Y) ≃ (X == Y)
  ⊙ua-equiv {X = X} {Y = Y} =
    (X ⊙≃ Y)
      ≃⟨ Σ₂-×-comm ⟩
    _
      ≃⟨ Σ-emap-r (λ u → pre∙-equiv (coe-β u (pt X))) ⟩
    (Σ (de⊙ X ≃ de⊙ Y) (λ u → coe (ua u) (pt X) == (pt Y)))
      ≃⟨ Σ-emap-l _ ua-equiv ⟩
    (Σ (de⊙ X == de⊙ Y) (λ eq → coe eq (pt X) == (pt Y)))
      ≃⟨ (⊙==-Σ-== (pt X) (pt Y)) ⁻¹ ⟩
    (X == Y)
      ≃∎


{- Path type level -}
instance
  ≃-level : ∀ {i j} {n : ℕ₋₂} {A : Type i} {B : Type j}
    → (has-level n A → has-level n B → has-level n (A ≃ B))
  ≃-level {n = ⟨-2⟩} = ≃-contr
  ≃-level {n = S n} pA pB = Σ-level (Π-level (cst pB)) (λ _ → prop-has-level-S is-equiv-is-prop)

  universe-=-level : ∀ {i} {n : ℕ₋₂} {A B : Type i}
    → (has-level n A → has-level n B → has-level n (A == B))
  universe-=-level pA pB = equiv-preserves-level ua-equiv {{≃-level pA pB}}