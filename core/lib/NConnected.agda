{-
This file is a variation on the library HoTT-Agda,
written by Leclerc L.
-}

{-# OPTIONS --without-K --warning ignore #-}

module lib.NConnected where

open import lib.Base
open import lib.types.Truncation
open import lib.Function
open import lib.NType
open import lib.Equivalence
open import lib.PathGroupoid
open import lib.types.Sigma
open import lib.Funext
open import lib.types.Pi
open import lib.Equivalence2
open import lib.types.TLevel
open import lib.PathOver
open import lib.types.Paths

{- Recursive definition of n-connectedness -}

is_connected : ∀ {i} → ℕ₋₂ → (Type i) → (Type i)
is ⟨-2⟩ connected A = Lift ⊤
is (S n) connected A =
  ∥ A ∥ × ((a₀ a₁ : A) → is n connected (a₀ == a₁))

{- Proofs of several lemmas about n-connectedness -}

is-connected-apply : ∀ {i} {A : Type i} {n : ℕ₋₂}
  → is (S n) connected A
  → (x y : A)
  → is n connected (x == y)
is-connected-apply = snd

lemma-1-0-1 : 
  ∀ {i j} (A : Type i) (B : Type j) (n : ℕ₋₂)
  → is n connected A → has-level n B → is-equiv (λ (b : B) (_ : A) → b)

lemma-1-0-1 A B ⟨-2⟩ _ is-contr-B = is-eq
  (λ b _ → b)
  (λ _ → contr-center is-contr-B)
  (λ f → contr-has-all-paths {{weak-λ= (cst is-contr-B)}} _ _)
  (λ b → contr-path is-contr-B b)

lemma-1-0-1 A B (S n) (merely-A , hA) hB = 
  ∥⋅∥-rec is-equiv-is-prop lemma merely-A
  where
    q : (f : A → B) (a x : A) → f a == f x
    q f a x = is-equiv.g (lemma-1-0-1 (a == x) (f a == f x) n (hA _ _) (has-level-apply hB _ _)) (ap f)

    lemma : A → is-equiv (λ (b : B) (_ : A) → b)
    lemma a = is-eq
      (λ b _ → b)
      (λ f → f a)
      (λ f → λ= (q f a))
      λ a → idp

lemma-1-0-2 :
  ∀ {i j} (A : Type i) (P : A → Type j) (a : A) (n : ℕ₋₂)
  → is (S n) connected A → ((a : A) → has-level n (P a))
    → is-equiv (λ (f : Π A P) → f a)

lemma-1-0-2 A P a n hA hP = _∘ise_ {f = λ f → (λ (x : A) (_ : a == x) → f x)} {g = λ f → f a idp}
  (is-eq _ (λ d x p → J _ d p) (λ b → idp) λ φ → λ= λ x → λ= λ{ idp → idp }) 
  (snd (Π-emap-r λ x → cst , lemma-1-0-1 _ _ n (snd hA a x) (hP x)))

-- We need a lemma-1-0-3-0 in order to run the induction case

lemma-1-0-3-0 :
  ∀ {i j} (A : Type i) (P : A → Type j) (s t : Π A P) (a : A) (b : P a) 
   (q : t a == b) (p : s a == b)
  → Σ (s ~ t) (λ γ → γ a == p ∙ ! q) ≃ ((s , p) == (t , q))
lemma-1-0-3-0 A P s t a .(t a) idp p = 
  Σ (s ~ t) (λ γ → γ a == p ∙ ! idp) 
    ≃⟨ Σ-emap-r (λ γ → post∙-equiv (∙-unit-r _)) ⟩
  Σ (s ~ t) (λ γ → γ a == p)
    ≃⟨ Σ-emap-r (λ γ → pre∙-equiv (app=-β γ a)) ⟩
  Σ (s ~ t) (λ γ → app= (λ= γ) a == p)
    ≃⟨ Σ-emap-l (λ γ → app= γ a == p) λ=-equiv ⟩
  Σ (s == t) (λ γ → app= γ a == p)
    ≃⟨ Σ-emap-r (λ γ → !-equiv) ⟩
  Σ (s == t) (λ γ → p == app= γ a)
    ≃⟨ Σ-emap-r (λ γ → post∙-equiv (! (∙-unit-r _))) ⟩
  Σ (s == t) (λ γ → p == ap (λ v → v a) γ ∙ idp)
    ≃⟨ Σ-emap-r (λ γ → ↓-app=cst-econv) ⟩
  Σ (s == t) (λ γ → p == idp [ (λ v → v a == t a) ↓ γ ] )
    ≃⟨ =Σ-econv (s , p) (t , idp) ⟩
  (s , p) == (t , idp)
    ≃∎

lemma-1-0-3 :
  ∀ {i j} (A : Type i) (P : A → Type j) (a : A) (b : P a) (n : ℕ₋₂) (k : ℕ₋₂)
  → is (S n) connected A → ((x : A) → has-level (k +2+ n) (P x))
    → has-level k (Σ (Π A P) (λ s → s a == b))

lemma-1-0-3 A P a b n ⟨-2⟩ hA hP = equiv-is-contr-map (lemma-1-0-2 _ _ _ _ hA hP) b

lemma-1-0-3 A P a b n (S k) hA hP = has-level-in
  (λ{ (s , p) (t , q) → equiv-preserves-level
    (lemma-1-0-3-0 A P s t a b q p)
    {{lemma-1-0-3 A (λ (x : A) → s x == t x) a (p ∙ (! q)) n k hA λ x → has-level-apply (hP x) _ _}}
  })

is-set-⊙≃-n-connected-Sn-type :
  ∀ {i j} {A : Type i} {B : Type j} {n : TLevel}
  → (is n connected A)
  → (has-level (S n) B)
  → (a : A) (b : B)
  → is-set (⊙[ A , a ] ⊙≃ ⊙[ B , b ])
is-set-⊙≃-n-connected-Sn-type {A = A} {B = B} {⟨-2⟩}
  _ is-prop-B a b = Σ-level 
  (raise-level _ (Σ-level (Π-level (cst is-prop-B)) λ f → raise-level _ (has-level-apply is-prop-B _ _))) 
  λ ⊙f → raise-level _ is-equiv-is-prop
is-set-⊙≃-n-connected-Sn-type {A = A} {B = B} {S n}
  cA lB a b = Σ-level (lemma-1-0-3 A (cst B) a b n _ cA (cst lB)) 
  λ ⊙f → raise-level _ is-equiv-is-prop

is-Sn-connected-is-n-connected : ∀ {i} {A : Type i} {n}
  → is (S n) connected A
  → is n connected A
is-Sn-connected-is-n-connected {n = ⟨-2⟩} = (λ _ → lift unit)
is-Sn-connected-is-n-connected {n = S k} SSncA =
  fst SSncA , λ a₀ a₁ → is-Sn-connected-is-n-connected (snd SSncA a₀ a₁)

is-<T-connected : ∀ {i} {A : Type i} {k n : ℕ₋₂}
  → k <T n
  → is n connected A 
  → is k connected A
is-<T-connected ltS = is-Sn-connected-is-n-connected
is-<T-connected (ltSR m<n) SncA = is-<T-connected m<n (is-Sn-connected-is-n-connected SncA)

is-connected-is-prop : ∀ {i} {A : Type i} {n : ℕ₋₂}
  → is-prop (is n connected A)
is-connected-is-prop {A = A} {⟨-2⟩} = equiv-preserves-level (lower-equiv ⁻¹)
is-connected-is-prop {A = A} {S n} = ×-level is-prop-∥⋅∥ 
  (Π-level (λ _ → Π-level λ _ → is-connected-is-prop))

equiv-preserves-connectedness :  
  ∀ {i j} {A : Type i} {B : Type j} {n : ℕ₋₂}
  → (is n connected A)
  → (A ≃ B)
  → (is n connected B)
equiv-preserves-connectedness
  {n = ⟨-2⟩} _ _ = lift unit
equiv-preserves-connectedness {A = A} {B = B}
  {n = S n} hA A≃B = ∥⋅∥-rec is-prop-∥⋅∥ ([_] ∘ –> A≃B) (fst hA) , 
  λ b₀ b₁ → equiv-preserves-connectedness 
  ((snd hA) (<– A≃B b₀) (<– A≃B b₁)) (ap-equiv (A≃B ⁻¹) b₀ b₁ ⁻¹)