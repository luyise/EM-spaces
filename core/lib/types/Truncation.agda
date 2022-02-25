{- this part is a variation on the library
HoTT-Agda edited by Leclerc L. -}

{-# OPTIONS --without-K #-}

module lib.types.Truncation where

open import lib.Base
open import lib.Equivalence
open import lib.Equivalence2
open import lib.NType
open import lib.types.Sigma

{- Postulating the existence of a propositional truncation -}

module _ {i} where

  postulate 
    ∥_∥ : Type i → Type i
    [_] : {A : Type i} → A → ∥ A ∥
    is-prop-∥⋅∥ : {A : Type i} → is-prop (∥ A ∥)
    ∥⋅∥-elim : {A : Type i} {j : ULevel} {P : ∥ A ∥ → Type j} → ((a : ∥ A ∥) → is-prop (P a)) → ((a : A) → P [ a ]) → ((a : ∥ A ∥) → P a)
    [⋅]-β : {A : Type i} {j : ULevel} {P : ∥ A ∥ → Type j} → {p : (a : ∥ A ∥) → is-prop (P a)} → (f : (a : A) → P [ a ]) → (a : A) → (∥⋅∥-elim p f [ a ] == f a)

  ∥⋅∥-rec : {A : Type i} {j : ULevel} {P : Type j} → (is-prop P) → (A → P) → ∥ A ∥ → P
  ∥⋅∥-rec {A=A} {j=j} {P=P} p = ∥⋅∥-elim (cst p)
  [⋅]-β' : {A : Type i} {j : ULevel} {P : Type j} → {p : is-prop P} → (f : A → P) → (a : A) → (∥⋅∥-rec p f [ a ] == f a)
  [⋅]-β' = [⋅]-β

  Trunc : Type i → Type i
  Trunc = ∥_∥
  is-prop-Trunc : {A : Type i} → is-prop (∥ A ∥)
  is-prop-Trunc = is-prop-∥⋅∥
  Trunc-elim : {A : Type i} {j : ULevel} {P : ∥ A ∥ → Type j} → ((a : ∥ A ∥) → is-prop (P a)) → ((a : A) → P [ a ]) → ((a : ∥ A ∥) → P a)
  Trunc-elim = ∥⋅∥-elim
  Trunc-rec : {A : Type i} {j : ULevel} {P : Type j} → (is-prop P) → (A → P) → ∥ A ∥ → P
  Trunc-rec = ∥⋅∥-rec

⊙Trunc : ∀ {i} → Ptd i → Ptd i
⊙Trunc ⊙[ A , a ] = ⊙[ Trunc A , [ a ] ]

⊙Trunc-rec : ∀ {i j} {X : Ptd i} {Y : Ptd j} {{is-prop-Y : is-prop (de⊙ Y)}}
  → X ⊙→ Y
  → ⊙Trunc X ⊙→ Y
⊙Trunc-rec {{is-prop-Y}} f = (Trunc-rec is-prop-Y (fst f) , [⋅]-β' (fst f) _ ∙ (snd f))

is-equiv-∥⋅∥ : ∀ {i j} {X : Type i} {Y : Type j}
  → {{is-prop-Y : is-prop Y}}
  → {f : X → Y}
  → is-equiv f 
  → is-equiv (∥⋅∥-rec is-prop-Y f)
is-equiv-∥⋅∥ {X = X} {Y = Y} {{is-prop-Y}} {f}
  is-equiv-f = contr-map-is-equiv 
    λ y → Σ-level 
      (inhab-prop-is-contr [ is-equiv.g is-equiv-f y ] {{is-prop-∥⋅∥}}) 
      λ x → has-level-apply is-prop-Y _ _

≃-∥⋅∥ : ∀ {i j} {X : Type i} {Y : Type j}
  → (X ≃ Y)
  → (∥ X ∥ ≃ ∥ Y ∥)
≃-∥⋅∥ {X = X} {Y = Y} (f , is-equiv-f) = 
  (∥⋅∥-rec is-prop-∥⋅∥ ([_] ∘ f)) , 
  is-eq _ ((∥⋅∥-rec is-prop-∥⋅∥ ([_] ∘ (is-equiv.g is-equiv-f)))) 
  (λ _ → prop-path is-prop-∥⋅∥ _ _) (λ _ → prop-path is-prop-∥⋅∥ _ _)