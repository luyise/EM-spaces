{-# OPTIONS --without-K #-}

open import lib.Base
open import lib.Equivalence
open import lib.Function
open import lib.NType
open import lib.types.Truncation

module lib.Function2 where

is-surj : ∀ {i j} {A : Type i} {B : Type j} (f : A → B) → Type (lmax i j)
is-surj {A = A} f = ∀ b → Trunc (hfiber f b)

module _ {i j k} {A : Type i} {B : Type j} {C : Type k}
  {f : A → B} {g : B → C} where
  abstract
    ∘-is-surj : is-surj g → is-surj f → is-surj (g ∘ f)
    ∘-is-surj g-is-surj f-is-surj c =
      Trunc-rec is-prop-Trunc
        (λ{(b , gb=c) →
          Trunc-rec is-prop-Trunc
          (λ{(a , fa=b) → [ a , ap g fa=b ∙ gb=c ]})
          (f-is-surj b)})
        (g-is-surj c)

module _ {i j} {A : Type i} {B : Type j} {f : A → B} where
  abstract
    equiv-is-surj : is-equiv f → is-surj f
    equiv-is-surj f-is-equiv b = [ g b , f-g b ]
      where open is-equiv f-is-equiv