{-
This file is a variation on the library HoTT-Agda,
written by Leclerc L.
-}

{-# OPTIONS --without-K --warning ignore #-}

open import lib.Base
open import lib.Equivalence
open import lib.Function
open import lib.Funext
open import lib.NConnected
open import lib.NType
open import lib.PathOver
open import lib.PathGroupoid
open import lib.PathFunctor
open import lib.PathSeq
open import lib.types.Int
open import lib.types.LoopSpace
open import lib.types.Nat
open import lib.types.Paths
open import lib.types.Pointed
open import lib.types.Sigma
open import lib.types.TLevel

module lib.Homogeneous where

{- Definition of homogeneous types -}

homogeneous-struct : ∀ {i} (A : Type i) → Type (lsucc i)
homogeneous-struct A = (a₀ a₁ : A) → ⊙[ A , a₀ ] == ⊙[ A , a₁ ]

homogeneous-struct-Ω : ∀ {i} (A : Ptd i) → homogeneous-struct (Ω A)
homogeneous-struct-Ω A p q = 
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
  → (hA : homogeneous-struct A)
  → (a₀ a₁ : A) (p : a₀ == a₁)
  → ap ⊙[ A ,_] p == ! (hA a₀ a₀) ∙ (hA a₀ a₁)
lemma-1-0-4-1 {A = A} hA a₀ .a₀ idp = ! (!-inv-l (hA a₀ a₀))

lemma-1-0-4-2 : ∀ {i} {A : Type i}
  → homogeneous-struct A
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

fun-to-homogeneous :
  ∀ {i j} (A : Type i) (B : Type j) (a : A) (b : B)
  → (homogeneous-struct B)
  → (A → B) ≃ B × (⊙[ A , a ] ⊙→ ⊙[ B , b ])
fun-to-homogeneous A B a b hB = _ , is-eq to from to-from from-to
  where
    to : (A → B) → B × (⊙[ A , a ] ⊙→ ⊙[ B , b ])
    to f = (f a , (⊙coe (hB (f a) b)) ⊙∘ (f , idp))

    from : B × (⊙[ A , a ] ⊙→ ⊙[ B , b ]) → (A → B)
    from (y , ⊙f) = fst ((⊙coe (! (hB y b))) ⊙∘ ⊙f)
      where f = fst ⊙f

    lemma : ∀ y ⊙f → from (y , ⊙f) a == y
    lemma y ⊙f = ap (coe (ap de⊙ (! (hB y b)))) (snd ⊙f) ∙ ⊙coe-pt (! (hB y b))

    to-from : (p : B × (⊙[ A , a ] ⊙→ ⊙[ B , b ])) → (to (from p) == p)
    to-from (y , f , idp) = pair= ((⊙coe-pt (! (hB y (f a)))))
      (↓-cst-in (lemma-1-0-4-2 hB (f a) a _ f (λ= (λ x → eq x)) _ idp))
      where private
        eq : (x : A) 
          → (fst (⊙coe (hB (from (y , f , idp) a) (f a))) ∘
            from (y , f , idp)) x
          == f x
        eq x =
          (fst (⊙coe (hB (from (y , f , idp) a) (f a))) ∘
            from (y , f , idp)) x
            =⟨ ap (λ u → ((fst (⊙coe (hB u (f a))) ∘ from (y , f , idp)) x)) (lemma y (f , idp)) ⟩
          (fst (⊙coe (hB y (f a))) ∘ from (y , f , idp)) x
            =⟨ ap (fst (⊙coe (hB y (f a)))) (coe-ap-! de⊙ (hB y (f a)) (f x)) ⟩
          coe (ap de⊙ (hB y (f a))) (coe! (ap de⊙ (hB y (f a))) (f x))
            =⟨ coe!-inv-r (ap de⊙ (hB y (f a))) (f x) ⟩
          f x
            =∎

    from-to : (f : A → B) → from (to f) == f
    from-to f = λ= λ x → (coe-ap-! de⊙ (hB (f a) b) 
      (coe (ap de⊙ (hB (f a) b)) (f x))) 
      ∙ coe!-inv-l ((ap de⊙ (hB (f a) b))) (f x)

{- Defining a weaker notion, maybe useful without ua -}

weak-homogeneous-struct : ∀ {i} (A : Type i) → Type i
weak-homogeneous-struct A = (a₀ a₁ : A) → ⊙[ A , a₀ ] ⊙≃ ⊙[ A , a₁ ]

homogeneous-struct-weak-homogeneous-struct :
  ∀ {i} {A : Type i}
  → (homogeneous-struct A) 
  → weak-homogeneous-struct A
homogeneous-struct-weak-homogeneous-struct {A = A} hA a₀ a₁ =
  transport (λ ⊙X → ⊙[ A , a₀ ] ⊙≃ ⊙X) (hA a₀ a₁) (⊙ide _)

weak-homogeneous-struct-Ω : ∀ {i} (A : Ptd i) → weak-homogeneous-struct (Ω A)
weak-homogeneous-struct-Ω = homogeneous-struct-weak-homogeneous-struct ∘ homogeneous-struct-Ω

weak-homogeneous-struct-n-connected-Sn-type :
  ∀ {i} {A : Type i} {n : ℕ} (0<n : 0 < n)
  → (is (⟨ n ⟩) connected A)
  → (has-level (S ⟨ n ⟩) A)
  → weak-homogeneous-struct A
weak-homogeneous-struct-n-connected-Sn-type {A = A} {n} (ltS) cA lA a = 
  is-equiv.g (lemma-1-0-2 A 
    (λ (x : A) → ⊙[ A , a ] ⊙≃ ⊙[ A , x ])
    a ⟨ 0 ⟩ cA (λ x → is-set-⊙≃-n-connected-Sn-type cA lA a x)) 
    (⊙ide _)
weak-homogeneous-struct-n-connected-Sn-type {A = A} {n = _} (ltSR k) cA lA a = 
  is-equiv.g (lemma-1-0-2 A 
    (λ (x : A) → ⊙[ A , a ] ⊙≃ ⊙[ A , x ])
    a ⟨ 0 ⟩ (is-<T-connected (<T-ap-S (⟨⟩-monotone-< k)) cA) (λ x → is-set-⊙≃-n-connected-Sn-type cA lA a x)) 
    (⊙ide _)

ℤ-weakly-homogeneous : weak-homogeneous-struct ℤ
ℤ-weakly-homogeneous m n = ((λ k → (k ℤ+ ℤ~ m) ℤ+ n) , computation₁ m n) , 
  is-eq _ ((λ k → (k ℤ+ ℤ~ n) ℤ+ m)) (computation₂ m n) (computation₂ n m)
  where abstract
    computation₁ : (m n : ℤ) → m ℤ+ ℤ~ m ℤ+ n == n
    computation₁ m n =
      m ℤ+ ℤ~ m ℤ+ n
        =⟨ ap (_ℤ+ n) (ℤ~-inv-r m) ⟩
      n
        =∎

    computation₂ : (m n k : ℤ) → (((k ℤ+ ℤ~ n) ℤ+ m) ℤ+ ℤ~ m) ℤ+ n == k
    computation₂ m n k =
      (((k ℤ+ ℤ~ n) ℤ+ m) ℤ+ ℤ~ m) ℤ+ n
        =⟨ ℤ+-assoc ((k ℤ+ ℤ~ n) ℤ+ m) (ℤ~ m) n ⟩
      ((k ℤ+ ℤ~ n) ℤ+ m) ℤ+ (ℤ~ m ℤ+ n)
        =⟨ ℤ+-assoc (k ℤ+ ℤ~ n) m (ℤ~ m ℤ+ n) ⟩
      (k ℤ+ ℤ~ n) ℤ+ (m ℤ+ (ℤ~ m ℤ+ n))
        =⟨ ap ((k ℤ+ ℤ~ n) ℤ+_) (! (ℤ+-assoc m (ℤ~ m) n)) ⟩
      (k ℤ+ ℤ~ n) ℤ+ ((m ℤ+ ℤ~ m) ℤ+ n)
        =⟨ ap (λ q → ((k ℤ+ ℤ~ n) ℤ+ (q ℤ+ n))) (ℤ~-inv-r m) ⟩
      (k ℤ+ ℤ~ n) ℤ+ n
        =⟨ ℤ+-assoc k (ℤ~ n) n ⟩
      k ℤ+ (ℤ~ n ℤ+ n)
        =⟨ ap (k ℤ+_) (ℤ~-inv-l n) ⟩
      k ℤ+ 0
        =⟨ ℤ+-unit-r k ⟩
      k
        =∎

coe-Ω-⊙[-,-] :
    ∀ {i} {A : Type i} {a₀ a₁ : A} 
  → (q : a₀ == a₁)
  → (p : a₀ == a₀)
  → coe (ap (Ω ∘ ⊙[ A ,_]) q) p == ! q ∙ p ∙' q
coe-Ω-⊙[-,-] idp p = idp

homogeneous→abelian :
    ∀ {i} {A : Type i}
  → homogeneous-struct A
  → (a₀ : A)
  → (p q : a₀ == a₀)
  → p ∙ q == q ∙ p
homogeneous→abelian {A = A} hA a₀ p q =
  ! (∙'=∙ p q) ∙ 
  (–>-is-inj (pre∙-equiv (! q))) _ _ (! (coe-Ω-⊙[-,-] q p) 
  ∙ ((ap (λ u → coe u p) (ap-∘ Ω ⊙[ A ,_] q ∙ ap (ap Ω) (lemma-1-0-4-1 hA _ _ q ∙ !-inv-l (hA a₀ a₀)))) 
  ∙ (ap (_∙ p) (! (!-inv-l q)))) 
  ∙ (∙-assoc (! q) q p))

module homogeneous-Aut
  {i : ULevel} {A : Type i}
  (hA : homogeneous-struct A)
  where
  
  ⊙Φ : (a₀ a₁ : A) → ⊙[ A , a₀ ] ⊙→ ⊙[ A , a₁ ]
  ⊙Φ a₀ a₁ = ⊙coe (! (hA a₀ a₀) ∙ (hA a₀ a₁))

  Φ : (a₀ a₁ : A) → (A → A)
  Φ a₀ a₁ = fst (⊙Φ a₀ a₁)

  is-equiv-Φ : (a₀ a₁ : A) → is-equiv (Φ a₀ a₁)
  is-equiv-Φ a₀ a₁ = snd (⊙coe-equiv (! (hA a₀ a₀) ∙ (hA a₀ a₁)))

  Φ-idf : (a₀ : A) → Φ a₀ a₀ == idf A
  Φ-idf a₀ = ap (coe ∘ (ap de⊙)) (!-inv-l (hA a₀ a₀))

  Φ-assoc : (a₀ a₁ a₂ : A) → a₀ == a₁
    → Φ a₀ a₂ ∘ Φ a₀ a₁ == Φ a₀ (Φ a₀ a₂ a₁)
  Φ-assoc a₀ .a₀ a₂ idp = 
    ap (Φ a₀ a₂ ∘_) (Φ-idf a₀)
    ∙ λ= (λ _ → idp) ∙ (ap (Φ a₀) (! (snd (⊙Φ a₀ a₂)))) 

  -- Φ-comm : (a₀ a₁ a₂ : A) → a₀ == a₁
  --   → Φ a₀ a₂ ∘ Φ a₀ a₁ == Φ a₀ a₁ ∘ Φ a₀ a₂

