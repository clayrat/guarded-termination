{-# OPTIONS --guarded #-}
module Examples.Mergesort where

open import Prelude hiding (_<_)
open import Data.Bool
open import Data.Dec
open import Data.Nat
open import Data.Nat.Order.Computational
open import Data.List
open import Correspondences.Wellfounded

open import Later
open import Clocked.Partial
open import Clocked.Partial.Converges

private variable
  κ : Cl
  ℓ : Level
  A : 𝒰 ℓ

split : List A → List A × List A
split  []         = [] , []
split (x ∷ [])    = x ∷ [] , []
split (x ∷ y ∷ l) =
  let xs , ys = split l in
  x ∷ xs , y ∷ ys

-- both should actually be in [ |l|/2↓ , |l|/2↑ ]
split-lengths : (l : List A)
              → let xs , ys = split l in
              (length xs ≤ length l) × (length ys ≤ length l)
split-lengths []          = tt , tt
split-lengths (x ∷ [])    = tt , tt
split-lengths (x ∷ y ∷ l) =
  let q , r = split-lengths l in
    ≤-trans {m = length (split l .fst)} q (≤-ascend {n = length l})
  , ≤-trans {m = length (split l .snd)} r (≤-ascend {n = length l})

merge : ⦃ oA : Ord A ⦄
      → List A → List A → List A
merge []          ys      = ys
merge xs@(_ ∷ _)  []      = xs
merge (x ∷ xs)   (y ∷ ys) =
  if ⌊ x ≤? y ⌋<
    then x ∷ merge xs (y ∷ ys)
    else y ∷ merge (x ∷ xs) ys

{-
mergesort : ⦃ oA : Ord A ⦄
          → List A → List A
mergesort []          = []
mergesort (x ∷ [])    = x ∷ []
mergesort (x ∷ y ∷ l) =
  let xs , ys = split l in
  merge (mergesort (x ∷ xs)) (mergesort (y ∷ xs))
-}

mergesort-bodyᵏ : ⦃ oA : Ord A ⦄
                → ▹ κ (List A → gPart κ (List A))
                → List A → gPart κ (List A)
mergesort-bodyᵏ m▹ []          = now []
mergesort-bodyᵏ m▹ (x ∷ [])    = now (x ∷ [])
mergesort-bodyᵏ m▹ (x ∷ y ∷ l) =
  let xs , ys = split l in
  map²ᵏ merge (later (m▹ ⊛ next (x ∷ xs))) (later (m▹ ⊛ next (y ∷ ys)))

mergesortᵏ : ⦃ oA : Ord A ⦄
           → List A → gPart κ (List A)
mergesortᵏ = fix mergesort-bodyᵏ

mergesort : ⦃ oA : Ord A ⦄
          → List A → Part (List A)
mergesort l κ = mergesortᵏ l

-- termination

mergesort⇓ : ⦃ oA : Ord A ⦄
           → ∀ l → Acc (λ x y → length x < length y) l → mergesort l ⇓
mergesort⇓ []           a            = [] , ∣ 0 , refl ∣₁
mergesort⇓ (x ∷ [])     a            = (x ∷ []) , ∣ 0 , refl ∣₁
mergesort⇓ {A} (x ∷ y ∷ l) (acc rec) =
  let xs , ys = split l
      xsl , ysl = split-lengths l
      q , q⇓ = mergesort⇓ {A = A} (x ∷ xs) (rec (x ∷ xs) xsl)
      r , r⇓ = mergesort⇓ {A = A} (y ∷ ys) (rec (y ∷ ys) ysl)
    in
    (merge q r)
  , map
      (λ where
           (zk , ze) →
              suc zk , (fun-ext λ κ →
                          mergesortᵏ (x ∷ y ∷ l)
                            ＝⟨ ap (λ q → q (x ∷ y ∷ l)) (fix-path mergesort-bodyᵏ) ⟩
                          map²ᵏ merge (δᵏ (mergesortᵏ (x ∷ xs))) (δᵏ (mergesortᵏ (y ∷ ys)))
                            ＝⟨⟩
                          δᵏ (map²ᵏ merge (mergesortᵏ (x ∷ xs)) (mergesortᵏ (y ∷ ys)))
                            ＝⟨ ap δᵏ (happly ze κ) ⟩
                          delay-byᵏ (suc zk) (merge q r)
                            ∎))
      (map²⇓ merge q⇓ r⇓)
