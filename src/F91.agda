{-# OPTIONS --guarded #-}
module F91 where

open import Prelude hiding (_<_)
open import Data.Empty
open import Data.Nat
open import Data.Bool
open import Data.Dec
open import Data.Nat.Order.Base
open import Correspondences.Wellfounded

open import Later
open import Clocked.Partial
open import Clocked.Partial.Converges

private variable
  κ : Cl

-- McCarthy's function

f91ᵏ-body : ▹ κ (ℕ → gPart κ ℕ) → ℕ → gPart κ ℕ
f91ᵏ-body f▹ n =
  if n ≤ᵇ 100
    then later ((_>>=ᵏ_) ⍉ (f▹ ⊛ next (11 + n)) ⊛ f▹)
    else now (n ∸ 10)

f91ᵏ : ℕ → gPart κ ℕ
f91ᵏ = fix f91ᵏ-body

f91 : ℕ → Part ℕ
f91 n k = f91ᵏ n

-- termination

f91-suc-90≤n≤100 : ∀ n k
                 → 90 ≤ n → n ≤ 100
                 → f91 (suc n) ⇓ᵖ k
                 → f91 n ⇓ᵖ k
f91-suc-90≤n≤100 n k n≥90 n≤100 =
  map λ where
    (m , e) →
        suc m
      , (fun-ext λ κ →
          f91ᵏ n
            ＝⟨ ap (λ q → q n) (fix-path f91ᵏ-body) ⟩
          (if ⌜ n ≤ᵇ 100 ⌝ then δᵏ (f91ᵏ (11 + n) >>=ᵏ f91ᵏ) else now (n ∸ 10))
            ＝⟨ ap! (reflects-true (≤-reflects n 100) n≤100) ⟩
          (δᵏ (f91ᵏ (11 + n) >>=ᵏ f91ᵏ))
            ＝⟨ ap (λ q → (δᵏ (q (11 + n) >>=ᵏ f91ᵏ))) (fix-path f91ᵏ-body) ⟩
          δᵏ ((if ⌜ n ≤ᵇ 89 ⌝ then δᵏ (f91ᵏ (22 + n) >>=ᵏ f91ᵏ) else now (1 + n)) >>=ᵏ f91ᵏ)
            ＝⟨ ap! (reflects-false (≤-reflects n 89) (<→≱ (<≃suc≤ .fst n≥90))) ⟩
          δᵏ (f91ᵏ (suc n))
            ＝⟨ ap δᵏ (happly e κ) ⟩
          delay-by (suc m) k κ
            ∎)

f91＝91-90≤n≤100 : ∀ n
                 → 90 ≤ n → n ≤ 100
                 → f91 n ⇓ᵖ 91
f91＝91-90≤n≤100 = {!!}
