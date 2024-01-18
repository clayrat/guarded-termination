{-# OPTIONS --guarded #-}
module Examples.ZeroOut where

open import Prelude

open import Later
open import Clocked.Partial
open import Clocked.Partial.Converges

private variable
  κ : Cl

{-
zeroOut : ℕ → ℕ
zeroOut  zero   = zero
zeroOut (suc n) = zeroOut (zeroOut n)
-}

zeroOutᵏ-body : ▹ κ (ℕ → gPart κ ℕ) → ℕ → gPart κ ℕ
zeroOutᵏ-body z▹  zero   = now zero
zeroOutᵏ-body z▹ (suc n) = later ((_=<<ᵏ_) ⍉ z▹ ⊛ (z▹ ⊛ next n))

zeroOutᵏ : ℕ → gPart κ ℕ
zeroOutᵏ = fix zeroOutᵏ-body

zeroOut : ℕ → Part ℕ
zeroOut n κ = zeroOutᵏ n

-- termination

zeroOut⇓ : ∀ n → zeroOut n ⇓ᵖ 0
zeroOut⇓  zero   = ∣ 0 , refl ∣₁
zeroOut⇓ (suc n) =
  map (λ where
           (k , e) →
             (suc k) , (fun-ext λ κ →
                                   zeroOutᵏ (suc n)
                                     ＝⟨ ap (λ q → q (suc n)) (fix-path zeroOutᵏ-body)  ⟩
                                   δᵏ (zeroOutᵏ =<<ᵏ ⌜ zeroOutᵏ n ⌝)
                                     ＝⟨ ap! (happly e κ) ⟩
                                   δᵏ (zeroOutᵏ =<<ᵏ delay-byᵏ k 0)
                                     ＝⟨ ap δᵏ (delay-by-bindᵏ zeroOutᵏ 0 k) ⟩
                                   delay-byᵏ (suc k) 0
                                     ∎))
    (zeroOut⇓ n)
