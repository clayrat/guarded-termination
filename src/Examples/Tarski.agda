{-# OPTIONS --guarded #-}

import Prelude as P hiding (_<_ ; Tactic-bishop-finite ; ord→is-discrete)
open P
open import Data.Empty
open import Data.Bool
open import Data.Dec
open import Data.Nat
open import Correspondences.Wellfounded

open import Later
open import Clocked.Partial
open import Clocked.Partial.Converges
open import Clocked.Partial.All

module Examples.Tarski
  {ℓ ℓ′ : Level}
  {A : 𝒰 ℓ}
  ⦃ dA : is-discrete A ⦄
  (bot : A)
  (_≤_ : Corr² (A , A) ℓ′)
  (≤-bot : ∀ x → bot ≤ x)
  (wf-> : Wf λ x y → (x ≠ y) × (y ≤ x))
  {F : A → A}
  (Fmono : ∀ x y → x ≤ y → F x ≤ F y)
  where

private variable
  κ : Cl

_>_ : Corr² (A , A) (ℓ ⊔ ℓ′)
x > y = (x ≠ y) × (y ≤ x)

-- well-founded

iterᵗᵃ : (x : A) → x ≤ F x → Acc _>_ x → A
iterᵗᵃ x pre (acc rec) with x ≟ F x
... | yes e = x
... | no ne = iterᵗᵃ (F x) (Fmono x (F x) pre) (rec (F x) (ne ∘ sym , pre))

lfp : A
lfp = iterᵗᵃ bot (≤-bot (F bot)) (wf-> bot)

lfp-eq : F lfp ＝ lfp
lfp-eq =
  to-induction _>_ wf->
    (λ a → (l : a ≤ F a) → (ac : Acc _>_ a) → F (iterᵗᵃ a l ac) ＝ iterᵗᵃ a l ac)
    go bot (≤-bot (F bot)) (wf-> bot)
  where
  go : (a : A)
     → ((b : A) → b > a → (l : b ≤ F b) → (ac : Acc _>_ b) → F (iterᵗᵃ b l ac) ＝ iterᵗᵃ b l ac)
     → (l : a ≤ F a) → (ac : Acc _>_ a)
     → F (iterᵗᵃ a l ac) ＝ iterᵗᵃ a l ac
  go a ih l (acc rec) with a ≟ F a
  ... | yes e = sym e
  ... | no ne = ih (F a) (ne ∘ sym , l) (Fmono a (F a) l) (rec (F a) (ne ∘ sym , l))

lfp-least : ∀ z → F z ＝ z → lfp ≤ z
lfp-least z fz =
  to-induction _>_ wf->
    (λ a → (l : a ≤ F a) → (ac : Acc _>_ a) → a ≤ z → iterᵗᵃ a l ac ≤ z)
    go bot (≤-bot (F bot)) (wf-> bot) (≤-bot z)
  where
  go : (a : A)
     → ((b : A) → b > a → (l : b ≤ F b) → (ac : Acc _>_ b) → b ≤ z → iterᵗᵃ b l ac ≤ z)
     → (l : a ≤ F a) → (ac : Acc _>_ a) → a ≤ z → iterᵗᵃ a l ac ≤ z
  go a ih l (acc rec) la with a ≟ F a
  ... | yes e = la
  ... | no ne = ih (F a) (ne ∘ sym , l) (Fmono a (F a) l) (rec (F a) (ne ∘ sym , l)) (subst (F a ≤_) fz (Fmono a z la))

-- coinductive

iterᵏ-body : ▹ κ (A → gPart κ A) → A → gPart κ A
iterᵏ-body i▹ x = if ⌊ x ≟ F x ⌋ then now x else later (i▹ ⊛ next (F x))

iterᵏ : A → gPart κ A
iterᵏ = fix iterᵏ-body

iterᶜ : A → Part A
iterᶜ x κ = iterᵏ x

lfpᵏ : gPart κ A
lfpᵏ = iterᵏ bot

lfpᶜ : Part A
lfpᶜ κ = lfpᵏ

-- convergence and properties

iterᶜ-acc⇓ : (x : A) → x ≤ F x → Acc _>_ x → iterᶜ x ⇓
iterᶜ-acc⇓ x pre (acc rec) with x ≟ F x
... | yes e = x , ∣ 0 , refl ∣₁
... | no ne =
  second
    (map
       λ where
          (m , e) →
            suc m , fun-ext λ κ →
                       ap (λ q → later (q ⊛ next (F x))) (pfix iterᵏ-body)
                     ∙ ap δᵏ (happly e κ))
    (iterᶜ-acc⇓ (F x) (Fmono x (F x) pre) (rec (F x) (ne ∘ sym , pre)))

iterᶜ⇓ : (x : A) → x ≤ F x → iterᶜ x ⇓
iterᶜ⇓ x pre = iterᶜ-acc⇓ x pre (wf-> x)

lfpᶜ⇓ : lfpᶜ ⇓
lfpᶜ⇓ = iterᶜ⇓ bot (≤-bot (F bot))

-- we can decouple property proofs from the Acc machinery
iterᶜ-eq : (x : A) → x ≤ F x → Allᵖ (λ q → F q ＝ q) (iterᶜ x)
iterᶜ-eq x le κ = fix {k = κ} go x le
  where
  go : ▹ κ ((x : A) → x ≤ F x → gAllᵖ κ (λ q → F q ＝ q) (iterᵏ x))
     → (x : A) → x ≤ F x → gAllᵖ κ (λ q → F q ＝ q) (iterᵏ x)
  go ih▹ x le with x ≟ F x
  ... | yes e = gAll-now (sym e)
  ... | no _  =
    gAll-later λ α →
      transport (λ i → gAllᵖ κ (λ q → F q ＝ q) (pfix iterᵏ-body (~ i) α (F x))) $
      ih▹ α (F x) (Fmono x (F x) le)

lfpᶜ-eq : Allᵖ (λ q → F q ＝ q) lfpᶜ
lfpᶜ-eq = iterᶜ-eq bot (≤-bot (F bot))

iterᶜ-least : ∀ z → F z ＝ z
            → ∀ x → x ≤ z → Allᵖ (_≤ z) (iterᶜ x)
iterᶜ-least z ze x le κ = fix {k = κ} go x le
  where
  go : ▹ κ ((x : A) → x ≤ z → gAllᵖ κ (_≤ z) (iterᵏ x))
     → (x : A) → x ≤ z → gAllᵖ κ (_≤ z) (iterᵏ x)
  go ih▹ x xz with x ≟ F x
  ... | yes _ = gAll-now xz
  ... | no ne =
    gAll-later λ α →
      transport (λ i → gAllᵖ κ (_≤ z) (pfix iterᵏ-body (~ i) α (F x))) $
      ih▹ α (F x) (subst (F x ≤_) ze (Fmono x z xz))

lfpᶜ-least : ∀ z → F z ＝ z → Allᵖ (_≤ z) lfpᶜ
lfpᶜ-least z ze = iterᶜ-least z ze bot (≤-bot z)
