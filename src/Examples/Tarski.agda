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

lfpᶜ-eq : Allᵖ (λ q → F q ＝ q) lfpᶜ
lfpᶜ-eq κ =
  to-induction _>_ wf->
    (λ a → a ≤ F a → Acc _>_ a → gAllᵖ κ (λ q → F q ＝ q) (iterᵏ a))
    go bot (≤-bot (F bot)) (wf-> bot)
  where
  go : (x : A)
     → ((y : A) → y > x → y ≤ F y → Acc _>_ y → gAllᵖ κ (λ q → F q ＝ q) (iterᵏ y))
     → x ≤ F x → Acc _>_ x → gAllᵖ κ (λ q → F q ＝ q) (iterᵏ x)
  go x ih pre (acc rec) with x ≟ F x
  ... | yes e = gAll-now (sym e)
  ... | no ne =
    gAll-later λ α →
      transport (λ i → gAllᵖ κ (λ q → F q ＝ q) (pfix iterᵏ-body (~ i) α (F x))) $
      ih (F x) (ne ∘ sym , pre) (Fmono x (F x) pre) (rec (F x) (ne ∘ sym , pre))

lfpᶜ-least : ∀ z → F z ＝ z → Allᵖ (_≤ z) lfpᶜ
lfpᶜ-least z fz κ =
  to-induction _>_ wf->
    (λ a → a ≤ F a → Acc _>_ a → a ≤ z → gAllᵖ κ (_≤ z) (iterᵏ a))
    go bot (≤-bot (F bot)) (wf-> bot) (≤-bot z)
  where
  go : (a : A)
     → ((b : A) → b > a → b ≤ F b → Acc _>_ b → b ≤ z → gAllᵖ κ (_≤ z) (iterᵏ b))
     → a ≤ F a → Acc _>_ a → a ≤ z → gAllᵖ κ (_≤ z) (iterᵏ a)
  go a ih l (acc rec) la with a ≟ F a
  ... | yes e = gAll-now la
  ... | no ne =
    gAll-later λ α →
      transport (λ i → gAllᵖ κ (_≤ z) (pfix iterᵏ-body (~ i) α (F a))) $
      ih (F a) (ne ∘ sym , l) (Fmono a (F a) l) (rec (F a) (ne ∘ sym , l)) (subst (F a ≤_) fz (Fmono a z la))
