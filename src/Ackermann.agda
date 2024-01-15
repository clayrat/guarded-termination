{-# OPTIONS --guarded #-}
module Ackermann where

open import Prelude hiding (_<_)
open import Data.Empty
open import Data.Nat
open import Data.Nat.Order.Inductive
open import Data.Bool
open import Data.Dec
open import Data.Sum
open import Correspondences.Wellfounded
open import Meta.Variadic

open import Later
open import Clocked.Partial
open import Clocked.Partial.Converges

private variable
  κ : Cl

-- this works directly, but let's use lexicographic termination manually:
{-
ack : ℕ → ℕ → ℕ
ack    zero      n        = suc n
ack   (suc m-1)  zero     = ack m-1 1
ack m@(suc m-1) (suc n-1) = ack m-1 (ack m n-1)
-}

ackᵏ-body : ▹ κ (ℕ → ℕ → gPart κ ℕ) → ℕ → ℕ → gPart κ ℕ
ackᵏ-body a▹    zero      n        = now (suc n)
ackᵏ-body a▹   (suc m-1)  zero     = later (a▹ ⊛ next m-1 ⊛ next 1)
ackᵏ-body a▹ m@(suc m-1) (suc n-1) = later ((_>>=ᵏ_) ⍉ (a▹ ⊛ next m ⊛ next n-1) ⊛ (a▹ ⊛ next m-1))

ackᵏ : ℕ → ℕ → gPart κ ℕ
ackᵏ = fix ackᵏ-body

ack : ℕ → ℕ → Part ℕ
ack m n κ = ackᵏ m n

-- TODO upstream

private variable
  ℓ ℓ′ : Level
  A : 𝒰 ℓ
  B : 𝒰 ℓ′

data _×<_ (_<ₗ_ : Corr² (A , A) ℓ) (_<ᵣ_ : Corr² (B , B) ℓ′) : Corr² ((A × B) , (A × B)) (level-of-type A ⊔ level-of-type B ⊔ ℓ ⊔ ℓ′) where
  l< : ∀ {x₁ y₁ x₂ y₂} (x₁<x₂ : x₁ <ₗ x₂) → _×<_ _<ₗ_ _<ᵣ_ (x₁ , y₁) (x₂ , y₂)
  r≤ : ∀ {x y₁ y₂} (y₁<y₂ : y₁ <ᵣ y₂) → _×<_ _<ₗ_ _<ᵣ_ (x  , y₁) (x  , y₂)

×-wellFounded : {_<ₗ_ : Corr² (A , A) ℓ} {_≤ᵣ_ : Corr² (B , B) ℓ′}
              → Wf _<ₗ_ → Wf _≤ᵣ_ → Wf (_×<_ _<ₗ_ _≤ᵣ_)
×-wellFounded {_<ₗ_} {_≤ᵣ_} wl wr (x , y) =
  acc $ ×-acc (wl x) (wr y)
  where
  ×-acc : ∀ {x y}
        → Acc _<ₗ_ x → Acc _≤ᵣ_ y
        → ∀ ab → _×<_ _<ₗ_ _≤ᵣ_ ab (x , y) → Acc (_×<_ _<ₗ_ _≤ᵣ_) ab
  ×-acc (acc rx)  ay      (a , b) (l< x₁<x₂) = acc (×-acc (rx a x₁<x₂) (wr b))
  ×-acc  ax      (acc ry) (a , b) (r≤ y₁<y₂) = acc (×-acc ax (ry b y₁<y₂))

-- termination

ack⇓ : ∀ m n → Acc (_×<_ _<_ _<_) (m , n) → ack m n ⇓
ack⇓    zero      n      _        = (suc n) , ∣ 0 , refl ∣₁
ack⇓ m@(suc m-1)  zero  (acc rec) =
  second
    (λ {x} →
      map λ where
              (k , e) →
                 (suc k) , fun-ext λ κ →
                             ackᵏ m 0
                               ＝⟨ ap (λ q → q m 0) (fix-path ackᵏ-body) ⟩
                             δᵏ (ackᵏ m-1 1)
                               ＝⟨ ap δᵏ (happly e κ) ⟩
                             delay-byᵏ (suc k) x
                               ∎)
    (ack⇓ m-1 1 (rec (m-1 , 1) (l< (s≤s ≤-refl))))
ack⇓ m@(suc m-1) n@(suc n-1) (acc rec) =
  let (x , x⇓) = ack⇓ m n-1 (rec (m , n-1) (r≤ (s≤s ≤-refl))) in
  second
    (λ {x = y} →
       map² (λ where
                 (k1 , e1) (k2 , e2) →
                   suc (k1 + k2) , fun-ext λ κ →
                                     ackᵏ m n
                                       ＝⟨ ap (λ q → q m n) (fix-path ackᵏ-body) ⟩
                                     δᵏ (⌜ ackᵏ m n-1 ⌝ >>=ᵏ ackᵏ m-1)
                                       ＝⟨ ap! (happly e1 κ) ⟩
                                     δᵏ (delay-byᵏ k1 x >>=ᵏ ackᵏ m-1)
                                       ＝⟨ ap δᵏ (delay-by-bindᵏ (ackᵏ m-1) x k1) ⟩
                                     spinᵏ (suc k1) ⌜ ackᵏ m-1 x ⌝
                                       ＝⟨ ap! (happly e2 κ) ⟩
                                     spinᵏ (suc k1) (delay-byᵏ k2 y)
                                       ＝⟨ sym $ iter-add (suc k1) k2 δᵏ (now y) ⟩
                                     delay-byᵏ (suc (k1 + k2)) y
                                       ∎)
             x⇓)
    (ack⇓ m-1 x (rec (m-1 , x) (l< (s≤s ≤-refl))))
