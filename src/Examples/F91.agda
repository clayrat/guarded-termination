{-# OPTIONS --guarded #-}
module Examples.F91 where

open import Prelude hiding (_<_)
open import Data.Empty
open import Data.Nat
open import Data.Nat.Order.Base
open import Data.Nat.DivMod
open import Data.Nat.DivMod.Base
open import Data.Bool
open import Data.Dec
open import Correspondences.Wellfounded

open import Later
open import Clocked.Partial
open import Clocked.Partial.Converges

private variable
  κ : Cl

-- McCarthy's function

{-
f91 : ℕ → ℕ
f91 n = if n ≤ᵇ 100 then f91 (f91 (11 + n)) else n ∸ 10
-}

f91ᵏ-body : ▹ κ (ℕ → gPart κ ℕ) → ℕ → gPart κ ℕ
f91ᵏ-body f▹ n =
  if n ≤ᵇ 100
    then later ((_=<<ᵏ_) ⍉ f▹ ⊛ (f▹ ⊛ next (11 + n)))
    else now (n ∸ 10)

f91ᵏ : ℕ → gPart κ ℕ
f91ᵏ = fix f91ᵏ-body

f91 : ℕ → Part ℕ
f91 n k = f91ᵏ n

-- termination

f91-n>100⇓ : ∀ n
           → 100 < n
           → f91 n ⇓ᵖ (n ∸ 10)
f91-n>100⇓ n n>100 =
 ∣ 0 , (fun-ext λ κ →
          f91ᵏ n
            ＝⟨ ap (λ q → q n) (fix-path f91ᵏ-body) ⟩
          (if ⌜ n ≤ᵇ 100 ⌝ then δᵏ (f91ᵏ =<<ᵏ f91ᵏ (11 + n)) else now (n ∸ 10))
            ＝⟨ ap! (¬⟦-⟧ᵇ≃false .fst $ true-reflects reflects-not $ reflects-false (≤-reflects n 100) (<≃≱ .fst n>100)) ⟩
          now (n ∸ 10)
            ∎) ∣₁

f91-suc-90≤n≤100 : ∀ n k
                 → 90 ≤ n → n ≤ 100
                 → f91 (suc n) ⇓ᵖ k
                 → f91 n ⇓ᵖ k
f91-suc-90≤n≤100 n k n≥90 n≤100 =
  map λ where
    (m , e) →
        suc m
      , fun-ext λ κ →
          f91ᵏ n
            ＝⟨ ap (λ q → q n) (fix-path f91ᵏ-body) ⟩
          (if ⌜ n ≤ᵇ 100 ⌝ then δᵏ (f91ᵏ =<<ᵏ f91ᵏ (11 + n)) else now (n ∸ 10))
            ＝⟨ ap! (⟦-⟧ᵇ≃true .fst $ reflects-true (≤-reflects n 100) n≤100) ⟩
          δᵏ (f91ᵏ =<<ᵏ f91ᵏ (11 + n))
            ＝⟨ ap (λ q → δᵏ (f91ᵏ =<<ᵏ q (11 + n))) (fix-path f91ᵏ-body) ⟩
          δᵏ (f91ᵏ =<<ᵏ (if ⌜ n ≤ᵇ 89 ⌝ then δᵏ (f91ᵏ =<<ᵏ f91ᵏ (22 + n)) else now (suc n)))
            ＝⟨ ap! (¬⟦-⟧ᵇ≃false .fst $ true-reflects reflects-not $ reflects-false (≤-reflects n 89) (<→≱ (<≃suc≤ .fst n≥90))) ⟩
          δᵏ (f91ᵏ (suc n))
            ＝⟨ ap δᵏ (happly e κ) ⟩
          delay-byᵏ (suc m) k
            ∎

f91＝91-100-n≤10 : ∀ n
                 → n ≤ 10
                 → f91 (100 ∸ n) ⇓ᵖ 91
f91＝91-100-n≤10  zero   n≤10 =
  f91-suc-90≤n≤100 100 91 (true-reflects (≤-reflects 90 100) tt) ≤-refl ∣ 0 , refl ∣₁
f91＝91-100-n≤10 (suc n) n≤10 =
  f91-suc-90≤n≤100 (99 ∸ n) 91
    (subst (90 ≤_) (m+[n∸p]＝m+n∸p 90 9 n (≤-peel n≤10)) $
     true-reflects (≤-reflects 90 (90 + (9 ∸ n))) tt)
    (≤-∸-l-≃ {p = n} .fst z≤) $
  subst (λ q → f91 q ⇓ᵖ 91)
        (sym $ suc-∸ n 99 (≤-trans ≤-ascend (≤-trans n≤10 (true-reflects (≤-reflects 10 99) tt)))) $
  f91＝91-100-n≤10 n (≤-trans ≤-ascend n≤10)

opaque
  unfolding _≤_
  f91＝91-90≤n≤100 : ∀ n
                   → 90 ≤ n → n ≤ 100
                   → f91 n ⇓ᵖ 91
  f91＝91-90≤n≤100 n n≥90 n≤100@(k , ek) =
    subst (λ q → f91 q ⇓ᵖ 91) (ap (_∸ k) (sym ek) ∙ +-cancel-∸-r n k) $
    f91＝91-100-n≤10 k $
    ≤-+≃2l {p = n} .fst $
    subst (_≤ n + 10) (sym ek) $
    subst (100 ≤_) (+-comm 10 n) $
    ((≤-+≃2l {p = 10} {m = 90} {n = n}) ₑ⁻¹) .fst n≥90

f91＝91-·11 : ∀ k n
            → k · 11 < 100
            → 90 ∸ k · 11 ≤ n → n ≤ 100 ∸ k · 11
            → f91 n ⇓ᵖ 91
f91＝91-·11  zero   n k11<100 n≥90-k11 n≤100-k11 = f91＝91-90≤n≤100 n n≥90-k11 n≤100-k11
f91＝91-·11 (suc k) n k11<100 n≥90-k11 n≤100-k11 =
  map² (λ where
            (s91 , e91) (s , e) →
               suc (s + s91)
             , fun-ext λ κ →
                 f91ᵏ n
                   ＝⟨ ap (λ q → q n) (fix-path f91ᵏ-body) ⟩
                 (if ⌜ n ≤ᵇ 100 ⌝ then δᵏ (f91ᵏ =<<ᵏ f91ᵏ (11 + n)) else now (n ∸ 10))
                   ＝⟨ ap! (⟦-⟧ᵇ≃true .fst $
                           reflects-true (≤-reflects n 100) $
                           ≤-trans n≤100-k11 $
                           (∸≤≃≤+ {n = k · 11} ₑ⁻¹) .fst $
                           subst (89 ≤_) (+-assoc 89 11 (k · 11) ∙ +-comm 100 (k · 11)) $
                           ≤-+-r) ⟩
                 δᵏ (f91ᵏ =<<ᵏ ⌜ f91ᵏ (11 + n) ⌝)
                   ＝⟨ ap! (happly e κ) ⟩
                 δᵏ (f91ᵏ =<<ᵏ delay-byᵏ s 91)
                   ＝⟨ ap δᵏ (delay-by-bindᵏ f91ᵏ 91 s) ⟩
                 δᵏ (iter s δᵏ ⌜ f91ᵏ 91 ⌝)
                   ＝⟨ ap! (happly e91 κ) ⟩
                 δᵏ (iter s δᵏ (delay-by s91 91 κ))
                   ＝⟨ ap δᵏ (sym (iter-add s s91 δᵏ (now 91))) ⟩
                 (delay-byᵏ (suc (s + s91)) 91)
                   ∎)
    (f91＝91-90≤n≤100 91 (true-reflects (≤-reflects 90 91) tt)
                         (true-reflects (≤-reflects 91 100) tt))
    (f91＝91-·11 k (11 + n)
                (<-trans <-+-lr k11<100)
                ((≤-∸-l-≃ ∙ₑ ≤-∸-l-≃ {p = k · 11}) .fst n≥90-k11)
                (subst (11 + n ≤_)
                       (m+[n∸p]＝m+n∸p 11 89 (k · 11) (<→≤ (<-+≃2l .fst k11<100)))
                       ((≤-+≃2l ₑ⁻¹) .fst n≤100-k11)))

f91＝91-n≤100 : ∀ n
              → n ≤ 100
              → f91 n ⇓ᵖ 91
f91＝91-n≤100 n n≤100 with ≤-dec 90 n
... | yes n≥90 = f91＝91-90≤n≤100 n n≥90 n≤100
... | no ¬n≥90 = let n<90 = (<≃≱ ₑ⁻¹) .fst ¬n≥90 in
  f91＝91-·11 ((100 ∸ n) / 11) n (prf1 n) (prf2 n n<90) (prf3 n n<90)
  where
  prf1 : ∀ n → (100 ∸ n) / 11 · 11 < 100
  prf1  zero   = true-reflects (<-reflects 99 100) tt
  prf1 (suc n) = ≤-<-trans (m/n*n≤m (99 ∸ n) 11)
                           ((≤-∸-l-≃ {p = n} ∙ₑ ≤≃<suc) .fst z≤)

  prf2 : ∀ n → n < 90 → 90 ∸ (100 ∸ n) / 11 · 11 ≤ n
  prf2 n n<90 =
    subst (λ q → 90 ∸ q ≤ n) (∸-+-assoc n 100 ((100 ∸ n) % 11) ∙ sym ([m/n]*n＝ (100 ∸ n) 11)) $
    (∸≤≃≤+ {n = 100 ∸ (n + (100 ∸ n) % 11)} ₑ⁻¹) .fst $
    subst (90 ≤_) (m∸[n∸p]＝m∸n+p 100 (n + (100 ∸ n) % 11) n ≤-+-r
                    (≤-+ ((≤≃<suc ₑ⁻¹) .fst n<90)
                         (<→≤ (m%n<n (100 ∸ n) 11 (true-reflects (<-reflects 0 11) tt))))) $
    subst (λ q → 90 ≤ 100 ∸ (q ∸ n)) (+-comm ((100 ∸ n) % 11) n) $
    subst (λ q → 90 ≤ 100 ∸ q) (sym $ +-cancel-∸-r ((100 ∸ n) % 11) n) $
    (≤-∸-r-≃ {m = (100 ∸ n) % 11} (true-reflects (<-reflects 0 90) tt) ₑ⁻¹) .fst $
    subst (_≤ 100) (+-comm 90 ((100 ∸ n) % 11)) $
    ((≤-+≃2l {p = 90} ∙ₑ ≤≃<suc) ₑ⁻¹) .fst $
    m%n<n (100 ∸ n) 11 (true-reflects (<-reflects 0 11) tt)

  prf3 : ∀ n → n < 90 → n ≤ 100 ∸ (100 ∸ n) / 11 · 11
  prf3    zero   _    = z≤
  prf3 n@(suc _) n<90 =
    (≤-∸-r-≃ {m = (100 ∸ n) / 11 · 11} z<s ₑ⁻¹) .fst $
    subst (λ q → q + n ≤ 100) (∸-+-assoc n 100 ((100 ∸ n) % 11) ∙ sym ([m/n]*n＝ (100 ∸ n) 11)) $
    subst (_≤ 100) (m∸[n∸p]＝m∸n+p 100 (n + (100 ∸ n) % 11) n ≤-+-r
                        (≤-+ ((≤≃<suc ₑ⁻¹) .fst n<90)
                             (<→≤ (m%n<n (100 ∸ n) 11 (true-reflects (<-reflects 0 11) tt))))) $
    (∸≤≃≤+ {n = n + (100 ∸ n) % 11 ∸ n} ₑ⁻¹) .fst ≤-+-l

f91⇓ : ∀ n → f91 n ⇓
f91⇓ n with (≤-dec n 100)
... | yes n≤100 = 91 , (f91＝91-n≤100 n n≤100)
... | no  n>100 = n ∸ 10 , (f91-n>100⇓ n ((<≃≱ ₑ⁻¹) .fst n>100))
