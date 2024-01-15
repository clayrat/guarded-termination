{-# OPTIONS --guarded #-}
module Examples.GCD where

open import Prelude hiding (_<_)
open import Data.Empty
open import Data.Nat
open import Data.Nat.Order.Inductive
open import Data.Nat.DivMod
open import Data.Nat.DivMod.Inductive
open import Correspondences.Wellfounded

open import Later
open import Clocked.Partial
open import Clocked.Partial.Converges

private variable
  κ : Cl

-- classical fused definition
{-
gcd′ : (m n : ℕ) → Acc _<_ m → n < m → ℕ
gcd′ m    zero    _        _   = m
gcd′ m n@(suc _) (acc rec) n<m = gcd′ n (m % n) (rec n n<m) (m%n<n m n (s≤s z≤))

gcd : ℕ → ℕ → ℕ
gcd m n with ≤-split m n
... | inl      m<n  = gcd′ n m (Wf-< n) m<n
... | inr (inl n<m) = gcd′ m n (Wf-< m) n<m
... | inr (inr _)   = m
-}

-- GCD via partiality monad

gcdᵏ-body : ▹ κ (ℕ → ℕ → gPart κ ℕ) → ℕ → ℕ → gPart κ ℕ
gcdᵏ-body g▹ m    zero   = now m
gcdᵏ-body g▹ m n@(suc _) = later (g▹ ⊛ next n ⊛ next (m % n))

gcdᵏ : ℕ → ℕ → gPart κ ℕ
gcdᵏ = fix gcdᵏ-body

gcd : ℕ → ℕ → Part ℕ
gcd m n k = gcdᵏ m n

-- properties

gcd-refl : ∀ m → gcd m m ⇓ᵖ m
gcd-refl    zero   = ∣ 0 , refl ∣₁
gcd-refl m@(suc _) = ∣ 1 , (fun-ext λ κ → ap (λ q → q m m) (fix-path gcdᵏ-body)
                                        ∙ ap (δᵏ ∘ gcdᵏ m) (n%n＝0 m)) ∣₁

gcd-<-comm : ∀ m n → m < n → gcd m n ＝⇓ gcd n m
gcd-<-comm m n@(suc _) m<n =
  ＝⇓-trans (＝→＝⇓ (fun-ext λ κ → ap (λ q → q m n) (fix-path gcdᵏ-body))) $
  ＝⇓-sym $ ＝⇓-trans ＝⇓-δ $    -- we need clocks for this step
  ＝→＝⇓ (fun-ext λ κ → ap (δᵏ ∘ gcdᵏ n) (sym (m<n⇒m%n≡m m n m<n)))

gcd-comm : ∀ m n → gcd m n ＝⇓ gcd n m
gcd-comm m n with ≤-split m n
... | inl      m<n  = gcd-<-comm m n m<n
... | inr (inl n<m) = ＝⇓-sym (gcd-<-comm n m n<m)
... | inr (inr e)   = subst (λ q → gcd m q ＝⇓ gcd q m) e ＝⇓-refl

-- termination

gcd-<⇓ : ∀ m n → Acc _<_ m → n < m → gcd m n ⇓
gcd-<⇓ m    zero    _        _   = m , ∣ 0 , refl ∣₁
gcd-<⇓ m n@(suc _) (acc rec) n<m =
  second (map λ where (y , prf) → suc y , fun-ext λ κ → ap (λ q → q m n) (fix-path gcdᵏ-body)
                                                      ∙ ap δᵏ (happly prf κ)) $
  gcd-<⇓ n (m % n) (rec n n<m) (m%n<n m n (s≤s z≤))

gcd⇓ : ∀ m n → gcd m n ⇓
gcd⇓ m n with ≤-split m n
... | inl      m<n  = let (x , g⇓) = gcd-<⇓ n m (Wf-< n) m<n in
                      x , gcd-comm m n x .snd g⇓
... | inr (inl n<m) = gcd-<⇓ m n (Wf-< m) n<m
... | inr (inr e)   = m , subst (λ q → gcd m q ⇓ᵖ m) e (gcd-refl m)
