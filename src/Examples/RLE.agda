{-# OPTIONS --guarded #-}
module Examples.RLE where

import Prelude as P hiding (_<_ ; Tactic-bishop-finite ; ord→is-discrete)
open P
open import Data.Bool
open import Data.Dec
open import Data.Nat
open import Data.Nat.Order.Inductive
open import Data.List
open import Correspondences.Wellfounded

open import Later
open import Clocked.Partial
open import Clocked.Partial.Converges

private variable
  κ : Cl
  ℓ ℓ′ ℓ″ : Level
  A : 𝒰 ℓ
  B : 𝒰 ℓ′

-- TODO copypasta

Acc-on : {_≺_ : Corr² (A , A) ℓ″} (f : B → A) (b : B)
       → Acc _≺_ (f b) → Acc (λ x y → f x ≺ f y) b
Acc-on f b (acc rec) = acc λ y p → Acc-on f y (rec (f y) p)

span-length : ∀ (p : A → Bool) x
            → let (y , z) = span p x in
              length x ＝ length y + length z
span-length p []      = refl
span-length p (h ∷ t) with p h
... | true  = ap suc (span-length p t)
... | false = refl

{-
map-through : (A → List A → B × List A) → List A → List B
map-through f  []      = []
map-through f (a ∷ as) =
  let (b , as′) = f a as in
  b ∷ map-through f as′
-}

map-throughᵏ-body : (A → List A → B × List A) → ▹ κ (List A → gPart κ (List B)) → List A → gPart κ (List B)
map-throughᵏ-body f m▹ []       = now []
map-throughᵏ-body f m▹ (a ∷ as) =
  let (b , as′) = f a as in
  later (mapᵏ (b ∷_) ⍉ (m▹ ⊛ next as′))

map-throughᵏ : (A → List A → B × List A) → List A → gPart κ (List B)
map-throughᵏ f = fix (map-throughᵏ-body f)

map-through : (A → List A → B × List A) → List A → Part (List B)
map-through f l κ = map-throughᵏ f l

compress-span : ⦃ dA : is-discrete A ⦄
              → A → List A → (ℕ × A) × List A
compress-span {A} hd tl =
  let (p , s) = span {A = A} (λ a → ⌊ _≟_ a hd ⌋) tl in
  ((suc (length p)) , hd) , s

rle : ⦃ dA : is-discrete A ⦄
    → List A → Part (List (ℕ × A))
rle = map-through compress-span

-- termination

map-through-acc⇓ : (f : A → List A → B × List A)
                 → (∀ a as → length (f a as .snd) ≤ length as)
                 → ∀ l
                 → Acc (λ x y → length x < length y) l
                 → map-through f l ⇓
map-through-acc⇓ f _   []        _        = [] , ∣ 0 , refl ∣₁
map-through-acc⇓ f prf (a ∷ as) (acc rec) =
  let (b , as′) = f a as
      (q , q⇓) = map-through-acc⇓ f prf as′ (rec as′ (s≤s (prf a as)))
    in
    (b ∷ q)
  , map (λ where
             (qk , qe) →
               suc qk , fun-ext λ κ →
                          map-throughᵏ f (a ∷ as)
                            ＝⟨ ap (λ q → q (a ∷ as)) (fix-path (map-throughᵏ-body f))  ⟩
                          δᵏ (mapᵏ (_∷_ b) ⌜ map-throughᵏ f as′ ⌝)
                            ＝⟨ ap! (happly qe κ) ⟩
                          δᵏ (mapᵏ (_∷_ b) (delay-byᵏ qk q))
                            ＝⟨ ap δᵏ (delay-by-mapᵏ q qk) ⟩
                          delay-byᵏ (suc qk) (b ∷ q)
                            ∎)
        q⇓

map-through⇓ : (f : A → List A → B × List A)
             → (∀ a as → length (f a as .snd) ≤ length as)
             → ∀ l → map-through f l ⇓
map-through⇓ f prf l = map-through-acc⇓ f prf l (Acc-on length l $ Wf-< (length l))

compress-span-prf : ⦃ dA : is-discrete A ⦄
                  → (a : A) → (as : List A)
                  → length (compress-span a as .snd) ≤ length as
compress-span-prf a as =
  subst (length (compress-span a as .snd) ≤_)
        (sym (span-length (λ x → ⌊ x ≟ a ⌋) as))
        ≤-+-l

rle⇓ : ⦃ dA : is-discrete A ⦄
     → (as : List A) → rle as ⇓
rle⇓ as = map-through⇓ compress-span compress-span-prf as

