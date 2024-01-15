{-# OPTIONS --guarded #-}
module WordsBy where

open import Prelude hiding (_<_)
open import Data.Bool
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

-- TODO upstream
×-inj : {a c : A} {b d : B}
      → (a , b) ＝ (c , d) → (a ＝ c) × (b ＝ d)
×-inj e = (λ i → e i .fst) , (λ i → e i .snd)

span-length : ∀ (p : A → Bool) x
            → let (y , z) = span p x in
              length x ＝ length y + length z
span-length p []      = refl
span-length p (h ∷ t) with p h
... | true  = ap suc (span-length p t)
... | false = refl

Acc-on : {_≺_ : Corr² (A , A) ℓ″} (f : B → A) (b : B)
       → Acc _≺_ (f b) → Acc (λ x y → f x ≺ f y) b
Acc-on f b (acc rec) = acc λ y p → Acc-on f y (rec (f y) p)

-- break

break : (A → Bool) → List A → List A × List A
break p = span (not ∘ p)

break-length : ∀ (p : A → Bool) x
             → let (y , z) = break p x
               in length x ＝ length y + length z
break-length p x = span-length (not ∘ p) x

{-
wordsBy : (A → Bool) → List A → List (List A)
wordsBy p []        = []
wordsBy p (hd ∷ tl) =
  if p hd
    then wordsBy p tl
    else let (w , z) = break p tl in
         (hd ∷ w) ∷ wordsBy p z
-}

wordsByᵏ-body : (A → Bool)
              → ▹ κ (List A → gPart κ (List (List A)))
              → List A → gPart κ (List (List A))
wordsByᵏ-body p w▹ []        = now []
wordsByᵏ-body p w▹ (hd ∷ tl) =
  later (if p hd
           then w▹ ⊛ next tl
           else let (w , z) = break p tl in
                mapᵏ ((hd ∷ w) ∷_) ⍉ (w▹ ⊛ next z))

wordsByᵏ : (A → Bool)
         → List A → gPart κ (List (List A))
wordsByᵏ p = fix (wordsByᵏ-body p)

wordsBy : (A → Bool)
        → List A → Part (List (List A))
wordsBy p l κ = wordsByᵏ p l

-- termination

wordsBy⇓-acc : (p : A → Bool)
             → ∀ l → Acc (λ x y → length x < length y) l → wordsBy p l ⇓
wordsBy⇓-acc p []         _        = [] , ∣ 0 , refl ∣₁
wordsBy⇓-acc p (hd ∷ tl) (acc rec) with p hd
... | true  =
  second
    (λ {x} →
      map λ where
              (k , e) →
                 (suc k) , fun-ext λ κ →
                             later (dfix (wordsByᵏ-body p) ⊛ next tl)
                               ＝⟨ ap later (▹-ext λ α i → pfix (wordsByᵏ-body p) i α tl) ⟩
                             δᵏ (wordsByᵏ p tl)
                               ＝⟨ ap δᵏ (happly e κ) ⟩
                             delay-byᵏ (suc k) x
                               ∎)
    (wordsBy⇓-acc p tl (rec tl ≤-refl))
... | false =
  let (w , z) = break p tl
      (x , x⇓) = wordsBy⇓-acc p z (rec z (s≤s (subst (λ q → length (break p tl .snd) ≤ q)
                                              (sym (break-length p tl))
                                              ≤-+-l)))
    in
    ((hd ∷ w) ∷ x)
  , map (λ where
             (k , e) →
               (suc k) , fun-ext λ κ →
                           later (mapᵏ ((hd ∷ w) ∷_) ⍉ (dfix (wordsByᵏ-body p) ⊛ next z))
                             ＝⟨ ap later (▹-ext λ α i → mapᵏ ((hd ∷ w) ∷_) (pfix (wordsByᵏ-body p) i α z)) ⟩
                           δᵏ (mapᵏ ((hd ∷ w) ∷_) ⌜ wordsByᵏ p z ⌝)
                             ＝⟨ ap! (happly e κ) ⟩
                           δᵏ (mapᵏ ((hd ∷ w) ∷_) (delay-byᵏ k x))
                             ＝⟨ ap δᵏ (delay-by-mapᵏ x k) ⟩
                           delay-byᵏ (suc k) ((hd ∷ w) ∷ x)
                               ∎)
         x⇓

wordsBy⇓ : (p : A → Bool)
         → ∀ l → wordsBy p l ⇓
wordsBy⇓ p l = wordsBy⇓-acc p l (Acc-on length l $ Wf-< (length l))

