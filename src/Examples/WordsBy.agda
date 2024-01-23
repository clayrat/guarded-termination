{-# OPTIONS --guarded #-}
module Examples.WordsBy where

open import Prelude hiding (_<_)
open import Data.Empty
open import Data.Bool
open import Data.Dec
open import Data.Nat
open import Data.Nat.Order.Inductive
open import Data.List
open import Data.List.Correspondences.Unary.All
open import Data.List.Operations.Properties
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

Acc-on : {_≺_ : Corr² (A , A) ℓ″} (f : B → A) (b : B)
       → Acc _≺_ (f b) → Acc (λ x y → f x ≺ f y) b
Acc-on f b (acc rec) = acc λ y p → Acc-on f y (rec (f y) p)

-- break

break : (A → Bool) → List A → List A × List A
break p = span (not ∘ p)

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

-- termination & correctness

break-length : ∀ (p : A → Bool) x
             → let (y , z) = break p x
               in length x ＝ length y + length z
break-length p = span-length (not ∘ p)

-- + induction principle
wordsBy⇓-acc : (p : A → Bool)
             → (P : List A → List (List A) → 𝒰 ℓ″)
             → P [] []
             → (∀ a as aas → ⟦ p a ⟧ᵇ       → P as aas                → P (a ∷ as) aas)
             → (∀ a as aas → ⟦ not (p a) ⟧ᵇ → P (break p as .snd) aas → P (a ∷ as) ((a ∷ break p as .fst) ∷ aas))
             → ∀ l
             → Acc (λ x y → length x < length y) l
             → Σ[ r ꞉ List (List A) ] (wordsBy p l ⇓ᵖ r) × (P l r)
wordsBy⇓-acc p P P0 PT PF []         _        = [] , ∣ 0 , refl ∣₁ , P0
wordsBy⇓-acc p P P0 PT PF (hd ∷ tl) (acc rec) with p hd | recall p hd
... | true  | ⟪ e ⟫ =
  let (q , q⇓ , qP) = wordsBy⇓-acc p P P0 PT PF tl (rec tl ≤-refl) in
      q
    , map (λ where
              (k , e) →
                 (suc k) , fun-ext λ κ →
                             later (dfix (wordsByᵏ-body p) ⊛ next tl)
                               ＝⟨ ap later (▹-ext λ α i → pfix (wordsByᵏ-body p) i α tl) ⟩
                             δᵏ (wordsByᵏ p tl)
                               ＝⟨ ap δᵏ (happly e κ) ⟩
                             delay-byᵏ (suc k) q
                               ∎)
         q⇓
    , PT hd tl q (subst ⟦_⟧ᵇ (sym e) tt) qP
... | false | ⟪ e ⟫ =
  let (w , z) = break p tl
      (q , q⇓ , qP) = wordsBy⇓-acc p P P0 PT PF z (rec z (s≤s (subst (λ q → length (break p tl .snd) ≤ q)
                                                           (sym (break-length p tl))
                                                           ≤-+-l)))
    in
    ((hd ∷ w) ∷ q)
  , map (λ where
             (k , e) →
               (suc k) , fun-ext λ κ →
                           later (mapᵏ ((hd ∷ w) ∷_) ⍉ (dfix (wordsByᵏ-body p) ⊛ next z))
                             ＝⟨ ap later (▹-ext λ α i → mapᵏ ((hd ∷ w) ∷_) (pfix (wordsByᵏ-body p) i α z)) ⟩
                           δᵏ (mapᵏ ((hd ∷ w) ∷_) ⌜ wordsByᵏ p z ⌝)
                             ＝⟨ ap! (happly e κ) ⟩
                           δᵏ (mapᵏ ((hd ∷ w) ∷_) (delay-byᵏ k q))
                             ＝⟨ ap δᵏ (delay-by-mapᵏ q k) ⟩
                           delay-byᵏ (suc k) ((hd ∷ w) ∷ q)
                               ∎)
         q⇓
  , PF hd tl q (subst (⟦_⟧ᵇ ∘ not) (sym e) tt) qP

wordsBy⇓ : (p : A → Bool)
         → (P : List A → List (List A) → 𝒰 ℓ″)
         → P [] []
         → (∀ a as aas → ⟦ p a ⟧ᵇ → P as aas → P (a ∷ as) aas)
         → (∀ a as aas → ⟦ not (p a) ⟧ᵇ → P (break p as .snd) aas → P (a ∷ as) ((a ∷ break p as .fst) ∷ aas))
         → ∀ l
         → Σ[ r ꞉ List (List A) ] (wordsBy p l ⇓ᵖ r) × (P l r)
wordsBy⇓ p P P0 PT PF l = wordsBy⇓-acc p P P0 PT PF l (Acc-on length l $ Wf-< (length l))

wordsBy⇓-in : ∀ (p : A → Bool) l
            → All (⟦_⟧ᵇ ∘ p) l → wordsBy p l ⇓ᵖ []
wordsBy⇓-in p l ap =
  let (r , r⇓ , r[]) = wordsBy⇓ p (λ l′ r → All (⟦_⟧ᵇ ∘ p) l′ → r ＝ [])
                         (λ _ → refl)
                         (λ a as aas pa ih → λ where (a′ ∷ aa) → ih aa)
                         (λ a as aas npa ih → λ where (a′ ∷ aa) → absurd (false-reflects reflects-id npa a′))
                         l
     in
  subst (wordsBy p l ⇓ᵖ_) (r[] ap) r⇓

wordsBy⇓-out : ∀ (p : A → Bool) l
             → Σ[ r ꞉ List (List A) ] (wordsBy p l ⇓ᵖ r) × (All (λ x → All (⟦_⟧ᵇ ∘ not ∘ p) x) r)
wordsBy⇓-out p =
  wordsBy⇓ p (λ _ r → All (λ x → All (⟦_⟧ᵇ ∘ not ∘ p) x) r)
     []
     (λ a as aas pa ih → ih)
     (λ a as aas npa ih → (npa ∷ span-all (not ∘ p) as) ∷ ih)

