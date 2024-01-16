{-# OPTIONS --guarded #-}
module Examples.HORec where

open import Prelude
open import Data.Empty
open import Data.Nat
open import Data.List

open import Later
open import Clocked.Partial
open import Clocked.Partial.Converges

private variable
  κ : Cl
  ℓ ℓ′ : Level
  A : 𝒰 ℓ
  B : 𝒰 ℓ′

-- TODO move

list-travᵏ : List (gPart κ A) → gPart κ (List A)
list-travᵏ []      = now []
list-travᵏ (h ∷ t) = apᵏ (mapᵏ _∷_ h) (list-travᵏ t)

List▹ : (A → ▹ κ B) → List A → ▹ κ (List B)
List▹ f []      = next []
List▹ f (h ∷ t) = (_∷_) ⍉ f h ⊛ List▹ f t

data Tree (A : 𝒰 ℓ) : 𝒰 ℓ where
  node : A → List (Tree A) → Tree A

{-
mirror : Tree A → Tree A
mirror (node a ts) = node a (reverse (map mirror ts))
-}

map-mirrorᵏ-body : ▹ κ (Tree A → gPart κ (Tree A)) → List (Tree A) → gPart κ (List (Tree A))
map-mirrorᵏ-body m▹ ts = later (list-travᵏ ⍉ List▹ (λ t → m▹ ⊛ next t) ts)

mirrorᵏ-body : ▹ κ (Tree A → gPart κ (Tree A)) → Tree A → gPart κ (Tree A)
mirrorᵏ-body m▹ (node a ts) = mapᵏ (node a ∘ reverse) (map-mirrorᵏ-body m▹ ts)

mirrorᵏ : Tree A → gPart κ (Tree A)
mirrorᵏ = fix mirrorᵏ-body

mirror : Tree A → Part (Tree A)
mirror t κ = mirrorᵏ t

-- termination

map-mirrorᵏ : List (Tree A) → gPart κ (List (Tree A))
map-mirrorᵏ = map-mirrorᵏ-body (dfix mirrorᵏ-body)

map-mirror : List (Tree A) → Part (List (Tree A))
map-mirror t κ = map-mirrorᵏ t

mutual
  map-mirror⇓ : (ts : List (Tree A)) → map-mirror ts ⇓
  map-mirror⇓ []      = [] , ∣ 1 , refl ∣₁
  map-mirror⇓ (h ∷ t) =
    let (qs , qs⇓) = map-mirror⇓ t
        (r , r⇓) = mirror⇓ h
      in
      r ∷ qs
    , map² (λ where
                (rk , re) (zero   , qe) → absurd (now≠later (sym (happly qe k0)))
                (rk , re) (suc qk , qe) →
                   suc (max rk qk)
                 , fun-ext λ κ →
                      map-mirrorᵏ (h ∷ t)
                        ＝⟨ ap (λ q → map-mirrorᵏ-body q (h ∷ t)) (pfix mirrorᵏ-body) ⟩
                      later (apᵏ (mapᵏ _∷_ ⌜ mirrorᵏ h ⌝) ⍉ (list-travᵏ ⍉ (List▹ (next ∘ mirrorᵏ) t)))
                        ＝⟨ ap! (happly re κ) ⟩
                      later (apᵏ ⌜ mapᵏ _∷_ (delay-byᵏ rk r) ⌝ ⍉ (list-travᵏ ⍉ (List▹ (next ∘ mirrorᵏ) t)))
                        ＝⟨ ap! (delay-by-mapᵏ r rk) ⟩
                      later (apᵏ (delay-byᵏ rk (r ∷_)) ⍉ (list-travᵏ ⍉ (List▹ (next ∘ mirrorᵏ) t)))
                        ＝⟨ ap later (▹-ext λ α → ap (apᵏ (delay-byᵏ rk (r ∷_)))
                                                    ((λ i → list-travᵏ (List▹ (λ t₁ α₁ → pfix mirrorᵏ-body (~ i) α₁ t₁) t α))
                                                     ∙ ▹-ap (later-inj (happly qe κ)) α)) ⟩
                      δᵏ (apᵏ (delay-byᵏ rk (r ∷_)) (delay-byᵏ qk qs))
                        ＝⟨ ap δᵏ (delay-by-apᵏ (r ∷_) rk qs qk) ⟩
                      delay-byᵏ (suc (max rk qk)) (r ∷ qs)
                        ∎)
           r⇓ qs⇓

  mirror⇓ : (t : Tree A) → mirror t ⇓
  mirror⇓ (node a ts) =
    let (qs , qs⇓) = map-mirror⇓ ts in
      (node a (reverse qs))
    , map (λ where
                (qk , qe) →
                  qk , fun-ext λ κ →
                          mirrorᵏ (node a ts)
                            ＝⟨ ap (λ q → q (node a ts)) (fix-path mirrorᵏ-body) ⟩
                          mapᵏ (node a ∘ reverse) (map-mirrorᵏ-body ⌜ next mirrorᵏ ⌝ ts)
                            ＝⟨ ap! (sym $ pfix mirrorᵏ-body) ⟩
                          mapᵏ (node a ∘ reverse) ⌜ map-mirrorᵏ ts ⌝
                            ＝⟨ ap! (happly qe κ) ⟩
                          mapᵏ (node a ∘ reverse) (delay-byᵏ qk qs)
                            ＝⟨ delay-by-mapᵏ qs qk ⟩
                          delay-byᵏ qk (node a (reverse qs))
                            ∎)
          qs⇓
