{-# OPTIONS --guarded #-}
module Examples.Harper where

open import Prelude hiding (_<_)
open import Data.Empty
open import Data.Char
open import Data.Bool
open import Data.Dec
open import Data.Nat
open import Data.List
open import Correspondences.Wellfounded

open import Later
open import Clocked.Partial
open import Clocked.Partial.Converges

private variable
  κ : Cl
  A : 𝒰

-- TODO upstream
null? : List A → Bool
null?  []     = true
null? (_ ∷ _) = false

data StdReg : 𝒰 where
  NoMatch   : StdReg
  MatchChar : Char → StdReg
  Or        : StdReg → StdReg → StdReg
  Plus      : StdReg → StdReg
  Concat    : StdReg → StdReg → StdReg

gK : Cl → 𝒰 → 𝒰
gK κ A = A → gPart κ Bool

gMatchT : Cl → 𝒰 → 𝒰
gMatchT κ A = gK κ A → gPart κ Bool

K : 𝒰 → 𝒰
K A = A → Part Bool

K⇒ : K A → ∀ κ → gK κ A
K⇒ k κ l = k l κ

MatchT : 𝒰 → 𝒰
MatchT A = K A → Part Bool

matchi-bodyᵏ : ▹ κ (A → StdReg → gMatchT κ A)
             → StdReg → Char → A → gMatchT κ A
matchi-bodyᵏ m▹  NoMatch       c s k = now false
matchi-bodyᵏ m▹ (MatchChar x)  c s k = if ⌊ c ≟ x ⌋ then k s else now false
matchi-bodyᵏ m▹ (Or r₁ r₂)     c s k = map²ᵏ _or_ (matchi-bodyᵏ m▹ r₁ c s k) (matchi-bodyᵏ m▹ r₂ c s k)
matchi-bodyᵏ m▹ (Plus r)       c s k = matchi-bodyᵏ m▹ r c s λ s′ → map²ᵏ _or_ (k s′) (later (m▹ ⊛ next s′ ⊛ next (Plus r) ⊛ next k))
matchi-bodyᵏ m▹ (Concat r₁ r₂) c s k = matchi-bodyᵏ m▹ r₁ c s λ s′ → later (m▹ ⊛ next s′ ⊛ next r₂ ⊛ next k)

matcher-bodyᵏ : ▹ κ (List Char → StdReg → gMatchT κ (List Char))
              →      List Char → StdReg → gMatchT κ (List Char)
matcher-bodyᵏ m▹  []     r k = now false
matcher-bodyᵏ m▹ (c ∷ s) r k = matchi-bodyᵏ m▹ r c s k

matcherᵏ : List Char → StdReg → gMatchT κ (List Char)
matcherᵏ = fix matcher-bodyᵏ

matcher : List Char → StdReg → MatchT (List Char)
matcher l r k = matcherᵏ l r ∘ K⇒ k

match : List Char → StdReg → Part Bool
match s r = matcher s r (pureᵖ ∘ null?)

-- termination

matchiᵏ : StdReg → Char → List Char → gMatchT κ (List Char)
matchiᵏ = matchi-bodyᵏ (dfix matcher-bodyᵏ)

matchi : StdReg → Char → List Char → MatchT (List Char)
matchi r c s k = matchiᵏ r c s ∘ K⇒ k

-- TODO upstream
data Suffix {ℓ : Level} {A : 𝒰 ℓ} : List A → List A → 𝒰 ℓ where
  Stop : ∀ {x xs}
       → Suffix xs (x ∷ xs)
  Drop : ∀ {y xs ys}
       → Suffix xs ys → Suffix xs (y ∷ ys)

¬suffix-[] : {ℓ : Level} {A : 𝒰 ℓ} (xs : List A) → ¬ (Suffix xs [])
¬suffix-[] xs ()

suffix-trans : {ℓ : Level} {A : 𝒰 ℓ} {xs ys zs : List A}
             → Suffix xs ys
             → Suffix ys zs
             → Suffix xs zs
suffix-trans sxy  Stop      = Drop sxy
suffix-trans sxy (Drop syz) = Drop (suffix-trans sxy syz)

acc-suffix : {ℓ : Level} {A : 𝒰 ℓ} {y : A} {xs ys : List A}
           → Suffix xs (y ∷ ys)
           → Acc Suffix ys
           → Acc Suffix xs
acc-suffix  Stop     a        = a
acc-suffix (Drop s) (acc rec) = rec _ s

suffix-wf : {ℓ : Level} {A : 𝒰 ℓ} → Wf (Suffix {ℓ} {A})
suffix-wf []       = acc λ ys prf → absurd (¬suffix-[] ys prf)
suffix-wf (x ∷ xs) = acc λ ys prf → acc-suffix prf (suffix-wf xs)

mutual
  matchi⇓ : (r : StdReg) → (c : Char) → (s : List Char)
          → (k : K (List Char))
          → (∀ l → Suffix l (c ∷ s) → k l ⇓)
          → Acc Suffix (c ∷ s)
          → matchi r c s k ⇓
  matchi⇓  NoMatch       c s k k⇓ a           = false , ∣ 0 , refl ∣₁
  matchi⇓ (MatchChar x)  c s k k⇓ a with c ≟ x
  ... | yes e = second (λ {x = z} →
                          map λ where
                                  (qk , qe) →
                                    qk , fun-ext (λ κ → Data.Dec.elim
                                                         {C = λ q → (if ⌊ q ⌋ then k s κ else now false) ＝ delay-byᵏ qk z}
                                                         (λ _ → happly qe κ)
                                                         (λ ne → absurd (ne e))
                                                         (c ≟ x)))
                       (k⇓ s Stop)
  ... | no ne = false , ∣ 0 , fun-ext (λ κ →
                                          Data.Dec.elim
                                            {C = λ q → (if ⌊ q ⌋ then k s κ else now false) ＝ now false}
                                            (λ e → absurd (ne e))
                                            (λ _ → refl)
                                            (c ≟ x)) ∣₁
  matchi⇓ (Or r₁ r₂)     c s k k⇓ a =
    let (x , x⇓) = matchi⇓ r₁ c s k k⇓ a
        (y , y⇓) = matchi⇓ r₂ c s k k⇓ a
      in
    x or y , map²⇓ _or_ x⇓ y⇓
  matchi⇓ (Plus r)       c s k k⇓ a@(acc rec) =
    matchi⇓ r c s (λ z κ → map²ᵏ _or_ (k z κ) (later (dfix matcher-bodyᵏ ⊛ next z ⊛ next (Plus r) ⊛ next (K⇒ k κ))))
      (λ l sl →
         let (x , x⇓) = k⇓ l sl
             (y , y⇓) = matcher⇓ l (Plus r) k (λ l′ prf → k⇓ l′ (suffix-trans prf sl)) (rec l sl)
           in
         x or y , map²⇓ _or_ x⇓
                    (map (λ where
                              (yk , ye) →
                                 suc yk , fun-ext λ κ →
                                              ap later (▹-ext λ α → λ i → pfix matcher-bodyᵏ i α l (Plus r) (K⇒ k κ))
                                            ∙ ap δᵏ (happly ye κ))
                      y⇓))
      a
  matchi⇓ (Concat r₁ r₂) c s k k⇓ a@(acc rec) =
    matchi⇓ r₁ c s (λ z κ → later (dfix matcher-bodyᵏ ⊛ next z ⊛ next r₂ ⊛ next (K⇒ k κ)))
      (λ l sl →
         second
           (map λ where
                    (qk , qe) →
                       suc qk , fun-ext λ κ →
                                  ap later (▹-ext λ α → λ i → pfix matcher-bodyᵏ i α l r₂ (K⇒ k κ))
                                  ∙ ap δᵏ (happly qe κ))
           (matcher⇓ l r₂ k (λ l′ prf → k⇓ l′ (suffix-trans prf sl)) (rec l sl)))
      a

  matcher⇓ : (s : List Char) → (r : StdReg)
           → (k : K (List Char))
           → (∀ l → Suffix l s → k l ⇓)
           → Acc Suffix s
           → matcher s r k ⇓
  matcher⇓ []      r k k⇓ a = false , ∣ 0 , refl ∣₁
  matcher⇓ (c ∷ s) r k k⇓ a =
    let (q , q⇓) = matchi⇓ r c s k k⇓ a in
    q , map (λ where
                (qk , qe) →
                  qk , (fun-ext λ κ →
                          matcherᵏ (c ∷ s) r (K⇒ k κ)
                            ＝⟨ ap (λ q → q (c ∷ s) r (K⇒ k κ)) (fix-path matcher-bodyᵏ) ⟩
                          matchi-bodyᵏ (next matcherᵏ) r c s (K⇒ k κ)
                            ＝⟨ ap (λ q → matchi-bodyᵏ q r c s (K⇒ k κ)) (sym (pfix matcher-bodyᵏ)) ⟩
                          matchiᵏ r c s (K⇒ k κ)
                            ＝⟨ happly qe κ ⟩
                          delay-byᵏ qk q
                            ∎))
             q⇓

match⇓ : (s : List Char) → (r : StdReg) → match s r ⇓
match⇓ s r = matcher⇓ s r (pureᵖ ∘ null?) (λ l _ → null? l , pure⇓) (suffix-wf s)
