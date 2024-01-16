{-# OPTIONS --guarded #-}
module Examples.Harper where

open import Prelude hiding (_<_)
open import Data.Empty
open import Data.Char
open import Data.Bool
open import Data.Dec
open import Data.List

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

matchi : ▹ κ (A → StdReg → gMatchT κ A) → StdReg → Char → A → gMatchT κ A
matchi m▹  NoMatch       c s k = now false
matchi m▹ (MatchChar x)  c s k = if ⌊ c ≟ x ⌋ then k s else now false
matchi m▹ (Or r₁ r₂)     c s k = apᵏ (mapᵏ _or_ (matchi m▹ r₁ c s k)) (matchi m▹ r₂ c s k )
matchi m▹ (Plus r)       c s k = matchi m▹ r c s (λ s′ → apᵏ (mapᵏ _or_ (k s′)) (later (m▹ ⊛ next s′ ⊛ next (Plus r) ⊛ next k)))
matchi m▹ (Concat r₁ r₂) c s k = matchi m▹ r₁ c s (λ s′ → later (m▹ ⊛ next s′ ⊛ next r₂ ⊛ next k))

matcher-body : ▹ κ (List Char → StdReg → gMatchT κ (List Char)) → List Char → StdReg → gMatchT κ (List Char)
matcher-body m▹  []     r k = now false
matcher-body m▹ (c ∷ s) r k = matchi m▹ r c s k

matcher : List Char → StdReg → gMatchT κ (List Char)
matcher = fix matcher-body

match : List Char → StdReg → Part Bool
match s r κ = matcher s r (now ∘ null?)

-- termination

