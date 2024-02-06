{-# OPTIONS --safe #-}
module Data.Plus where

open import Prelude

open import Data.Sum
open import Data.Star

infixr 5 _◅⁺_
infixr 5 _◅◅⁺_

private variable
  ℓ ℓ′ ℓ″ : Level
  A : 𝒰 ℓ
  R : Corr² (A , A) ℓ′

-- Transitive closure.

data Plus {ℓ ℓ′} {A : 𝒰 ℓ} (R : Corr² (A , A) ℓ′) : Corr² (A , A) (ℓ ⊔ ℓ′) where
  [_]⁺   : ∀ {a b} → R a b → Plus R a b
  _◅⁺_ : ∀ {a b c} → (x : R a b) → (xs : Plus R b c) → Plus R a c

-- Append/transitivity.

_◅◅⁺_ : ∀ {a b c} → Plus R a b → Plus R b c → Plus R a c
[ x ]⁺      ◅◅⁺ ys = x ◅⁺ ys
(x ◅⁺ xs) ◅◅⁺ ys = x ◅⁺ (xs ◅◅⁺ ys)

-- Conversion

Plus→Star : ∀ {a b} → Plus R a b → Star R a b
Plus→Star [ r ]⁺   = pure⋆ r
Plus→Star (r ◅⁺ p) = r ◅ Plus→Star p

Plus-uncons : ∀ {a b} → Plus R a b → Σ[ c ꞉ A ] (R a c × Star R c b)
Plus-uncons [ r ]⁺    = _ , r , ε
Plus-uncons (r ◅⁺ p) = _ , r , (Plus→Star p)

Plus-unsnoc : ∀ {a b} → Plus R a b → Σ[ c ꞉ A ] (Star R a c × R c b)
Plus-unsnoc [ r ]⁺ = _ , ε , r
Plus-unsnoc (r ◅⁺ p) =
  let (c , sc , rc) = Plus-unsnoc p in
  c , r ◅ sc , rc

◅-Star : ∀ {a b c} → R a b → Star R b c → Plus R a c
◅-Star r ε = [ r ]⁺
◅-Star r (x ◅ s) = r ◅⁺ ◅-Star x s

Star-◅ : ∀ {a b c} → Star R a b → R b c → Plus R a c
Star-◅  ε      r = [ r ]⁺
Star-◅ (x ◅ s) r = x ◅⁺ Star-◅ s r

Star→Plus＝ : ∀ {a b} → Star R a b → Plus R a b ⊎ (a ＝ b)
Star→Plus＝  ε      = inr refl
Star→Plus＝ (r ◅ s) = inl (◅-Star r s)
