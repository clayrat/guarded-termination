{-# OPTIONS --safe #-}

open import Prelude

module Data.Star where

infixr 6 _◅_
infixr 6 _◅ʳ_
infixr 5 _◅◅_

private variable
  ℓ ℓ′ ℓ″ : Level
  A : 𝒰 ℓ
  R : Corr² (A , A) ℓ′

-- Reflexive transitive closure.

data Star {ℓ ℓ′} {A : 𝒰 ℓ} (R : Corr² (A , A) ℓ′) : Corr² (A , A) (ℓ ⊔ ℓ′) where
  ε   : ∀ {a} → Star R a a
  _◅_ : ∀ {a b c} → (x : R a b) → (xs : Star R b c) → Star R a c

-- eliminator

elim
  : (P : ∀ {a b} → Star R a b → 𝒰 ℓ″)
  → (∀ {a} → P (ε {a = a}))
  → (∀ {a b c} (rab : R a b) (sbc : Star R b c)
        → P sbc → P (rab ◅ sbc))
  → ∀ {a b} (s : Star R a b) → P s
elim P pε p◅  ε       = pε
elim P pε p◅ (x ◅ xs) = p◅ x xs (elim P pε p◅ xs)

-- singleton

pure⋆ : ∀ {a b} → R a b → Star R a b
pure⋆ x = x ◅ ε

-- append/transitivity

_◅◅_ : ∀ {a b c} → Star R a b → Star R b c → Star R a c
ε        ◅◅ ys = ys
(x ◅ xs) ◅◅ ys = x ◅ (xs ◅◅ ys)

◅◅-ε : ∀ {a b} → (s : Star R a b) → s ◅◅ ε ＝ s
◅◅-ε  ε       = refl
◅◅-ε (x ◅ s) = ap (x ◅_) (◅◅-ε s)

-- snoc

_◅ʳ_ : ∀ {a b c} → Star R a b → R b c → Star R a c
ε         ◅ʳ rbc = pure⋆ rbc
(t ◅ xs) ◅ʳ rbc = t ◅ (xs ◅ʳ rbc)

◅◅-◅ʳ : ∀ {a b c d} → (sab : Star R a b) (rbc : R b c) (scd : Star R c d)
       → sab ◅ʳ rbc ◅◅ scd ＝ sab ◅◅ rbc ◅ scd
◅◅-◅ʳ ε         rbc scd = refl
◅◅-◅ʳ (h ◅ sab) rbc scd = ap (h ◅_) (◅◅-◅ʳ sab rbc scd)

◅ʳ-◅◅ : ∀ {a b c d} → (sab : Star R a b) (sbc : Star R b c) (rcd : R c d)
       → (sab ◅◅ sbc) ◅ʳ rcd ＝ sab ◅◅ sbc ◅ʳ rcd
◅ʳ-◅◅ ε         sbc rcd = refl
◅ʳ-◅◅ (h ◅ sab) sbc rcd = ap (h ◅_) (◅ʳ-◅◅ sab sbc rcd)

◅ʳ-elim :
    (P : ∀ {a b} → Star R a b → 𝒰 ℓ″)
  → (∀ {a} → P (ε {a = a}))
  → (∀ {a b c} (sab : Star R a b) (rbc : R b c)
        → P sab → P (sab ◅ʳ rbc))
  → ∀ {a b} (s : Star R a b) → P s
◅ʳ-elim {R} P pε p◅ʳ s = go ε s pε
  where
  go : ∀ {a b c} → (xs : Star R a b) → (ys : Star R b c) → P xs → P (xs ◅◅ ys)
  go xs  ε       pxs = subst P (sym $ ◅◅-ε xs) pxs
  go xs (y ◅ ys) pxs = subst P (◅◅-◅ʳ xs y ys) (go (xs ◅ʳ y) ys (p◅ʳ xs y pxs))
