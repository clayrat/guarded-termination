{-# OPTIONS --guarded #-}

import Prelude as P hiding (_<_ ; Tactic-bishop-finite ; ord→is-discrete)
open P
open import Data.Empty
open import Data.Bool
open import Data.Dec as Dec
open import Data.Sum
open import Data.Nat
open import Data.List
open import Data.List.Correspondences.Unary.Any
open import Correspondences.Wellfounded

open import Data.Star
open import Data.Plus
open import Later
open import Clocked.Partial
open import Clocked.Partial.Converges
open import Clocked.Partial.All

module Examples.DFS
  {ℓ ℓ′ : Level}
  {A : 𝒰 ℓ}
  ⦃ dA : is-discrete A ⦄
  (sucs : A → List A)
  (acy : Wf λ x y → Has x (sucs y))
  where

-- TODO smth

has : A → List A → Bool
has = elem (λ x y → ⌊ x ≟ y ⌋)

has-r : ∀ x xs → Reflects (Has x xs) (has x xs)
has-r x []       = ofⁿ ¬Any-[]
has-r x (y ∷ xs) with x ≟ y
... | yes e = ofʸ (here (sym e))
... | no ne =
  Reflects′.dmap there
    (λ h → λ where
               (here e) → ne (sym e)
               (there a) → h a)
    (has-r x xs)

Subset : List A → List A → 𝒰 ℓ
Subset xs ys = ∀ z → Has z xs → Has z ys

Subset-refl : ∀ xs → Subset xs xs
Subset-refl xs z = id

-- well-founded DFS

succ : A → A → 𝒰 ℓ
succ x y = Has x (sucs y)

mutual
  dfs : (x : A) → (accu : List A) → (ac : Acc succ x) → List A
  dfs x accu ac = if has x accu then accu else x ∷ dfs-list (sucs x) accu ac (Subset-refl (sucs x))

  -- an inlined left fold
  dfs-list : (l : List A) → (accu : List A) → {x : A} → (ac : Acc succ x) → Subset l (sucs x) → List A
  dfs-list  []     accu ac           sub = accu
  dfs-list (y ∷ l) accu ac@(acc rec) sub =
    dfs-list l
      (dfs y accu (rec y (sub y (here refl))))
      ac
      λ z Hz → sub z (there Hz)

dfs0 : A → List A
dfs0 x = dfs x [] (acy x)

succ-closed : List A → 𝒰 ℓ
succ-closed l = ∀ x y → Has x l → succ y x → Has y l

star-sc : ∀ l → succ-closed l
        → ∀ x y
        → Has x l
        → Star succ y x
        → Has y l
star-sc l sc x .x hx  ε             = hx
star-sc l sc x  y hx (_◅_ {b} h st) = sc b y (star-sc l sc x b hx st) h

mutual
   go : (x : A)
      → ((y : A) → succ y x → (l : List A) (ac : Acc succ y) → succ-closed l
         → (z : A) → (Has z (dfs y l ac) → Has z l ⊎ Star succ z y) × (Has z l ⊎ Star succ z y → Has z (dfs y l ac)))
      → (l : List A) (ac : Acc succ x) → succ-closed l
      → (y : A) → (Has y (dfs x l ac) → Has y l ⊎ Star succ y x)
                × (Has y l ⊎ Star succ y x → Has y (dfs x l ac))
   go x ih l ac sc y with has x l | recall (λ q → has q l) x
   ... | true  | ⟪ e ⟫ = inl , [ id , star-sc l sc x y (true-reflects (has-r x l) (subst ⟦_⟧ᵇ (sym e) tt)) ]ᵤ
   ... | false | ⟪ e ⟫ =
     let (f , g) = go-list x ih (sucs x) l
                     ac sc (Subset-refl (sucs x)) (λ z Hz Nz → absurd (Nz Hz)) y in
     (λ where
         (here e)   → inr (subst (Star succ y) (sym e) ε)
         (there hy) → [ inl , inr ∘ Plus→Star ]ᵤ (f hy))
     , [ there ∘ g ∘ inl , [ there ∘ g ∘ inr , (here ∘ sym) ]ᵤ ∘ Star→Plus＝ ]ᵤ

   go-list : (x : A)
           → ((y : A) → succ y x → (l : List A) (ac : Acc succ y) → succ-closed l
              → (z : A) → (Has z (dfs y l ac) → Has z l ⊎ Star succ z y) × (Has z l ⊎ Star succ z y → Has z (dfs y l ac)))
           → (l : List A) → (accu : List A)
           → (ac : Acc succ x)
           → succ-closed accu
           → (sub : Subset l (sucs x))
           → (accm : ∀ z → Has z (sucs x) → ¬ Has z l → Has z accu)
           → ∀ y
           → (Has y (dfs-list l accu ac sub) → Has y accu ⊎ Plus succ y x)
           × (Has y accu ⊎ Plus succ y x → Has y (dfs-list l accu ac sub))
   go-list x ih []      accu ac           sc sub accm y =
       inl
     , [ id
       , (λ p → let (s , syc , scx) = Plus-unsnoc p in star-sc (dfs-list [] accu ac sub) sc s y (accm s scx (λ ())) syc)
       ]ᵤ
   go-list x ih (w ∷ l) accu ac@(acc rec) sc sub accm y =
     let zz = ih w (sub w (here refl)) accu (rec w (sub w (here refl))) sc
         ww = go-list x ih l (dfs w accu (rec w (sub w (here refl)))) ac
                  (λ a b ha hs → zz b .snd ([ (λ hha → inl (sc a b hha hs)) , (λ str → inr (hs ◅ str)) ]ᵤ (zz a .fst ha)))
                  (λ z Hz → sub z (there Hz))
                  (λ z Hz Nz → zz z .snd (Dec.elim {C = λ _ → Has z accu ⊎ Star succ z w}
                                                   (λ e → inr (subst (Star succ z) e ε))
                                                   (λ ¬e → inl (accm z Hz (λ where
                                                                               (here e) → ¬e (sym e)
                                                                               (there Hl) → Nz Hl)))
                                                   (z ≟ w)))
                  y
       in
       (λ hh → [ (λ hp → [ inl , (λ str → inr (Star-◅ str (sub w (here refl)))) ]ᵤ (zz y .fst hp) ) , inr ]ᵤ (ww .fst hh))
     , (λ hh → ww .snd ([ (λ hy → inl (zz y .snd (inl hy))) , inr ]ᵤ hh))

dfs-correct : (x : A) → (l : List A) → (ac : Acc succ x)
            → succ-closed l
            → ∀ y
            → (Has y (dfs x l ac) → Has y l ⊎ Star succ y x) × (Has y l ⊎ Star succ y x → Has y (dfs x l ac))
dfs-correct = to-induction succ acy (λ z →
                                    (l : List A) (ac : Acc succ z) →
                                    succ-closed l →
                                    (y : A) →
                                    (Has y (dfs z l ac) → Has y l ⊎ Star succ y z) ×
                                    (Has y l ⊎ Star succ y z → Has y (dfs z l ac)))
   go
