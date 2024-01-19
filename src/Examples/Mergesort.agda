{-# OPTIONS --guarded #-}
module Examples.Mergesort where

open import Prelude
open import Data.Bool
open import Data.Dec
open import Data.Sum
open import Data.Nat
open import Data.Nat.Order.Base renaming (_<_ to _<ᶜ_)
open import Data.List
open import Correspondences.Wellfounded

open import Later
open import Clocked.Partial
open import Clocked.Partial.Converges

private variable
  κ : Cl
  ℓ ℓ′ : Level
  A : 𝒰 ℓ

-- TODO copypasta
Acc-on : {ℓ″ : Level} {B : 𝒰 ℓ′} {_≺_ : Corr² (A , A) ℓ″} (f : B → A) (b : B)
       → Acc _≺_ (f b) → Acc (λ x y → f x ≺ f y) b
Acc-on f b (acc rec) = acc λ y p → Acc-on f y (rec (f y) p)

-- TODO upstream
-- adjacent + sorted

Adj0 : Corr² (A , A) ℓ′ → A → List A → 𝒰 ℓ′
Adj0 R x []       = Lift _ ⊤
Adj0 R x (y ∷ ys) = R x y × Adj0 R y ys

Adj : Corr² (A , A) ℓ′ → List A → 𝒰 ℓ′
Adj R []       = Lift _ ⊤
Adj R (x ∷ xs) = Adj0 R x xs

ole : ⦃ oA : Ord A ⦄
    → Corr² (A , A) (level-of-type A ⊔ oA .Ord.ℓo)
ole x y = (x ＝ y) ⊎₁ (x < y)  -- truncated to match _<_

=→ole : ⦃ oA : Ord A ⦄
      → {x y : A}
      → x ＝ y → ole x y
=→ole x=y = ∣ inl x=y ∣₁

<→ole : ⦃ oA : Ord A ⦄
      → {x y : A}
      → x < y → ole x y
<→ole x<y = ∣ inr x<y ∣₁

ole-trans : ⦃ oA : Ord A ⦄
          → {x y z : A}
          → ole x y → ole y z → ole x z
ole-trans ⦃ oA ⦄ {x} {z} =
  map² λ where
     (inl e)   oyz     → subst (λ q → (q ＝ z) ⊎ (q < z)) (sym e) oyz
     (inr ly) (inl e)  → inr (subst (x <_) e ly)
     (inr ly) (inr lz) → inr (oA .Ord.<-trans ly lz)

path : ⦃ oA : Ord A ⦄
      → A → List A → 𝒰 (level-of-type A ⊔ oA .Ord.ℓo)
path = Adj0 ole

sorted : ⦃ oA : Ord A ⦄
       → List A → 𝒰 (level-of-type A ⊔ oA .Ord.ℓo)
sorted = Adj ole

path-weaken : ⦃ oA : Ord A ⦄
          → {a b : A} {xs : List A}
          → ole a b → path b xs → path a xs
path-weaken {xs = []}      oab  pb       = pb
path-weaken {xs = x ∷ xs}  oab (hb , pb) = ole-trans oab hb , pb

-- permutation

data Perm {A : 𝒰 ℓ} : List A → List A → 𝒰 (level-of-type A) where
  p-refl  : ∀ {xs ys}
          → xs ＝ ys → Perm xs ys
  p-prep  : ∀ {xs ys x y}
          → x ＝ y → Perm xs ys → Perm (x ∷ xs) (y ∷ ys)
  p-swap  : ∀ {xs ys x y x′ y′}
          → x ＝ x′ → y ＝ y′ → Perm xs ys → Perm (x ∷ y ∷ xs) (y′ ∷ x′ ∷ ys)
  p-trans : ∀ {xs ys zs}
          → Perm xs ys → Perm ys zs → Perm xs zs

perm-sym : {xs ys : List A} → Perm xs ys → Perm ys xs
perm-sym (p-refl e)       = p-refl (sym e)
perm-sym (p-prep e p)     = p-prep (sym e) (perm-sym p)
perm-sym (p-swap ex ey p) = p-swap (sym ey) (sym ex) (perm-sym p)
perm-sym (p-trans p₁ p₂)  = p-trans (perm-sym p₂) (perm-sym p₁)

perm-shift : {xs ys : List A} {z : A} → Perm (xs ++ z ∷ ys) (z ∷ xs ++ ys)
perm-shift {xs = []}     = p-refl refl
perm-shift {xs = x ∷ xs} = p-trans (p-prep refl perm-shift) (p-swap refl refl (p-refl refl))

perm-++-l : {xs ys zs : List A} → Perm ys zs → Perm (xs ++ ys) (xs ++ zs)
perm-++-l {xs = []}     pyz = pyz
perm-++-l {xs = x ∷ xs} pyz = p-prep refl (perm-++-l {xs = xs} pyz)

perm-++-r : {xs ys zs : List A} → Perm xs ys → Perm (xs ++ zs) (ys ++ zs)
perm-++-r {zs} (p-refl e)       = p-refl (ap (_++ zs) e)
perm-++-r      (p-prep e p)     = p-prep e (perm-++-r p)
perm-++-r      (p-swap ex ey p) = p-swap ex ey (perm-++-r p)
perm-++-r      (p-trans p₁ p₂)  = p-trans (perm-++-r p₁) (perm-++-r p₂)

perm-++-lr : {as bs xs ys : List A} → Perm as xs → Perm bs ys → Perm (as ++ bs) (xs ++ ys)
perm-++-lr pax pby = p-trans (perm-++-r pax) (perm-++-l pby)

perm-++-comm : {xs ys : List A} → Perm (xs ++ ys) (ys ++ xs)
perm-++-comm {xs = []}     {ys} = p-refl (sym (++-id-r ys))
perm-++-comm {xs = x ∷ xs}      = perm-sym (p-trans perm-shift (p-prep refl (perm-sym (perm-++-comm {xs = xs}))))

-- merge sort

split : List A → List A × List A
split  []         = [] , []
split (x ∷ [])    = x ∷ [] , []
split (x ∷ y ∷ l) =
  let xs , ys = split l in
  x ∷ xs , y ∷ ys

merge : ⦃ oA : Ord A ⦄
      → List A → List A → List A
merge []          ys      = ys
merge xs@(_ ∷ _)  []      = xs
merge (x ∷ xs)   (y ∷ ys) =
  if ⌊ x ≤? y ⌋<
    then x ∷ merge xs (y ∷ ys)
    else y ∷ merge (x ∷ xs) ys

{-
mergesort : ⦃ oA : Ord A ⦄
          → List A → List A
mergesort []          = []
mergesort (x ∷ [])    = x ∷ []
mergesort (x ∷ y ∷ l) =
  let xs , ys = split l in
  merge (mergesort (x ∷ xs)) (mergesort (y ∷ xs))
-}

mergesort-bodyᵏ : ⦃ oA : Ord A ⦄
                → ▹ κ (List A → gPart κ (List A))
                → List A → gPart κ (List A)
mergesort-bodyᵏ m▹ []          = now []
mergesort-bodyᵏ m▹ (x ∷ [])    = now (x ∷ [])
mergesort-bodyᵏ m▹ (x ∷ y ∷ l) =
  let xs , ys = split l in
  map²ᵏ merge (later (m▹ ⊛ next (x ∷ xs))) (later (m▹ ⊛ next (y ∷ ys)))

mergesortᵏ : ⦃ oA : Ord A ⦄
           → List A → gPart κ (List A)
mergesortᵏ = fix mergesort-bodyᵏ

mergesort : ⦃ oA : Ord A ⦄
          → List A → Part (List A)
mergesort l κ = mergesortᵏ l

-- termination & correctness

split-perm : (l : List A)
           → let xs , ys = split l in
           Perm l (xs ++ ys)
split-perm []          = p-refl refl
split-perm (x ∷ [])    = p-refl refl
split-perm (x ∷ y ∷ l) =
  let p = split-perm l in
  p-prep refl (p-trans (p-prep refl p) (perm-sym perm-shift))

-- both should actually be in [ |l|/2↓ , |l|/2↑ ]
split-lengths : (l : List A)
              → let xs , ys = split l in
              (length xs ≤ length l) × (length ys ≤ length l)
split-lengths []          = z≤ , z≤
split-lengths (x ∷ [])    = ≤-refl , z≤
split-lengths (x ∷ y ∷ l) =
  let q , r = split-lengths l in
   s≤s (≤-trans {m = length (split l .fst)} q (≤-ascend {n = length l}))
 , s≤s (≤-trans {m = length (split l .snd)} r (≤-ascend {n = length l}))

merge-path : ⦃ oA : Ord A ⦄
           → {xs ys : List A} → {z : A}
           → path z xs → path z ys
           → path z (merge xs ys)
merge-path {xs = []}                        px        py       = py
merge-path {xs = _ ∷ _}  {ys = []}          px        py       = px
merge-path {xs = x ∷ xs} {ys = y ∷ ys} {z} (hx , px) (hy , py) =
  -- need an eliminator to pacify the termination checker
  Tri-elim
    {C = λ t → path z (if ⌊ t ⌋< then x ∷ merge xs (y ∷ ys) else y ∷ merge (x ∷ xs) ys)}
    (λ x<y x≠y y≮x → hx , merge-path {xs = xs} {ys = y ∷ ys} {z = x} px (<→ole x<y , py))
    (λ x≮y x=y y≮x → hy , merge-path {xs = x ∷ xs} {ys = ys} {z = y} (=→ole (sym x=y) , px) py)
    (λ x≮y x≠y y<x → hy , merge-path {xs = x ∷ xs} {ys = ys} {z = y} (<→ole y<x , px) py)
    (x ≤? y)

merge-sorted : ⦃ oA : Ord A ⦄
             → {xs ys : List A}
             → sorted xs → sorted ys
             → sorted (merge xs ys)
merge-sorted {xs = []}                   sx sy = sy
merge-sorted {xs = _ ∷ _}  {ys = []}     sx sy = sx
merge-sorted {xs = x ∷ xs} {ys = y ∷ ys} sx sy with x ≤? y
... | lt x<y x≠y y≮x = merge-path sx (<→ole x<y , sy)
... | eq x≮y x=y y≮x = merge-path (=→ole (sym x=y) , sx) sy
... | gt x≮y x≠y y<x = merge-path (<→ole y<x , sx) sy

merge-perm : ⦃ oA : Ord A ⦄
           → {xs ys : List A}
           → Perm (xs ++ ys) (merge xs ys)
merge-perm {xs = []}     {ys}          = p-refl refl
merge-perm {xs = x ∷ xs} {ys = []}     = p-refl (++-id-r (x ∷ xs))
merge-perm {xs = x ∷ xs} {ys = y ∷ ys} with x ≤? y | merge-perm {xs = xs} {ys = y ∷ ys} | merge-perm {xs = x ∷ xs} {ys = ys}
... | lt x<y x≠y y≮x | m1 | m2 = p-prep refl m1
... | eq x≮y x=y y≮x | m1 | m2 = p-trans (perm-shift {xs = x ∷ xs}) (p-prep refl m2)
... | gt x≮y x≠y y<x | m1 | m2 = p-trans (perm-shift {xs = x ∷ xs}) (p-prep refl m2)

mergesort⇓-acc : ⦃ oA : Ord A ⦄
               → ∀ l → Acc (λ x y → length x <ᶜ length y) l
               → Σ[ m ꞉ List A ] (mergesort l ⇓ᵖ m × sorted m × Perm l m)
mergesort⇓-acc []           a            = [] , ∣ 0 , refl ∣₁ , lift tt , p-refl refl
mergesort⇓-acc (x ∷ [])     a            = (x ∷ []) , ∣ 0 , refl ∣₁ , lift tt , p-refl refl
mergesort⇓-acc (x ∷ y ∷ l) (acc rec) =
  let xs , ys = split l
      xsl , ysl = split-lengths l
      q , q⇓ , qs , qp = mergesort⇓-acc (x ∷ xs) (rec (x ∷ xs) (≤≃<suc .fst (s≤s xsl)))
      r , r⇓ , rs , rp = mergesort⇓-acc (y ∷ ys) (rec (y ∷ ys) (≤≃<suc .fst (s≤s ysl)))
   in
     (merge q r)
    , map
        (λ where
             (zk , ze) →
                suc zk , (fun-ext λ κ →
                            mergesortᵏ (x ∷ y ∷ l)
                              ＝⟨ ap (λ q → q (x ∷ y ∷ l)) (fix-path mergesort-bodyᵏ) ⟩
                            map²ᵏ merge (δᵏ (mergesortᵏ (x ∷ xs))) (δᵏ (mergesortᵏ (y ∷ ys)))
                              ＝⟨⟩
                            δᵏ (map²ᵏ merge (mergesortᵏ (x ∷ xs)) (mergesortᵏ (y ∷ ys)))
                              ＝⟨ ap δᵏ (happly ze κ) ⟩
                            delay-byᵏ (suc zk) (merge q r)
                              ∎))
        (map²⇓ merge q⇓ r⇓)
    , merge-sorted {xs = q} qs rs
    , p-trans
        (p-trans (p-prep refl (p-trans (p-prep refl (split-perm l)) (perm-sym perm-shift)))
                 (perm-++-lr qp rp))
        (merge-perm {xs = q} {ys = r})

mergesort⇓ : ⦃ oA : Ord A ⦄
           → ∀ l
           → Σ[ m ꞉ List A ] (mergesort l ⇓ᵖ m × sorted m × Perm l m)
mergesort⇓ l = mergesort⇓-acc l (Acc-on length l (<-wf (length l)))
