{-# OPTIONS --guarded #-}
module Examples.Quicksort where

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
-- computational all

All : Corr¹ A ℓ′ → List A → 𝒰 ℓ′
All R []       = Lift _ ⊤
All R (x ∷ xs) = R x × All R xs

All-++ : {P : Corr¹ A ℓ′} {xs ys : List A}
       → All P xs → All P ys → All P (xs ++ ys)
All-++ {xs = []}      ax       ay = ay
All-++ {xs = x ∷ xs} (px , ax) ay = px , All-++ ax ay

All-map : {P Q : Corr¹ A ℓ′} {xs : List A}
        → ({x : A} → P x → Q x) → All P xs → All Q xs
All-map     {xs = []}     f  ap      = ap
All-map {P} {xs = x ∷ xs} f (p , ap) = f p , All-map {P = P} f ap

All-map² : {P Q R : Corr¹ A ℓ′} {xs : List A}
         → ({x : A} → P x → Q x → R x) → All P xs → All Q xs → All R xs
All-map²         {xs = []}     f  ap      aq       = ap
All-map² {P} {Q} {xs = x ∷ xs} f (p , ap) (q , aq) = f p q , All-map² {P = P} {Q = Q} f ap aq

Allrel : Corr² (A , A) ℓ′ → List A → List A → 𝒰 ℓ′
Allrel R xs ys = All (λ x → All (R x) ys) xs

Allrel-cons-r : {R : Corr² (A , A) ℓ′} {y : A} {xs ys : List A}
              → All (λ q → R q y) xs → Allrel R xs ys
              → Allrel R xs (y ∷ ys)
Allrel-cons-r = All-map² _,_

Pairwise : Corr² (A , A) ℓ′ → List A → 𝒰 ℓ′
Pairwise R []       = Lift _ ⊤
Pairwise R (x ∷ xs) = All (R x) xs × Pairwise R xs

Pairwise-++ : {R : Corr² (A , A) ℓ′} {xs ys : List A}
            → Allrel R xs ys → Pairwise R xs → Pairwise R ys
            → Pairwise R (xs ++ ys)
Pairwise-++ {xs = []}      a        px       py = py
Pairwise-++ {xs = x ∷ xs} (ay , a) (ax , px) py = All-++ ax ay , Pairwise-++ a px py

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

path→All : ⦃ oA : Ord A ⦄
         → {x : A} {xs : List A}
         → path x xs → All (ole x) xs
path→All {xs = []}      p      = p
path→All {xs = x ∷ xs} (o , p) = o , path→All (path-weaken o p)

path→sorted : ⦃ oA : Ord A ⦄
            → {x : A} {xs : List A}
            → path x xs → sorted xs
path→sorted {xs = []}      p      = p
path→sorted {xs = x ∷ xs} (_ , p) = p

sorted→path : ⦃ oA : Ord A ⦄
            → {x : A} {xs : List A}
            → All (ole x) xs → sorted xs → path x xs
sorted→path {xs = []}      a      s = s
sorted→path {xs = y ∷ xs} (o , a) s = o , s

sorted→pairwise : ⦃ oA : Ord A ⦄
                → {xs : List A}
                → sorted xs → Pairwise ole xs
sorted→pairwise {xs = []}     sx = sx
sorted→pairwise {xs = x ∷ xs} sx =
  (path→All sx) , (sorted→pairwise (path→sorted sx))

pairwise→sorted : ⦃ oA : Ord A ⦄
                → {xs : List A}
                → Pairwise ole xs → sorted xs
pairwise→sorted {xs = []}      p      = p
pairwise→sorted {xs = x ∷ xs} (a , p) = sorted→path a (pairwise→sorted p)

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

All-perm : {P : Corr¹ A ℓ′} {xs ys : List A} → Perm xs ys → All P xs → All P ys
All-perm {P} (p-refl e)        ax            = subst (All P) e ax
All-perm {P} (p-prep e p)     (px , ax)      = subst P e px , All-perm p ax
All-perm {P} (p-swap ex ey p) (px , py , ax) = subst P ey py , subst P ex px , All-perm p ax
All-perm     (p-trans p₁ p₂)   ax            = All-perm p₂ (All-perm p₁ ax)

-- quicksort

partition : ⦃ oA : Ord A ⦄
          → List A → A → List A × List A
partition []       b = [] , []
partition (x ∷ xs) b =
  let l , r = partition xs b in
  if ⌊ x ≤? b ⌋<
    then (x ∷ l) , r
    else l , (x ∷ r)

{-
quicksort : ⦃ oA : Ord A ⦄
          → List A → List A
quicksort []       = []
quicksort (x ∷ xs) =
  let l , r = partition xs x in
  quicksort l ++ x ∷ quicksort r
-}

quicksort-bodyᵏ : ⦃ oA : Ord A ⦄
                → ▹ κ (List A → gPart κ (List A))
                → List A → gPart κ (List A)
quicksort-bodyᵏ q▹ []       = now []
quicksort-bodyᵏ q▹ (x ∷ xs) =
  let l , r = partition xs x in
  map²ᵏ (λ p q → p ++ x ∷ q)
        (later (q▹ ⊛ next l))
        (later (q▹ ⊛ next r))

quicksortᵏ : ⦃ oA : Ord A ⦄
           → List A → gPart κ (List A)
quicksortᵏ = fix quicksort-bodyᵏ

quicksort : ⦃ oA : Ord A ⦄
          → List A → Part (List A)
quicksort l κ = quicksortᵏ l

-- termination & correctness

partition-lengths : ⦃ oA : Ord A ⦄
                  → (l : List A) (b : A)
                  → let xs , ys = partition l b in
                   (length xs ≤ length l) × (length ys ≤ length l)
partition-lengths []      b = z≤ , z≤
partition-lengths (x ∷ l) b with x ≤? b | partition-lengths l b
... | lt x<y x≠y y≮x | (px , py) = (s≤s px) , ≤-trans py ≤-ascend
... | eq x≮y x=y y≮x | (px , py) = (≤-trans px ≤-ascend) , (s≤s py)
... | gt x≮y x≠y y<x | (px , py) = (≤-trans px ≤-ascend) , (s≤s py)

partition-perm : ⦃ oA : Ord A ⦄
               → (l : List A) (b : A)
               → let xs , ys = partition l b in
                 Perm l (xs ++ ys)
partition-perm []      b = p-refl refl
partition-perm (x ∷ l) b with x ≤? b
... | lt x<y x≠y y≮x = p-prep refl (partition-perm l b)
... | eq x≮y x=y y≮x = p-trans (p-prep refl (partition-perm l b)) (perm-sym perm-shift)
... | gt x≮y x≠y y<x = p-trans (p-prep refl (partition-perm l b)) (perm-sym perm-shift)

partition-ole : ⦃ oA : Ord A ⦄
                  → (l : List A) (b : A)
                  → let xs , ys = partition l b in
                    All (_< b) xs × All (ole b) ys
partition-ole []      b = (lift tt) , (lift tt)
partition-ole (x ∷ l) b with x ≤? b | partition-ole l b
... | lt x<y x≠y y≮x | (ax , ay) = (x<y , ax) , ay
... | eq x≮y x=y y≮x | (ax , ay) = ax , (=→ole (sym x=y) , ay)
... | gt x≮y x≠y y<x | (ax , ay) = ax , (<→ole y<x , ay)

quicksort⇓-acc : ⦃ oA : Ord A ⦄
               → ∀ l → Acc (λ x y → length x <ᶜ length y) l
               → Σ[ m ꞉ List A ] (quicksort l ⇓ᵖ m × sorted m × Perm l m)
quicksort⇓-acc []        a        = [] , ∣ 0 , refl ∣₁ , lift tt , p-refl refl
quicksort⇓-acc (x ∷ xs) (acc rec) =
  let
    l , r = partition xs x
    xsl , ysl = partition-lengths xs x
    ol , or = partition-ole xs x
    ql , ql⇓ , qls , qlp = quicksort⇓-acc l (rec l (≤≃<suc .fst xsl))
    qr , qr⇓ , qrs , qrp = quicksort⇓-acc r (rec r (≤≃<suc .fst ysl))
   in
    (ql ++ x ∷ qr)
  , map (λ where
            (qk , qe) →
               suc qk , fun-ext λ κ →
                          quicksortᵏ (x ∷ xs)
                            ＝⟨ ap (λ q → q (x ∷ xs)) (fix-path quicksort-bodyᵏ)  ⟩
                          map²ᵏ (λ p q → p ++ x ∷ q) (δᵏ (quicksortᵏ l)) (δᵏ (quicksortᵏ r))
                            ＝⟨⟩
                          δᵏ (map²ᵏ (λ p q → p ++ x ∷ q) (quicksortᵏ l) (quicksortᵏ r))
                            ＝⟨ ap δᵏ (happly qe κ) ⟩
                          delay-byᵏ (suc qk) (ql ++ x ∷ qr)
                            ∎)
      (map²⇓ (λ p q → p ++ x ∷ q) ql⇓ qr⇓)
  , (pairwise→sorted {xs = ql ++ x ∷ qr} $
      Pairwise-++ {xs = ql} {ys = x ∷ qr}
        (Allrel-cons-r (All-perm qlp (All-map <→ole ol))
                       (All-perm qlp (All-map (λ z<x → All-perm qrp (All-map (ole-trans (<→ole z<x)) or)) ol)))
        (sorted→pairwise qls)
        (All-perm qrp or , (sorted→pairwise qrs)))
  , p-trans (p-prep refl (p-trans (partition-perm xs x) (perm-++-lr qlp qrp))) (perm-sym perm-shift)
