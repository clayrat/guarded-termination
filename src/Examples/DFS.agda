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

private variable
  κ : Cl

succ : A → A → 𝒰 ℓ
succ x y = Has x (sucs y)

-- TODO smth / copypasta

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

succ-closed : List A → 𝒰 ℓ
succ-closed l = ∀ x y → Has x l → succ y x → Has y l

star-sc : ∀ l → succ-closed l
        → ∀ x y
        → Has x l
        → Star succ y x
        → Has y l
star-sc l sc x .x hx  ε             = hx
star-sc l sc x  y hx (_◅_ {b} h st) = sc b y (star-sc l sc x b hx st) h

-- well-founded DFS

mutual
  dfs : (x : A) → (a : List A) → (ac : Acc succ x) → List A
  dfs x a ac = if has x a then a else x ∷ dfs-list (sucs x) a ac (Subset-refl (sucs x))

  -- an inlined left fold
  dfs-list : (l a : List A) → {x : A} → (ac : Acc succ x) → Subset l (sucs x) → List A
  dfs-list  []     a     ac           sub = a
  dfs-list (y ∷ l) a {x} ac@(acc rec) sub =
    dfs-list l
      (dfs y a (rec y (sub y (here refl))))
      {x} ac
      λ z Hz → sub z (there Hz)

dfs0 : A → List A
dfs0 x = dfs x [] (acy x)

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
  where
  go-list : (x : A)
          → ((y : A) → succ y x → (l : List A) (ac : Acc succ y) → succ-closed l
             → (z : A) → (Has z (dfs y l ac) → Has z l ⊎ Star succ z y) × (Has z l ⊎ Star succ z y → Has z (dfs y l ac)))
          → (l : List A) → (accu : List A)
          → (ac : Acc succ x)
          → succ-closed accu
          → (sub : Subset l (sucs x))
          → (∀ z → succ z x → ¬ Has z l → Has z accu)
          → ∀ y
          → (Has y (dfs-list l accu ac sub) → Has y accu ⊎ Plus succ y x)
          × (Has y accu ⊎ Plus succ y x → Has y (dfs-list l accu ac sub))
  go-list x ih []      accu ac           sc sub accm y =
      inl
    , [ id
      , (λ p → let (s , syc , scx) = Plus-unsnoc p in
               star-sc (dfs-list [] accu ac sub) sc s y (accm s scx ¬Any-[]) syc)
      ]ᵤ
  go-list x ih (w ∷ l) accu ac@(acc rec) sc sub accm y =
    let swx : succ w x
        swx = sub w (here refl)
        ihw = ih w swx accu (rec w swx) sc
        ihl = go-list x ih l (dfs w accu (rec w swx)) ac
                 (λ a b ha hs → ihw b .snd ([ (λ hha → inl (sc a b hha hs)) , (λ str → inr (hs ◅ str)) ]ᵤ (ihw a .fst ha)))
                 (λ z Hz → sub z (there Hz))
                 (λ z Hz Nz → ihw z .snd (Dec.rec (λ e → inr (subst (Star succ z) e ε))
                                                  (λ ¬e → inl (accm z Hz (¬Any-∷ (¬e ∘ sym) Nz)))
                                                  (z ≟ w)))
                 y
      in
      (λ hh → [ (λ hp → [ inl , (λ str → inr (Star-◅ str swx)) ]ᵤ (ihw y .fst hp) ) , inr ]ᵤ (ihl .fst hh))
    , (λ hh → ihl .snd ([ (λ hy → inl (ihw y .snd (inl hy))) , inr ]ᵤ hh))

  go : (x : A)
     → ((y : A) → succ y x → (l : List A) (ac : Acc succ y) → succ-closed l
        → (z : A) → (Has z (dfs y l ac) → Has z l ⊎ Star succ z y) × (Has z l ⊎ Star succ z y → Has z (dfs y l ac)))
     → (l : List A) (ac : Acc succ x) → succ-closed l
     → (y : A) → (Has y (dfs x l ac) → Has y l ⊎ Star succ y x)
               × (Has y l ⊎ Star succ y x → Has y (dfs x l ac))
  go x ih l ac sc y with has x l | recall (λ q → has q l) x
  ... | true  | ⟪ e ⟫ = inl , [ id , star-sc l sc x y (true-reflects (has-r x l) (subst ⟦_⟧ᵇ (sym e) tt)) ]ᵤ
  ... | false | _     =
    let (f , g) = go-list x ih (sucs x) l ac sc
                    (Subset-refl (sucs x)) (λ z Hz Nz → absurd (Nz Hz)) y
      in
    (λ where
        (here e)   → inr (subst (Star succ y) (sym e) ε)
        (there hy) → [ inl , inr ∘ Plus→Star ]ᵤ (f hy))
    , [ there ∘ g ∘ inl , [ there ∘ g ∘ inr , (here ∘ sym) ]ᵤ ∘ Star→Plus＝ ]ᵤ

-- DFS finds all reachable nodes
dfs0-correct : (x : A)
             → ∀ y
             → (Has y (dfs0 x) → Star succ y x) × (Star succ y x → Has y (dfs0 x))
dfs0-correct x y =
  let (f , g) = dfs-correct x [] (acy x) (λ _ _ h _ → absurd (¬Any-[] h)) y in
    [ (λ h → absurd (¬Any-[] h)) , id ]ᵤ ∘ f
  , g ∘ inr

-- coinductive

-- TODO move + generalize level
foldlᵏ : {B : 𝒰 ℓ}
       → (B → A → ▹ κ (gPart κ B))
       → B → List A → gPart κ B
foldlᵏ f x []       = now x
foldlᵏ f x (a ∷ as) = later (((λ q → foldlᵏ f q as) =<<ᵏ_) ⍉ f x a)

-- TODO we should probably have some combinators for foldlᵏ

dfs-listᵏ-body : ▹ κ (A → List A → gPart κ (List A))
               → List A → List A → gPart κ (List A)
dfs-listᵏ-body d▹ l a = foldlᵏ (λ y b → d▹ ⊛ next b ⊛ next y) a l

dfsᵏ-body : ▹ κ (A → List A → gPart κ (List A))
          → A → List A → gPart κ (List A)
dfsᵏ-body d▹ x a = if has x a then now a else mapᵏ (x ∷_) (dfs-listᵏ-body d▹ (sucs x) a)

dfsᵏ : A → List A → gPart κ (List A)
dfsᵏ = fix dfsᵏ-body

dfsᶜ : A → List A → Part (List A)
dfsᶜ x a κ = dfsᵏ x a

-- termination

dfs-listᵏ : List A → List A → gPart κ (List A)
dfs-listᵏ = dfs-listᵏ-body (dfix dfsᵏ-body)

dfs-listᶜ : List A → List A → Part (List A)
dfs-listᶜ l a κ = dfs-listᵏ l a

mutual
  dfsᶜ⇓ : (x : A) → (a : List A) → Acc succ x → dfsᶜ x a ⇓
  dfsᶜ⇓ x a ac with has x a
  ... | true  = a , ∣ 0 , refl ∣₁
  ... | false =
    let (q , q⇓) = dfs-listᶜ⇓ (sucs x) a ac (Subset-refl (sucs x)) in
    (x ∷ q) , (map⇓ (x ∷_) q⇓)

  dfs-listᶜ⇓ : (l a : List A) → {x : A} → Acc succ x → Subset l (sucs x) → dfs-listᶜ l a ⇓
  dfs-listᶜ⇓ []      a     ac           sub = a , ∣ 0 , refl ∣₁
  dfs-listᶜ⇓ (y ∷ l) a {x} ac@(acc rec) sub =
    let (q , q⇓) = dfsᶜ⇓ y a (rec y (sub y (here refl)))
        (z , z⇓) = dfs-listᶜ⇓ l q {x} ac (λ z Hz → sub z (there Hz))
      in
    z , (map (λ qke → let (qk , qe) = qke in  -- splitting this directly breaks termination checker for some reason
                   (suc qk)
                 , fun-ext λ κ →
                     dfs-listᵏ (y ∷ l) a
                       ＝⟨⟩
                     later ((dfs-listᵏ l =<<ᵏ_) ⍉ (dfix dfsᵏ-body ⊛ next y ⊛ next a))
                       ＝⟨ ap later (▹-ext λ α → ap (dfs-listᵏ l =<<ᵏ_) λ i → pfix dfsᵏ-body i α y a) ⟩
                     δᵏ (dfs-listᵏ l =<<ᵏ dfsᵏ y a)
                       ＝⟨ ap δᵏ (happly qe κ) ⟩
                     delay-byᵏ (suc qk) z
                       ∎)
             (bind⇓ (dfs-listᶜ l) q⇓ z⇓))
