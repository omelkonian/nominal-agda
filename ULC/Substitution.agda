open import Prelude.Init; open SetAsType
open import Prelude.General
open import Prelude.DecEq
open import Prelude.DecLists
open import Prelude.Measurable
open import Prelude.InfEnumerable
open import Prelude.Setoid

-- ** Substitution.
module ULC.Substitution (Atom : Type) ⦃ _ : DecEq Atom ⦄ ⦃ _ : Enumerable∞ Atom ⦄ where

open import ULC.Base    Atom ⦃ it ⦄
open import ULC.Measure Atom ⦃ it ⦄ ⦃ it ⦄
open import ULC.Alpha   Atom ⦃ it ⦄ ⦃ it ⦄
open import Nominal Atom
open import Nominal.Product Atom

infix 6 _[_/_]
{-# TERMINATING #-}
_[_/_] : Term → Atom → Term → Term
(` x) [ 𝕒 / N ] = if x == 𝕒 then N else ` x
(L · M) [ 𝕒 / N ] =
  let L′ = L [ 𝕒 / N ]
      M′ = M [ 𝕒 / N ]
  in L′ · M′
(ƛ t̂) [ 𝕒 / N ] =
  let y = fresh-var (𝕒 , t̂ , N)
  -- let y , _ = minFresh (𝕒 ∷ supp t̂ ++ supp N)
  in ƛ y ⇒ conc t̂ y [ 𝕒 / N ]

{- ** well-founded version
t₀ [ 𝕒 / s ] = ≺-rec _ go t₀
  module ∣Substitution∣ where
    go : ∀ x → (∀ y → y ≺ x → Term) → Term
    go x rec with x
    ... | ` x   = if x == 𝕒 then s else ` x
    ... | l · m = rec l (l ·≺ˡ m) · rec m (l ·≺ʳ m)
    -- Cannot simply use `ƛ (mapAbs go f)` here; need well-founded recursion
    -- ... | ƛ f   = ƛ mapAbs-Term f (λ t t≺ → rec t t≺)
    ... | ƛ f =
      let y , _ = fresh (nub $ 𝕒 ∷ supp f ++ supp s)
      in  ƛ y ⇒ rec (conc f y) (conc≺ f y)
-}

{-
-- specialized version of `mapAbs` for Term
mapAbs-Term : (x' : Abs Term) → (∀ (t : Term) → t ≺ᵐ x' → Term) → Abs Term
mapAbs-Term x' f =
  let a , _ = fresh (supp x' ++ supp?? f)
  in abs a (f (conc x' a) (conc≺ x' a))

-- ⋯ (ƛ f) → ƛ mapAbs _[ 𝕒 / s ] f

-- capture-avoiding application
conc† : Abs Term → Atom → Term
conc† f@(abs x t) y =
  let z , _ = fresh (y ∷ supp f)
  in conc (⦅ x ↔ z ⦆ f) y
-}

subs : List (Atom × Term) → Op₁ Term
subs = λ where
  [] t → t
  ((𝕒 , s) ∷ σ) t → subs σ (t [ 𝕒 / s ])

sub-ξ : (L · M) [ x / N ] ≡ (L [ x / N ]) · (M [ x / N ])
sub-ξ = refl

sub-ƛ : (ƛ x ⇒ N) [ y / M ] ≡
  (let x′ , _ = minFresh (y ∷ x ∷ supp N ++ supp M)
   in ƛ x′ ⇒ swap x′ x N [ y / M ])
sub-ƛ = refl

-- T0D0: unifying with `conc`
infix 5 _[_]
_[_] : Abs Term → Term → Term
t̂@(abs x t) [ s ] = ƛ t̂ [ x / s ]

{-
-- T0D0: fix
-- enforce the Barendregt convention: no shadowing, distinct bound variables
barendregt : Op₁ Term
barendregt = λ where
  (` x)     → ` x
  (l · r)   → barendregt l · barendregt r
  (ƛ a ⇒ t) → ƛ freshen (abs a $ barendregt t)
-}
