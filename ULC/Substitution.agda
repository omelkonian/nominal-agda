open import Prelude.Init
open SetAsType
open import Prelude.DecEq
open import Prelude.DecLists
open import Prelude.Measurable
open import Prelude.InfEnumerable
open import Prelude.Setoid

-- ** Substitution.
module ULC.Substitution (Atom : Type) ⦃ _ : DecEq Atom ⦄ ⦃ _ : Enumerable∞ Atom ⦄ where

open import ULC.Base    Atom
open import ULC.Measure Atom
open import ULC.Alpha   Atom
open import Nominal     Atom

-- specialized version of `mapAbs` for Term
-- mapAbs-Term : (x' : Abs Term) → (∀ (t : Term) → t ≺ᵐ x' → Term) → Abs Term
-- mapAbs-Term x' f =
--   let a , _ = fresh (supp x' ++ supp?? f)
--   in abs a (f (conc x' a) (conc≺ x' a))

-- capture-avoiding application
-- conc† : Abs Term → Atom → Term
-- conc† f@(abs x t) y =
--   let z , _ = fresh (y ∷ supp f)
--   in conc (⦅ x ↔ z ⦆ f) y

_[_/_] : Term → Atom → Term → Term
t₀ [ 𝕒 / s ] = ≺-rec _ go t₀
  where
    go : ∀ x → (∀ y → y ≺ x → Term) → Term
    go x rec with x
    ... | ` x   = if x == 𝕒 then s else ` x
    ... | l · m = rec l (l ·≺ˡ m) · rec m (l ·≺ʳ m)
    -- Cannot simply use `ƛ (mapAbs go f)` here; need well-founded recursion
    -- ... | ƛ f   = ƛ mapAbs-Term f (λ t t≺ → rec t t≺)
    ... | ƛ f =
      let y , _ = fresh (nub $ 𝕒 ∷ supp f ++ supp s)
      in  ƛ y ⇒ rec (conc f y) (conc≺ f y)

-- enforce the Barendregt convention: no shadowing, distinct bound variables
-- T0D0: fix
barendregt : Op₁ Term
barendregt = λ where
  (` x)     → ` x
  (l · r)   → barendregt l · barendregt r
  (ƛ a ⇒ t) → ƛ freshen (abs a $ barendregt t)
