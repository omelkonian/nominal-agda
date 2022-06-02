open import Prelude.Init
open import Prelude.DecEq

-- ** Substitution.
module ULC.Substitution (Atom : Set) ⦃ _ : DecEq Atom ⦄ where

open import ULC.Base
open import Nominal Atom

{-# TERMINATING #-}
_[_↝_] : Term → Atom → Term → Term
t₀ [ 𝕒 ↝ s ] = go t₀
  where
    go : Term → Term
    go = λ where
      (` x)    → if x == 𝕒 then s else ` x
      (t · t′) → go t · go t′
      (ƛ f)    → ƛ (mapAbs go f)
