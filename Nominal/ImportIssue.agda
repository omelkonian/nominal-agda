{-# OPTIONS --allow-unsolved-metas #-}
open import Prelude.Init; open SetAsType
open import Prelude.DecEq
open import Prelude.Setoid

module Nominal.ImportIssue (Atom : Type) ⦃ _ : DecEq Atom ⦄ where

open import Nominal.Swap    Atom
-- importing both abstractions and products confuses instance resolution
open import Nominal.Abs     Atom
open import Nominal.Product Atom

module _ {A : Type} ⦃ _ : ISetoid A ⦄ ⦃ _ : Swap A ⦄ where

  private variable 𝕒 𝕓 : Atom

  _ : ∀ {x y : Atom × Atom} → x ≈ y → ⦅ 𝕒 ↔ 𝕓 ⦆ x ≈ ⦅ 𝕒 ↔ 𝕓 ⦆ y
  _ = cong-swap

  _ : ∀ {x y : Abs Atom} → x ≈ y → ⦅ 𝕒 ↔ 𝕓 ⦆ x ≈ ⦅ 𝕒 ↔ 𝕓 ⦆ y
  _ = cong-swap
  -- _ = cong-swap {A = Abs _} -- this works
