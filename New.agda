open import Prelude.Init
open import Prelude.DecEq

module New (Atom : Set) ⦃ _ : DecEq Atom ⦄ where

-- ** The И quantifier.
И : Pred₀ (Pred₀ Atom)
И φ = ∃ λ (xs : List Atom) → (∀ y → y L.Mem.∉ xs → φ y)

-- ** the co-finite construction leads to issues with universe levels.
-- open import Cofinite.agda
-- И : Pred (Pred Atom ℓ) (lsuc ℓ)
-- И P = powᶜᵒᶠ P
