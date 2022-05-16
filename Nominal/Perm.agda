open import Prelude.Init
open import Prelude.DecEq

module Nominal.Perm (Atom : Set) ⦃ _ : DecEq Atom ⦄ where

open import Nominal.Swap Atom

private variable A : Set ℓ

-- ** permutations
Perm = List (Atom × Atom)

perm : ⦃ Swap A ⦄ → Perm → A → A
perm = chain ∘ map (uncurry swap)
  where chain = foldr _∘′_ id
