open import Prelude.Init hiding (swap)
open import Prelude.DecEq

module Perm (Atom : Set) ⦃ _ : DecEq Atom ⦄ where

-- postulate 𝕒 𝕓 𝕔 𝕕 : Atom

open import Swap Atom ⦃ it ⦄

-- ** permutations

Perm = List (Atom × Atom)

perm : ⦃ Swap A ⦄ → Perm → A → A
perm = chain ∘ map (uncurry swap)
  where chain = foldr _∘′_ id
