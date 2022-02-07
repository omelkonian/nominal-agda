open import Prelude.Init
open import Prelude.DecEq

module Swap (Atom : Set) ⦃ _ : DecEq Atom ⦄ where

open import Swap.Base   Atom ⦃ it ⦄ public
open import Swap.Derive Atom ⦃ it ⦄ public
