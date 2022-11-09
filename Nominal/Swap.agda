open import Prelude.Init; open SetAsType
open import Prelude.DecEq

module Nominal.Swap (Atom : Type) ⦃ _ : DecEq Atom ⦄ where

open import Nominal.Swap.Base   Atom public
open import Nominal.Swap.Derive Atom public
