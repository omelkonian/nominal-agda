open import Prelude.Init
open import Prelude.DecEq

module Nominal.Swap (Atom : Set) ⦃ _ : DecEq Atom ⦄ where

open import Nominal.Swap.Base   Atom public
open import Nominal.Swap.Derive Atom public
