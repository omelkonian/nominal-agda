open import Prelude.Init
open SetAsType
open import Prelude.DecEq

module Nominal.Abs (Atom : Type) ⦃ _ : DecEq Atom ⦄ where

open import Nominal.Abs.Base    Atom ⦃ it ⦄ public
open import Nominal.Abs.Lift    Atom ⦃ it ⦄ public
-- open import Nominal.Abs.Functor Atom public
