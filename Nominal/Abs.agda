open import Prelude.Init
open import Prelude.DecEq

module Nominal.Abs (Atom : Set) ⦃ _ : DecEq Atom ⦄ where

open import Nominal.Abs.Base    Atom public
open import Nominal.Abs.Lift    Atom public
open import Nominal.Abs.Functor Atom public
