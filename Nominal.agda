open import Prelude.Init
open import Prelude.DecEq

module Nominal (Atom : Set) ⦃ _ : DecEq Atom ⦄ where

open import Nominal.Swap Atom public
open import Nominal.Perm Atom public
open import Nominal.Abs Atom public
open import Nominal.New Atom public
open import Nominal.Support Atom public
-- open import Nominal.Fresh Atom public
