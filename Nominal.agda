open import Prelude.Init
open import Prelude.DecEq

module Nominal (Atom : Set) ⦃ _ : DecEq Atom ⦄ where

open import Swap Atom public
open import Perm Atom public
open import Abs  Atom public
open import New  Atom public
