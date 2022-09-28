open import Prelude.Init
open SetAsType
open import Prelude.DecEq
open import Prelude.InfEnumerable

module Nominal (Atom : Type) ⦃ _ : DecEq Atom ⦄ where

open import Nominal.Swap    Atom public
open import Nominal.Perm    Atom public
open import Nominal.Abs     Atom public
open import Nominal.Support Atom public
open import Nominal.Fun     Atom public
