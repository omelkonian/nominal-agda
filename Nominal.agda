open import Prelude.Init
open SetAsType
open import Prelude.DecEq
open import Prelude.InfEnumerable

module Nominal (Atom : Type) ⦃ _ : DecEq Atom ⦄ where

open import Nominal.Swap    Atom ⦃ it ⦄ public
open import Nominal.Perm    Atom ⦃ it ⦄ public
open import Nominal.Fun     Atom ⦃ it ⦄ public
open import Nominal.Abs     Atom ⦃ it ⦄ public
open import Nominal.Product Atom ⦃ it ⦄ public
open import Nominal.Support Atom ⦃ it ⦄ public
