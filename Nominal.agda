open import Prelude.Init; open SetAsType
open import Prelude.DecEq

module Nominal (Atom : Type) ⦃ _ : DecEq Atom ⦄ where

open import Nominal.New Atom public
open import Nominal.Swap Atom public
open import Nominal.Perm Atom public

open import Nominal.Support Atom public
open import Nominal.MinSupport Atom public

open import Nominal.Fun Atom public
open import Nominal.Abs Atom public

-- open import Nominal.Product Atom public
-- [BUG]
-- Don't export this together with Abs!
-- Otherwise instance resolution fails for no reason
-- as demonstrated by the example imported below.
open import Nominal.ImportIssue
