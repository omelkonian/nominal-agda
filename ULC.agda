open import Prelude.Init; open SetAsType
open import Prelude.DecEq

module ULC (Atom : Type) ⦃ _ : DecEq Atom ⦄ where

open import ULC.Base         Atom public
open import ULC.Measure      Atom public
open import ULC.Alpha        Atom public
open import ULC.Substitution Atom public
open import ULC.Reduction    Atom public
