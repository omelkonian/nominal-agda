open import Prelude.DecEq

module ULC (Atom : Set) ⦃ _ : DecEq Atom ⦄ where

open import ULC.Base    Atom public
open import ULC.Measure Atom public
open import ULC.Alpha   Atom public
