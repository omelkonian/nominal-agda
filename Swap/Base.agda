open import Prelude.Init hiding (swap)
open import Prelude.DecEq

module Swap.Base (Atom : Set) ⦃ _ : DecEq Atom ⦄ where

variable A : Set ℓ

record Swap (A : Set ℓ) : Set ℓ where
  field swap : Atom → Atom → A → A
open Swap ⦃...⦄ public

instance
  Atom↔ : Swap Atom
  Atom↔ .swap a₁ a₂ a =
    if      a == a₁ then a₂
    else if a == a₂ then a₁
    else                 a

swapId : Atom → Atom → A → A
swapId _ _ = id

-- ** Nameless
record Nameless (A : Set ℓ) : Set ℓ where
  field ⦃ register ⦄ : ⊤
open Nameless ⦃...⦄

instance
  ⊤∅      = Nameless ⊤ ∋ it
  Bool∅   = Nameless Bool ∋ it
  ℕ∅      = Nameless ℕ ∋ it
  Char∅   = Nameless Char ∋ it
  String∅ = Nameless String ∋ it

  -- Nameless↔ : ⦃ Nameless A ⦄ → Swap A
  -- Nameless↔ .swap = swapId
