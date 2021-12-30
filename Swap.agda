{-# OPTIONS -v nominal:100 #-}
open import Prelude.Init hiding (swap)
open import Prelude.DecEq

open Meta
open import Prelude.Generics
open Debug ("nominal" , 100)

module Swap (Atom : Set) ⦃ _ : DecEq Atom ⦄ where

open import Swap.Base   Atom ⦃ it ⦄ public
open import Swap.Derive Atom ⦃ it ⦄ public

-- instance
--   ×↔ : ∀ {a b : Level} {A : Set a} {B : Set b}
--     → ⦃ Swap A ⦄
--     → ⦃ Swap B ⦄
--     → Swap (A × B)
--   ×↔ .swap = λ 𝕒 𝕓 → λ where
--     (a , b) → swap 𝕒 𝕓 a , swap 𝕒 𝕓 b
-- unquoteDecl ×↔′ = DERIVE Swap [ quote _×_ , ×↔′ ]
