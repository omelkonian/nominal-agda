open import Prelude.Init
open SetAsType
open import Prelude.DecEq
open import Prelude.General
open import Prelude.Closures
open import Prelude.InferenceRules
open import Prelude.Decidable
open import Prelude.Membership

module ULC.Base (Atom : Set) ⦃ _ : DecEq Atom ⦄ where

open import Nominal Atom

-- ** ULC terms.
data Term : Type where
  _·_ : Op₂ Term
  `_ : Atom → Term
  ƛ_ : Abs Term → Term
-- unquoteDecl Swap-Term = DERIVE Swap [ quote Term , Swap-Term ]

instance
  {-# TERMINATING #-}
  Swap-Term : Swap Term
  Swap-Term .swap 𝕒 𝕓 = λ where
    (t · t′) → swap 𝕒 𝕓 t · swap 𝕒 𝕓 t′
    (` x)    → ` swap 𝕒 𝕓 x
    (ƛ f)    → ƛ swap 𝕒 𝕓 f

infix  30 `_
infixl 20 _·_
infixr 10 ƛ_
infixr 5 ƛ_⇒_
pattern ƛ_⇒_ x y = ƛ abs x y

variable
  x y 𝕩 𝕪 𝕫 : Atom
  t t′ t″ w w′ w″ L L′ M M′ N N′ M₁ M₂ : Term
