open import Prelude.Init; open SetAsType
open L.Mem
open import Prelude.DecEq
open import Prelude.InfEnumerable
open import Prelude.Setoid
-- open import Prelude.Bifunctor
-- open import Prelude.InferenceRules

module Nominal.Abs.Product (Atom : Type) ⦃ _ : DecEq Atom ⦄ ⦃ _ : Enumerable∞ Atom ⦄ where

open import Nominal.New      Atom
open import Nominal.Swap     Atom
open import Nominal.Support  Atom
open import Nominal.Abs.Base Atom
open import Nominal.Product  Atom
open import Nominal.Abs.Support Atom

module _
  {A : Type ℓ} {B : Type ℓ′}
  ⦃ _ : ISetoid A ⦄ ⦃ _ : ISetoid B ⦄
  ⦃ _ : SetoidLaws A ⦄ ⦃ _ : SetoidLaws B ⦄
  ⦃ _ : Swap A ⦄ ⦃ _ : Swap B ⦄
  ⦃ _ : SwapLaws A ⦄ ⦃ _ : SwapLaws B ⦄ where

  open ≈-Reasoning

  Abs-× : Abs (A × B) → Abs A × Abs B
  Abs-× (abs x (a , b)) = abs x a , abs x b

  module _ ⦃ _ : FinitelySupported A ⦄ ⦃ _ : FinitelySupported B ⦄ where
    Abs-×˘ : Abs A × Abs B → Abs (A × B)
    Abs-×˘ (t̂ , t̂′) =
      let z = minFresh (supp t̂ ++ supp t̂′) .proj₁
       in abs z (conc t̂ z , conc t̂′ z)
