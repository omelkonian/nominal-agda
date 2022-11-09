open import Prelude.Init; open SetAsType
open L.Mem
open import Prelude.DecEq
open import Prelude.Setoid
open import Prelude.Bifunctor
open import Prelude.InferenceRules
open import Prelude.InfEnumerable

module Nominal.Abs.Support (Atom : Type) ⦃ _ : DecEq Atom ⦄ ⦃ _ : Enumerable∞ Atom ⦄ where

open import Nominal.New      Atom
open import Nominal.Swap     Atom
open import Nominal.Support  Atom
open import Nominal.Abs.Base Atom

module _ {A : Type ℓ}
  ⦃ _ : ISetoid A ⦄ ⦃ _ : Setoid-Laws A ⦄
  ⦃ _ : Swap A ⦄ ⦃ _ : SwapLaws A ⦄
  ⦃ _ : FinitelySupported A ⦄ where

  -- abstractions over finitely supported types are themselves finite
  instance
    FinSupp-Abs : FinitelySupported (Abs A)
    FinSupp-Abs .∀fin (abs x t) =
      let xs , p = ∀fin t
      in x ∷ xs , λ y z y∉ z∉ →
      begin
        ⦅ z ↔ y ⦆ (abs x t)
      ≡⟨⟩
        -- ⦅ 𝕒 ↔ 𝕓 ⦆ (f 𝕔) ≈ (⦅ 𝕒 ↔ 𝕓 ⦆ f) (⦅ 𝕒 ↔ 𝕓 ⦆ 𝕔)
        abs (⦅ z ↔ y ⦆ x) (⦅ z ↔ y ⦆ t)
      ≡⟨ cong (λ ◆ → abs ◆ (⦅ z ↔ y ⦆ t))
            $ swap-noop z y x (λ where ♯0 → z∉ ♯0; ♯1 → y∉ ♯0) ⟩
        abs x (⦅ z ↔ y ⦆ t)
      ≈⟨ cong-abs $ p y z (y∉ ∘ there) (z∉ ∘ there) ⟩
        abs x t
      ∎ where open ≈-Reasoning

  -- Two ways to fix functoriality:
    -- 1. require that (f : A → A) is equivariant
  --   2. ...or that it at least has finite support
  mapAbs : Op₁ A → Op₁ (Abs A)
      -- ≈ (A → A) → (Abs A → Abs A)
  -- T0D0: In order to resolve termination issues (via well-founded recursion),
  -- we need a more restrainted version of mapAbs with type:
  -- mapAbs : (x' : Abs A) → (f : (a : A) → a ≺ f → A) → Abs A
  -- NB: a generalisation would be to say that the size behaviour of
  --     `mapAbs f` corresponds to that of `f`
  mapAbs f x' =
    let a = fresh-var x' -- T0D0: ++ supp?? f
    in abs a (f $ conc x' a)

  freshen : Op₁ (Abs A)
  freshen f@(abs a t) =
    let xs , _ = ∀fin f
        b , b∉ = minFresh xs
    in abs b (conc f b)
