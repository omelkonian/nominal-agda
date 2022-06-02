open import Prelude.Init
open import Prelude.DecEq
open import Prelude.InferenceRules
open import Prelude.Setoid

module Nominal.Fresh (Atom : Set) ⦃ _ : DecEq Atom ⦄ where

open import Nominal.Swap    Atom
open import Nominal.Abs     Atom
open import Nominal.New     Atom
open import Nominal.Support Atom

module _ {A : Set ℓ} ⦃ _ : Swap A ⦄ ⦃ _ : ISetoid A ⦄ ⦃ _ : Setoid-Laws A ⦄ where
  -- ≈ FM sets (Fraenkel-Maestowski set theory)

  infix 4 _#_
  _#_ : Atom → A → Set ℓ
  𝕒 # x = И λ 𝕓 → swap 𝕓 𝕒 x ≡ x

--   fresh : let open Support {A = Atom → A} in

--           (f : Atom → A) → FinSupp f → A
--   fresh f = ?
--   -- 1. Use the И quantifier to get a fresh atom `𝕒`
--   -- 2. Call `x : A = f 𝕒`
--   -- 3. [Reason about the uniqueness of x]
--   -- 4. Return x

--   postulate
--     fresh : (Atom → A) → A

--     fresh-axiom : ∀ {f : Atom → A} →

--       И (λ 𝕒 → 𝕒 # f 𝕒)
--       ───────────────────────
--       И (λ 𝕒 → fresh f ≡ f 𝕒)

-- _ : λTerm
-- _ = fresh λ 𝕒 → (ƛ 𝕒 ⇒ ` 𝕒)

-- module _ {A : Set ℓ} {B : Set ℓ′} ⦃ _ : Swap A ⦄ ⦃ _ : Swap B ⦄ where

--   mapAbs : (A → B) → (Abs A → Abs B)
--   mapAbs f x' = fresh λ 𝕒 →
--     abs 𝕒 (f $ conc x' 𝕒)

--   -- mapAbs suc (abs 𝕒 0) ≡ abs ? 1
