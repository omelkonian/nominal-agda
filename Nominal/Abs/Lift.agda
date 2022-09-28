open import Prelude.Init
open SetAsType
open import Prelude.DecEq
open import Prelude.Setoid

module Nominal.Abs.Lift (Atom : Type) ⦃ _ : DecEq Atom ⦄ where

open import Nominal.Swap     Atom
open import Nominal.Fun      Atom
open import Nominal.Abs.Base Atom

module _ {A : Type ℓ} {B : Type ℓ′} ⦃ _ : Swap A ⦄ ⦃ _ : Swap B ⦄ where

  theorem→ : Abs (A → B) → (Abs A → Abs B)
  theorem→ (abs 𝕒 f) (abs 𝕓 a) = abs 𝕒 $ swap 𝕓 𝕒 (f a)

  postulate theorem← : (Abs A → Abs B) → Abs (A → B)
  -- theorem← F = abs {!!} (λ a → {!!})

private variable A : Type ℓ

record Lift (P : Type ℓ → Type ℓ′) : Type (lsuc ℓ ⊔ₗ ℓ′) where
  field lift : P A → P (Abs A)
open Lift ⦃...⦄ public

instance
  -- Lift-Fun : ∀ {B : Type ℓ′} → Lift (λ A → A → B)
  -- Lift-Fun .lift f (abs 𝕒 x) = {!!}

  Lift-Rel : Lift (λ (A : Type ℓ) → Rel A ℓ′)
  Lift-Rel .lift _~_ = λ where
    (abs _ x) (abs _ y) → x ~ y

-- lift : Rel A ℓ → Rel (Abs A) ℓ
-- (lift _~_) = λ where
--   -- (abs _ x) (abs _ y) → x ~ y
--   -- (abs 𝕒 x) (abs 𝕓 y) → x ~ swap 𝕓 𝕒 y
--   x y → let 𝕔 = freshAtom in conc x 𝕔 ~ conc y 𝕔
--    where postulate freshAtom : Atom

-- instance
--   Setoid-Abs : ⦃ ISetoid A ⦄ → ISetoid (Abs A)
--   Setoid-Abs = λ where
--     .relℓ → _
--     ._≈_  → lift _≈_
