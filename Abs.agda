open import Prelude.Init hiding (swap)
open import Prelude.DecEq
open import Prelude.General

module Abs (Atom : Set) ⦃ _ : DecEq Atom ⦄ where

open import Swap Atom ⦃ it ⦄

module _ {ℓ} {A : Set ℓ} ⦃ _ : Swap A ⦄ where

  record Abs (A : Set ℓ) : Set ℓ where
    constructor abs
    field atom : Atom
          term : A
  open Abs public

  conc : Abs A → Atom → A
  conc (abs 𝕒 x) 𝕓 = swap 𝕓 𝕒 x

  instance
    Swap-Abs : Swap (Abs A)
    Swap-Abs .swap 𝕒 𝕓 (abs 𝕔 x) = abs (swap 𝕒 𝕓 𝕔) (swap 𝕒 𝕓 x)

  -- _≈_ : Rel (Abs A) _
  -- x ≈ y = let 𝕔 = freshAtom in conc x 𝕔 ≡ conc y 𝕔
  --   where postulate freshAtom : Atom

  -- instance
  --   DecEq-Abs : ⦃ DecEq A ⦄ → DecEq (Abs A)
  --   DecEq-Abs ._≟_ (abs 𝕒 x) (abs 𝕓 y) = {!!}

  record Lift (P : Set ℓ → Set ℓ′) : Set (ℓ ⊔ₗ ℓ′) where
    field lift : P A → P (Abs A)
  open Lift ⦃...⦄ public

  open import Prelude.General

  instance
    -- Lift-Fun : ∀ {B : Set ℓ′} → Lift (λ A → A → B)
    -- Lift-Fun .lift f (abs 𝕒 x) = {!!}

    Lift-Rel : Lift (λ A → Rel A ℓ)
    Lift-Rel .lift _~_ = λ where
      (abs _ x) (abs _ y) → x ~ y

  -- lift : Rel A ℓ → Rel (Abs A) ℓ
  -- (lift _~_) = λ where
  --   -- (abs _ x) (abs _ y) → x ~ y
  --   -- (abs 𝕒 x) (abs 𝕓 y) → x ~ swap 𝕓 𝕒 y
  --   x y → let 𝕔 = freshAtom in conc x 𝕔 ~ conc y 𝕔
  --    where postulate freshAtom : Atom

  _≈_ : Rel (Abs A) _
  _≈_ = lift _≡_

  private
    variable
      𝕒 𝕓 𝕔 : Atom
      x : A

    _ : swap 𝕒 𝕓 (abs 𝕔 x)
      ≡ abs (swap 𝕒 𝕓 𝕔) (swap 𝕒 𝕓 x)
    _ = refl

    _∙_ = conc
    _ : conc (abs 𝕒 x) 𝕓 ≡ (abs 𝕒 x) ∙ 𝕓
    _ = refl

    _ : conc (abs 𝕒 x) 𝕓 ≡ swap 𝕓 𝕒 x
    _ = refl

-- module _ {A : Set ℓ} {B : Set ℓ′} ⦃ _ : Swap A ⦄ ⦃ _ : Swap B ⦄ where

--   liftF : (A → B) → (Abs A → Abs B)
--   liftF f (abs 𝕒 x) = {!!}

module _ {A : Set ℓ} {B : Set ℓ′} ⦃ _ : Swap A ⦄ ⦃ _ : Swap B ⦄ where

  instance
    Swap→ : Swap (A → B)
    Swap→ .swap 𝕒 𝕓 f a = swap {A = B} 𝕒 𝕓 $ f (swap {A = A} 𝕒 𝕓 a)

  theorem→ : Abs {A = A → B} (A → B) → (Abs {A = A} A → Abs {A = B} B)
  theorem→ (abs 𝕒 f) (abs 𝕓 a) = abs 𝕒 $ swap 𝕓 𝕒 (f a)

  postulate theorem← : (Abs {A = A} A → Abs {A = B} B) → Abs {A = A → B} (A → B)
  -- theorem← F = abs {!!} (λ a → {!!})
