open import Prelude.Init
open import Prelude.DecEq
open import Prelude.General

module AbsF (Atom : Set) ⦃ _ : DecEq Atom ⦄ where

open import Swap Atom ⦃ it ⦄

module _ ⦃ _ : Swap A ⦄ where
  Abs : Set ℓ → Set ℓ
  Abs A = Atom → A

  abs : Atom → A → Abs A
  abs 𝕒 x = λ 𝕓 → swap 𝕓 𝕒 x

  conc : Abs A → Atom → A
  -- conc f 𝕓 = swap 𝕓 {!!} {!!}
  conc f = f
  -- conc (abs 𝕒 x) 𝕓 = swap 𝕓 𝕒 x
  --                  = (abs 𝕒 x) 𝕓

  -- unquoteDecl Swap-Abs = DERIVE Swap [ quote Abs , Swap-Abs ]
  instance
    Swap-Abs : Swap (Abs A)
    Swap-Abs .swap 𝕒 𝕓 f 𝕔
      -- = fc -- swapping has no effects on abstractions
      -- = fc′ -- swapping only the input atom
      -- = ↔fc -- swapping only the output term
      = ↔fc′ -- swapping both the input atom and the output term
      where
        ↔𝕔 = swap 𝕒 𝕓 𝕔
        fc = f 𝕔
        fc′ = f ↔𝕔
        ↔fc = swap 𝕒 𝕓 fc
        ↔fc′ = swap 𝕒 𝕓 fc′

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
