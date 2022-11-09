open import Prelude.Init
open SetAsType
open import Prelude.General
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.Setoid

module Nominal.Product (Atom : Type) ⦃ _ : DecEq Atom ⦄ where

open import Nominal.Swap Atom

module _
  {A : Type ℓ} {B : Type ℓ′}
  ⦃ _ : ISetoid A ⦄ ⦃ _ : ISetoid B ⦄
  ⦃ _ : Setoid-Laws A ⦄ ⦃ _ : Setoid-Laws B ⦄
  ⦃ _ : Swap A ⦄ ⦃ _ : Swap B ⦄
  ⦃ _ : SwapLaws A ⦄ ⦃ _ : SwapLaws B ⦄ where

  open ≈-Reasoning

  instance
    Setoid-× : ISetoid (A × B)
    Setoid-× = λ where
      .relℓ → _
      ._≈_ (a , b) (a′ , b′) → (a ≈ a′) × (b ≈ b′)

    SetoidLaws-× : Setoid-Laws (A × B)
    SetoidLaws-× .isEquivalence = record
      { refl  = ≈-refl , ≈-refl
      ; sym   = λ (i , j) → ≈-sym i , ≈-sym j
      ; trans = λ (i , j) (k , l) → ≈-trans i k , ≈-trans j l
      }

  -- do not export, as it creates problems with instance resolution wrt Abs
  SwapLaws-× : SwapLaws (A × B)
  SwapLaws-× = record
    { cong-swap = λ (x , y) → cong-swap x , cong-swap y
    ; swap-id = swap-id , swap-id
    ; swap-rev = swap-rev , swap-rev
    ; swap-sym = swap-sym , swap-sym
    ; swap-swap = swap-swap , swap-swap
    }

private
  postulate
    𝕒 𝕓 : Atom
    𝕒≢𝕓 : 𝕒 ≢ 𝕓

  unquoteDecl Swap-Maybe = DERIVE Swap [ quote Maybe , Swap-Maybe ]

  justAtom : Atom × Maybe Atom
  justAtom = 𝕒 , just 𝕓

  justAtom′ : Atom × Maybe Atom
  justAtom′ = ⦅ 𝕒 ↔ 𝕓 ⦆ justAtom

  _ = justAtom .proj₁ ≡ 𝕒
    ∋ refl

  _ = justAtom .proj₂ ≡ just 𝕓
    ∋ refl

  _ : justAtom′ .proj₁ ≡ 𝕓
  _ rewrite dec-no (𝕒 ≟ 𝕓) 𝕒≢𝕓 .proj₂
          | ≟-refl 𝕒
          = refl

  _ : justAtom′ .proj₂ ≡ just 𝕒
  _ rewrite dec-no (𝕓 ≟ 𝕒) (≢-sym 𝕒≢𝕓) .proj₂
          | ≟-refl 𝕓
          = refl
