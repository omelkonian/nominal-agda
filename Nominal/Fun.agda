open import Prelude.Init
open SetAsType
open import Prelude.General
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.Setoid

module Nominal.Fun (Atom : Type) ⦃ _ : DecEq Atom ⦄ where

open import Nominal.Swap Atom

module _ {A : Type ℓ} {B : Type ℓ′} ⦃ _ : Swap A ⦄ ⦃ _ : Swap B ⦄ where

  open ≈-Reasoning

  instance
    Swap-Fun : Swap (A → B)
    Swap-Fun .swap a b f = swap a b ∘ f ∘ swap a b

    Setoid-Fun : ⦃ ISetoid B ⦄ → ISetoid (A → B)
    Setoid-Fun = λ where
      .relℓ → ℓ ⊔ₗ relℓ {A = B}
      ._≈_  f g → ∀ x → f x ≈ g x
      -- ._≈_  f g → ∀ x y → x ≈ y → f x ≈ g y

    SetoidLaws-Fun :
      ⦃ _ : ISetoid B ⦄ → ⦃ Setoid-Laws B ⦄
      → Setoid-Laws (A → B)
    SetoidLaws-Fun .isEquivalence = record
      { refl  = λ {f} x → ≈-refl
      ; sym   = λ f∼g x → ≈-sym (f∼g x)
      ; trans = λ f∼g g∼h x → ≈-trans (f∼g x) (g∼h x)
      }

    SwapLaws-Fun :
      ⦃ _ : ISetoid A ⦄ ⦃ _ : Setoid-Laws A ⦄ ⦃ _ : CongSetoid A ⦄ ⦃ _ : SwapLaws A ⦄
      ⦃ _ : ISetoid B ⦄ ⦃ _ : Setoid-Laws B ⦄ ⦃ _ : SwapLaws B ⦄
      → SwapLaws (A → B)
    SwapLaws-Fun .cong-swap {f}{g}{a}{b} f≗g x =
    -- ∀ {f g : A → B} → x ≈ y → ⦅ 𝕒 ↔ 𝕓 ⦆ f ≈ ⦅ 𝕒 ↔ 𝕓 ⦆ g
      cong-swap (f≗g _)
    SwapLaws-Fun .swap-id {a}{f} x =
    -- ∀ {f : A → B} → ⦅ 𝕒 ↔ 𝕒 ⦆ f ≈ f
      begin
        ⦅ a ↔ a ⦆ (f (⦅ a ↔ a ⦆ x))
      ≈⟨ swap-id ⟩
        f (⦅ a ↔ a ⦆ x)
      ≈⟨ ≈-cong f swap-id ⟩
        f x
      ∎
    SwapLaws-Fun .swap-rev {a}{b}{f} x =
    -- ∀ {f : A → B} → ⦅ 𝕒 ↔ 𝕓 ⦆ f ≈ ⦅ 𝕓 ↔ 𝕒 ⦆ f
      begin
        (⦅ a ↔ b ⦆ f) x
      ≡⟨⟩
        ⦅ a ↔ b ⦆ (f $ ⦅ a ↔ b ⦆ x)
      ≈⟨ cong-swap $ ≈-cong f swap-rev ⟩
        ⦅ a ↔ b ⦆ (f $ ⦅ b ↔ a ⦆ x)
      ≈⟨ swap-rev ⟩
        ⦅ b ↔ a ⦆ (f $ ⦅ b ↔ a ⦆ x)
      ≡⟨⟩
        (⦅ b ↔ a ⦆ f) x
      ∎
    SwapLaws-Fun .swap-sym {a}{b}{f} x =
    -- ∀ {f : A → B} → ⦅ 𝕒 ↔ 𝕓 ⦆ ⦅ 𝕓 ↔ 𝕒 ⦆ f ≈ f
      begin
        (⦅ a ↔ b ⦆ ⦅ b ↔ a ⦆ f) x
      ≡⟨⟩
        ⦅ a ↔ b ⦆ ⦅ b ↔ a ⦆ (f $ ⦅ b ↔ a ⦆ ⦅ a ↔ b ⦆ x)
      ≈⟨ cong-swap $ cong-swap $ ≈-cong f swap-sym ⟩
        ⦅ a ↔ b ⦆ ⦅ b ↔ a ⦆ (f x)
      ≈⟨ swap-sym ⟩
        f x
      ∎
    SwapLaws-Fun .swap-swap {𝕒 = a}{b}{c}{d}{f} x =
    -- ∀ {f : A → B} → ⦅ 𝕒 ↔ 𝕓 ⦆ ⦅ 𝕔 ↔ 𝕕 ⦆ f
    --               ≈ ⦅ ⦅ 𝕒 ↔ 𝕓 ⦆ 𝕔 ↔ ⦅ 𝕒 ↔ 𝕓 ⦆ 𝕕 ⦆ ⦅ 𝕒 ↔ 𝕓 ⦆ f
      begin
        (⦅ a ↔ b ⦆ ⦅ c ↔ d ⦆ f) x
      ≡⟨⟩
        ⦅ a ↔ b ⦆ ⦅ c ↔ d ⦆ (f $ ⦅ c ↔ d ⦆ ⦅ a ↔ b ⦆ x)
      ≈⟨ swap-swap ⟩
        ⦅ ⦅ a ↔ b ⦆ c ↔ ⦅ a ↔ b ⦆ d ⦆ ⦅ a ↔ b ⦆
          (f $ ⦅ c ↔ d ⦆ ⦅ a ↔ b ⦆ x)
      --                ↑ NB: note the change of ordering on swappings
      ≈⟨ cong-swap $ cong-swap $ ≈-cong f
       $ begin
           ⦅ c ↔ d ⦆ ⦅ a ↔ b ⦆ x
         ≡˘⟨ cong (λ ◆ → ⦅ c ↔ ◆ ⦆ ⦅ a ↔ b ⦆ x) swap-sym′ ⟩
           ⦅ c ↔ ⦅ a ↔ b ⦆ ⦅ a ↔ b ⦆ d ⦆ ⦅ a ↔ b ⦆ x
         ≡˘⟨ cong (λ ◆ → ⦅ ◆ ↔ ⦅ a ↔ b ⦆ ⦅ a ↔ b ⦆ d ⦆ ⦅ a ↔ b ⦆ x) swap-sym′ ⟩
           ⦅ ⦅ a ↔ b ⦆ ⦅ a ↔ b ⦆ c ↔ ⦅ a ↔ b ⦆ ⦅ a ↔ b ⦆ d ⦆ ⦅ a ↔ b ⦆ x
         ≈˘⟨ swap-swap ⟩
           ⦅ a ↔ b ⦆ ⦅ ⦅ a ↔ b ⦆ c ↔ ⦅ a ↔ b ⦆ d ⦆ x
         ∎
       ⟩
        ⦅ ⦅ a ↔ b ⦆ c ↔ ⦅ a ↔ b ⦆ d ⦆ ⦅ a ↔ b ⦆
          (f $ ⦅ a ↔ b ⦆ ⦅ ⦅ a ↔ b ⦆ c ↔ ⦅ a ↔ b ⦆ d ⦆ x)
      ≡⟨⟩
        (⦅ ⦅ a ↔ b ⦆ c ↔ ⦅ a ↔ b ⦆ d ⦆ ⦅ a ↔ b ⦆ f) x
      ∎

private
  postulate
    𝕒 𝕓 : Atom
    𝕒≢𝕓 : 𝕒 ≢ 𝕓

  unquoteDecl Swap-Maybe = DERIVE Swap [ quote Maybe , Swap-Maybe ]

  justAtom : Atom → Maybe Atom
  justAtom n =
    if n == 𝕒 then
      just 𝕒
    else
      nothing

  justAtom′ : Atom → Maybe Atom
  justAtom′ = ⦅ 𝕒 ↔ 𝕓 ⦆ justAtom

  _ : justAtom 𝕒 ≡ just 𝕒
  _ rewrite ≟-refl 𝕒 = refl

  _ : justAtom 𝕓 ≡ nothing
  _ rewrite dec-no (𝕓 ≟ 𝕒) (≢-sym 𝕒≢𝕓) .proj₂ = refl

  _ : justAtom′ 𝕒 ≡ nothing
  _ rewrite dec-no (𝕒 ≟ 𝕓) 𝕒≢𝕓 .proj₂
          | ≟-refl 𝕒
          | dec-no (𝕓 ≟ 𝕒) (≢-sym 𝕒≢𝕓) .proj₂
          = refl

  _ : justAtom′ 𝕓 ≡ just 𝕓
  _ rewrite ≟-refl 𝕓
          | dec-no (𝕓 ≟ 𝕒) (≢-sym 𝕒≢𝕓) .proj₂
          | ≟-refl 𝕒
          | ≟-refl 𝕒
          = refl
