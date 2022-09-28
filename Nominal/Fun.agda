open import Prelude.Init
open SetAsType
open import Prelude.General
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.Setoid
open import Prelude.InferenceRules

module Nominal.Fun (Atom : Type) ⦃ _ : DecEq Atom ⦄ where

open import Nominal.Swap Atom


module _ {A B : Type} ⦃ _ : Swap A ⦄ ⦃ _ : Swap B ⦄ where

  instance
    Swap-Fun : Swap (A → B)
    Swap-Fun .swap a b f = swap a b ∘ f ∘ swap a b

    Setoid-Fun : ⦃ ISetoid B ⦄ → ISetoid (A → B)
    Setoid-Fun = λ where
      .relℓ → relℓ {A = B}
      ._≈_  f g → ∀ x → f x ≈ g x

    SetoidLaws-Fun : ⦃ _ : ISetoid B ⦄ → ⦃ Setoid-Laws B ⦄
                   → Setoid-Laws (A → B)
    SetoidLaws-Fun .isEquivalence = record
      { refl  = λ {f} x → ≈-refl
      ; sym   = λ f∼g x → ≈-sym (f∼g x)
      ; trans = λ f∼g g∼h x → ≈-trans (f∼g x) (g∼h x)
      }

    open ≈-Reasoning

    SwapLaws-Fun : ⦃ _ : ISetoid A ⦄ ⦃ _ : Setoid-Laws A ⦄ ⦃ _ : CongSetoid A ⦄ ⦃ _ : SwapLaws A ⦄
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


  test-𝕒 : justAtom 𝕒 ≡ just 𝕒
  test-𝕒 rewrite ≟-refl 𝕒 = refl

  test-𝕓 : justAtom 𝕓 ≡ nothing
  test-𝕓 rewrite dec-no (𝕓 ≟ 𝕒) (≢-sym 𝕒≢𝕓) .proj₂ = refl

  test-𝕒′ : justAtom′ 𝕒 ≡ nothing
  test-𝕒′ rewrite dec-no (𝕒 ≟ 𝕓) 𝕒≢𝕓 .proj₂
                | ≟-refl 𝕒
                | dec-no (𝕓 ≟ 𝕒) (≢-sym 𝕒≢𝕓) .proj₂
                = refl

  test-𝕓′ : justAtom′ 𝕓 ≡ just 𝕓
  test-𝕓′ rewrite ≟-refl 𝕓
                | dec-no (𝕓 ≟ 𝕒) (≢-sym 𝕒≢𝕓) .proj₂
                | ≟-refl 𝕒
                | ≟-refl 𝕒
                = refl

open import Prelude.InfEnumerable
open import Prelude.Membership
module _ ⦃ _ : Enumerable∞ Atom ⦄ where
  open import Nominal.Support Atom
  open import Nominal.Abs     Atom


  module _ {A : Type}
    ⦃ _ : Swap A ⦄ ⦃ _ : ISetoid A ⦄ ⦃ _ : Setoid-Laws A ⦄ ⦃ _ : SwapLaws A ⦄
    ⦃ _ : FinitelySupported A ⦄ where

    Equivariant¹′ : (A → A) → Type _
    Equivariant¹′ f = ∃ λ (fin-f : FinSupp f) → fin-f .proj₁ ≡ []

    equivariant-equiv : ∀ {f : A → A} →
      Equivariant¹ f
      ═══════════════════
      Equivariant¹′ f
    equivariant-equiv {f = f} = ↝ , ↜
        where
          open ≈-Reasoning

          ↝ : Equivariant¹ f
              ───────────────────
              Equivariant¹′ f
          ↝ equiv-f = fin-f , refl
            where
              fin-f : FinSupp f
              fin-f = [] , λ x y _ _ a →
                begin
                  ⦅ y ↔ x ⦆ (f $ ⦅ y ↔ x ⦆ a)
                ≈⟨ cong-swap $ equiv-f _ _ _ ⟩
                  ⦅ y ↔ x ⦆ ⦅ y ↔ x ⦆ f a
                ≈⟨ swap-sym′ ⟩
                  f a
                ∎

          ↜ : Equivariant¹′ f
              ───────────────────
              Equivariant¹ f
          ↜ (fin-f , refl) x a b =
            begin
              f (⦅ a ↔ b ⦆ x)
            ≈˘⟨ swap-sym′ ⟩
              ⦅ a ↔ b ⦆ ⦅ a ↔ b ⦆ f (⦅ a ↔ b ⦆ x)
            ≈⟨ cong-swap $ fin-f .proj₂ _ _ (λ ()) (λ ()) _ ⟩
              ⦅ a ↔ b ⦆ f x
            ∎

    -- module _ ⦃ _ : CongSetoid A ⦄ where
    --   equivariant-equiv : ∀ {f : A → A} {fin-f : FinSupp f} {min-fin-f : MinSupp fin-f} →
    --     Equivariant¹ f
    --     ═══════════════════
    --     Equivariant¹′ fin-f
    --   equivariant-equiv {f = f}{fin-f}{min-fin-f} = ↝ , ↜
    --     where
    --       open ≈-Reasoning

    --       ↝ : Equivariant¹ f
    --           ───────────────────
    --           Equivariant¹′ fin-f
    --       ↝ equiv-f with ⟫ fin-f | ⟫ min-fin-f
    --       ... | ⟫ []    , _ | _         = refl
    --       ... | ⟫ x ∷ [] , p | ⟫ min =
    --         let y , y∉ = fresh [ x ]
    --         in ⊥-elim $ min y (y∉ ∘ here) λ a →
    --              ≈-trans (cong-swap $ equiv-f a x y) swap-sym′
    --       ... | ⟫ x ∷ y ∷ _ , p | ⟫ ((x≢y ∷ _) ∷ _) , min =
    --         ⊥-elim $ min x y (here refl) (there $′ here refl) x≢y λ a →
    --           begin
    --             swap x y (f $ swap x y a)
    --           ≈⟨ cong-swap $ equiv-f a x y ⟩
    --             ⦅ x ↔ y ⦆ ⦅ x ↔ y ⦆ f a
    --           ≈⟨ swap-sym′ ⟩
    --             f a
    --           ∎

    --       ↜ : Equivariant¹′ fin-f
    --           ───────────────────
    --           Equivariant¹ f
    --       ↜ refl x a b =
    --         begin
    --           f (swap a b x)
    --         ≈˘⟨ swap-sym′ ⟩
    --           swap a b (swap a b (f $ swap a b x))
    --         ≈⟨ cong-swap $ fin-f .proj₂ b a (λ ()) (λ ()) x ⟩
    --           swap a b (f x)
    --         ∎


    private
      f : A → A
      f = id

      suppF = Atoms ∋ []

      g : A → A
      g x = x

      f≗g : f ≗ g
      f≗g _ = refl

      f≈g : f ≈ g
      f≈g _ = ≈-refl

      fin-f : FinSupp f
      fin-f = suppF , λ _ _ _ _ _ → swap-sym′

      min-fin-f : MinSupp fin-f
      min-fin-f = Lvl.lift tt

      equiv-f : Equivariant¹ f
      equiv-f _ _ _ = ≈-refl

      equiv-f′ : Equivariant¹′ f
      equiv-f′ = fin-f , refl
