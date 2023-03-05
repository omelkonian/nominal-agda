open import Prelude.Init; open SetAsType
open L.Mem
open import Prelude.General
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.Setoid
open import Prelude.InferenceRules
open import Prelude.InfEnumerable

module Nominal.Fun (Atom : Type) ⦃ _ : DecEq Atom ⦄ where

open import Nominal.Swap Atom
open import Nominal.Support Atom
open import Nominal.MinSupport Atom

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
      ⦃ _ : ISetoid B ⦄ → ⦃ SetoidLaws B ⦄
      → SetoidLaws (A → B)
    SetoidLaws-Fun .isEquivalence = record
      { refl  = λ {f} x → ≈-refl
      ; sym   = λ f∼g x → ≈-sym (f∼g x)
      ; trans = λ f∼g g∼h x → ≈-trans (f∼g x) (g∼h x)
      }

    SwapLaws-Fun :
      ⦃ _ : ISetoid A ⦄ ⦃ _ : SetoidLaws A ⦄ ⦃ _ : CongSetoid A ⦄ ⦃ _ : SwapLaws A ⦄
      ⦃ _ : ISetoid B ⦄ ⦃ _ : SetoidLaws B ⦄ ⦃ _ : SwapLaws B ⦄
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

module _
  ⦃ _ : Enumerable∞ Atom ⦄
  {A : Type ℓ} ⦃ _ : ISetoid A ⦄ ⦃ _ : SetoidLaws A ⦄
  ⦃ _ : Swap A ⦄ ⦃ _ : SwapLaws A ⦄
  where

  --  * in the case of _→_, Equivariant′ is equivalent to Equivariant
  equivariant-equiv : ∀ {f : A → A} →
    Equivariant f
    ══════════════
    Equivariant′ f
  equivariant-equiv {f = f} = ↝ , ↜
      where
        open ≈-Reasoning

        ↝ : Equivariant f
            ───────────────────
            Equivariant′ f
        ↝ equiv-f = fin-f , refl
          where
            fin-f : FinSupp f
            fin-f = [] , λ x y _ _ a →
              begin
                ⦅ y ↔ x ⦆ (f $ ⦅ y ↔ x ⦆ a)
              ≈˘⟨ cong-swap $ equiv-f _ _ ⟩
                ⦅ y ↔ x ⦆ ⦅ y ↔ x ⦆ f a
              ≈⟨ swap-sym′ ⟩
                f a
              ∎

        ↜ : Equivariant′ f
            ───────────────────
            Equivariant f
        ↜ (fin-f , refl) a b {x} =
          begin
            ⦅ a ↔ b ⦆ f x
          ≈˘⟨ cong-swap $ fin-f .proj₂ _ _ (λ ()) (λ ()) _ ⟩
            ⦅ a ↔ b ⦆ ⦅ a ↔ b ⦆ f (⦅ a ↔ b ⦆ x)
          ≈⟨ swap-sym′ ⟩
            f (⦅ a ↔ b ⦆ x)
          ∎

  equivariant-equiv-min : ∀ {f : A → A} →
    Equivariant f
    ═════════════════
    MinEquivariant′ f
  equivariant-equiv-min {f = f} = ↝ , ↜
      where
        open ≈-Reasoning

        ↝ : Equivariant f
            ───────────────────
            MinEquivariant′ f
        ↝ equiv-f = fin-f , refl
          where
            fin-f : MinFinSupp f
            fin-f = [] , (λ x y _ _ a →
              begin
                ⦅ y ↔ x ⦆ (f $ ⦅ y ↔ x ⦆ a)
              ≈˘⟨ cong-swap $ equiv-f _ _ ⟩
                ⦅ y ↔ x ⦆ ⦅ y ↔ x ⦆ f a
              ≈⟨ swap-sym′ ⟩
                f a
              ∎) , λ _ _ ()

        ↜ : MinEquivariant′ f
            ───────────────────
            Equivariant f
        ↜ (fin-f , refl) a b {x} =
          begin
            ⦅ a ↔ b ⦆ f x
          ≈˘⟨ cong-swap $ fin-f .proj₂ .proj₁ _ _ (λ ()) (λ ()) _ ⟩
            ⦅ a ↔ b ⦆ ⦅ a ↔ b ⦆ f (⦅ a ↔ b ⦆ x)
          ≈⟨ swap-sym′ ⟩
            f (⦅ a ↔ b ⦆ x)
          ∎

  private
    f′ : A → A
    f′ = id

    suppF′ = Atoms ∋ []

    g′ : A → A
    g′ x = x

    f≗g : f′ ≗ g′
    f≗g _ = refl

    f≈g : f′ ≈ g′
    f≈g _ = ≈-refl

    fin-f : FinSupp f′
    fin-f = suppF′ , λ _ _ _ _ _ → swap-sym′

    min-fin-f : MinFinSupp f′
    min-fin-f = suppF′ , (λ _ _ _ _ _ → swap-sym′) , (λ _ _ ())

    equiv-f : Equivariant f′
    equiv-f _ _ = ≈-refl

    equiv-f′ : Equivariant′ f′
    equiv-f′ = fin-f , refl

    instance
      Setoid-Bool : ISetoid Bool
      Setoid-Bool = λ where
        .relℓ → 0ℓ
        ._≈_  → _≡_

      SetoidLaws-Bool : SetoidLaws Bool
      SetoidLaws-Bool .isEquivalence = PropEq.isEquivalence

    postulate x y : Atom

    f : Atom → Bool
    f z = (z == x) ∨ (z == y)
    suppF = List Atom ∋ x ∷ y ∷ []
    -- fresh f = False

    finF : FinSupp f
    finF = -, go
      where
        ∀x∉suppF : ∀ {z} → z ∉ suppF → f z ≡ false
        ∀x∉suppF {z} z∉ with z ≟ x
        ... | yes refl = ⊥-elim $ z∉ $ here refl
        ... | no _ with z ≟ y
        ... | yes refl = ⊥-elim $ z∉ $ there $′ here refl
        ... | no _ = refl

        go : ∀ 𝕒 𝕓 → 𝕒 ∉ suppF → 𝕓 ∉ suppF → f ∘ swap 𝕓 𝕒 ≗ f
        go 𝕒 𝕓 𝕒∉ 𝕓∉ z with z ≟ 𝕓
        ... | yes refl rewrite ∀x∉suppF 𝕒∉ | ∀x∉suppF 𝕓∉ = refl
        ... | no _ with z ≟ 𝕒
        ... | yes refl rewrite ∀x∉suppF 𝕒∉ | ∀x∉suppF 𝕓∉ = refl
        ... | no _ = refl

    _ = finF .proj₁ ≡ suppF
      ∋ refl

    g : Atom → Bool
    g z = (z ≠ x) ∧ (z ≠ y)
    suppG = List Atom ∋ x ∷ y ∷ []
    -- fresh g = True
    -- NB: g is infinite, but has finite support!

    finG : FinSupp g
    finG = -, go
      where
        ∀x∉suppG : ∀ {z} → z ∉ suppG → g z ≡ true
        ∀x∉suppG {z} z∉ with z ≟ x
        ... | yes refl = ⊥-elim $ z∉ $ here refl
        ... | no _ with z ≟ y
        ... | yes refl = ⊥-elim $ z∉ $ there $′ here refl
        ... | no _ = refl

        go : ∀ 𝕒 𝕓 → 𝕒 ∉ suppG → 𝕓 ∉ suppG → g ∘ swap 𝕓 𝕒 ≗ g
        go 𝕒 𝕓 𝕒∉ 𝕓∉ z with z ≟ 𝕓
        ... | yes refl rewrite ∀x∉suppG 𝕒∉ | ∀x∉suppG 𝕓∉ = refl
        ... | no _ with z ≟ 𝕒
        ... | yes refl rewrite ∀x∉suppG 𝕒∉ | ∀x∉suppG 𝕓∉ = refl
        ... | no _ = refl

    -- T0D0: example where _≗_ is not the proper notion of equality
    -- module _ ⦃ _ : Toℕ Atom ⦄ where
    --   h : Atom → Bool
    --   h z = even? (toℕ z)
    --   -- ∄ supp h ⇔ ∄ fresh h

  -- Find the non-finSupp swappable example.
  -- ∙ ZFA ↝ ZFA+choice
  -- ∙ the set of all total orderings on atoms
  -- (empty support on the outside, infinite support inside each order)
  -- ∙ FOL: ultra-filter construction
