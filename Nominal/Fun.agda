open import Prelude.Init; open SetAsType
open L.Mem
open import Prelude.General
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.InferenceRules
open import Prelude.InfEnumerable

open import Axiom.Extensionality.Propositional

module Nominal.Fun (Atom : Type) ⦃ _ : DecEq Atom ⦄ where

open import Nominal.Swap Atom
open import Nominal.Support Atom

module _ {A : Type ℓ} {B : Type ℓ′} ⦃ _ : Swap A ⦄ ⦃ _ : Swap B ⦄ where

  -- ** Axiom: function extensionality
  postulate ext : Extensionality ℓ ℓ′

  open ≡-Reasoning

  instance
    Swap-Fun : Swap (A → B)
    Swap-Fun .swap a b f = swap a b ∘ f ∘ swap a b

    -- Setoid-Fun : ⦃ ISetoid B ⦄ → ISetoid (A → B)
    -- Setoid-Fun = λ where
    --   .relℓ → ℓ ⊔ₗ relℓ {A = B}
    --   ._≡_  f g → ∀ x → f x ≡ g x
    --   -- ._≡_  f g → ∀ x y → x ≡ y → f x ≡ g y

    SwapLaws-Fun : ⦃ SwapLaws A ⦄ → ⦃ SwapLaws B ⦄ → SwapLaws (A → B)
    SwapLaws-Fun .swap-id {a}{f} = ext λ x →
    -- ∀ {f : A → B} → ⦅ 𝕒 ↔ 𝕒 ⦆ f ≡ f
      begin
        ⦅ a ↔ a ⦆ (f (⦅ a ↔ a ⦆ x))
      ≡⟨ swap-id ⟩
        f (⦅ a ↔ a ⦆ x)
      ≡⟨ cong f swap-id ⟩
        f x
      ∎
    SwapLaws-Fun .swap-rev {a}{b}{f} = ext λ x →
    -- ∀ {f : A → B} → ⦅ 𝕒 ↔ 𝕓 ⦆ f ≡ ⦅ 𝕓 ↔ 𝕒 ⦆ f
      begin
        (⦅ a ↔ b ⦆ f) x
      ≡⟨⟩
        ⦅ a ↔ b ⦆ (f $ ⦅ a ↔ b ⦆ x)
      ≡⟨ cong (swap _ _ ∘ f) swap-rev ⟩
        ⦅ a ↔ b ⦆ (f $ ⦅ b ↔ a ⦆ x)
      ≡⟨ swap-rev ⟩
        ⦅ b ↔ a ⦆ (f $ ⦅ b ↔ a ⦆ x)
      ≡⟨⟩
        (⦅ b ↔ a ⦆ f) x
      ∎
    SwapLaws-Fun .swap-sym {a}{b}{f} = ext λ x →
    -- ∀ {f : A → B} → ⦅ 𝕒 ↔ 𝕓 ⦆ ⦅ 𝕓 ↔ 𝕒 ⦆ f ≡ f
      begin
        (⦅ a ↔ b ⦆ ⦅ b ↔ a ⦆ f) x
      ≡⟨⟩
        ⦅ a ↔ b ⦆ ⦅ b ↔ a ⦆ (f $ ⦅ b ↔ a ⦆ ⦅ a ↔ b ⦆ x)
      ≡⟨ cong (swap _ _ ∘ swap _ _) $ cong f swap-sym ⟩
        ⦅ a ↔ b ⦆ ⦅ b ↔ a ⦆ (f x)
      ≡⟨ swap-sym ⟩
        f x
      ∎
    SwapLaws-Fun .swap-swap {𝕒 = a}{b}{c}{d}{f} = ext λ x →
    -- ∀ {f : A → B} → ⦅ 𝕒 ↔ 𝕓 ⦆ ⦅ 𝕔 ↔ 𝕕 ⦆ f
    --               ≡ ⦅ ⦅ 𝕒 ↔ 𝕓 ⦆ 𝕔 ↔ ⦅ 𝕒 ↔ 𝕓 ⦆ 𝕕 ⦆ ⦅ 𝕒 ↔ 𝕓 ⦆ f
      begin
        (⦅ a ↔ b ⦆ ⦅ c ↔ d ⦆ f) x
      ≡⟨⟩
        ⦅ a ↔ b ⦆ ⦅ c ↔ d ⦆ (f $ ⦅ c ↔ d ⦆ ⦅ a ↔ b ⦆ x)
      ≡⟨ swap-swap ⟩
        ⦅ ⦅ a ↔ b ⦆ c ↔ ⦅ a ↔ b ⦆ d ⦆ ⦅ a ↔ b ⦆
          (f $ ⦅ c ↔ d ⦆ ⦅ a ↔ b ⦆ x)
      --                ↑ NB: note the change of ordering on swappings
      ≡⟨ cong (swap _ _ ∘ swap _ _ ∘ f)
       $ begin
           ⦅ c ↔ d ⦆ ⦅ a ↔ b ⦆ x
         ≡˘⟨ cong (λ ◆ → ⦅ c ↔ ◆ ⦆ ⦅ a ↔ b ⦆ x) swap-sym′ ⟩
           ⦅ c ↔ ⦅ a ↔ b ⦆ ⦅ a ↔ b ⦆ d ⦆ ⦅ a ↔ b ⦆ x
         ≡˘⟨ cong (λ ◆ → ⦅ ◆ ↔ ⦅ a ↔ b ⦆ ⦅ a ↔ b ⦆ d ⦆ ⦅ a ↔ b ⦆ x) swap-sym′ ⟩
           ⦅ ⦅ a ↔ b ⦆ ⦅ a ↔ b ⦆ c ↔ ⦅ a ↔ b ⦆ ⦅ a ↔ b ⦆ d ⦆ ⦅ a ↔ b ⦆ x
         ≡˘⟨ swap-swap ⟩
           ⦅ a ↔ b ⦆ ⦅ ⦅ a ↔ b ⦆ c ↔ ⦅ a ↔ b ⦆ d ⦆ x
         ∎
       ⟩
        ⦅ ⦅ a ↔ b ⦆ c ↔ ⦅ a ↔ b ⦆ d ⦆ ⦅ a ↔ b ⦆
          (f $ ⦅ a ↔ b ⦆ ⦅ ⦅ a ↔ b ⦆ c ↔ ⦅ a ↔ b ⦆ d ⦆ x)
      ≡⟨⟩
        (⦅ ⦅ a ↔ b ⦆ c ↔ ⦅ a ↔ b ⦆ d ⦆ ⦅ a ↔ b ⦆ f) x
      ∎

  -- NB: swapping takes the conjugation action on functions
  module _ ⦃ _ : SwapLaws A ⦄ ⦃ _ : SwapLaws B ⦄ where
    conj : ∀ {𝕒 𝕓 : Atom} (f : A → B) (x : A) →
      (swap 𝕒 𝕓 f) x ≡ swap 𝕒 𝕓 (f $ swap 𝕒 𝕓 x)
    conj {𝕒} {𝕓} f x =
      begin
        (swap 𝕒 𝕓 f) x
      ≡⟨⟩
        (swap 𝕒 𝕓 ∘ f ∘ swap 𝕒 𝕓) x
      ≡⟨⟩
        swap 𝕒 𝕓 (f $ swap 𝕒 𝕓 x)
      ≡˘⟨ cong (swap _ _ ∘ f) swap-sym′ ⟩
        swap 𝕒 𝕓 (f $ swap 𝕒 𝕓 $ swap 𝕒 𝕓 $ swap 𝕒 𝕓 x)
      ≡⟨⟩
        (swap 𝕒 𝕓 ∘ f ∘ swap 𝕒 𝕓) (swap 𝕒 𝕓 $ swap 𝕒 𝕓 x)
      ≡⟨⟩
        (swap 𝕒 𝕓 f) (swap 𝕒 𝕓 $ swap 𝕒 𝕓 x)
      ≡˘⟨ distr-f 𝕒 𝕓 ⟩
        swap 𝕒 𝕓 (f $ swap 𝕒 𝕓 x)
      ∎ where distr-f = swap↔ f

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

module _ ⦃ _ : Enumerable∞ Atom ⦄ {A : Type ℓ} ⦃ _ : Swap A ⦄ ⦃ _ : SwapLaws A ⦄ where

  --  * in the case of _→_, Equivariant′ is equivalent to Equivariant
  equivariant-equiv : ∀ {f : A → A} →
    Equivariant f
    ══════════════
    Equivariant′ f
  equivariant-equiv {f = f} = ↝ , ↜
      where
        open ≡-Reasoning

        ↝ : Equivariant f
            ─────────────────
            Equivariant′ f
        ↝ equiv-f = fin-f , refl
          where
            fin-f : FinSupp f
            fin-f = [] , (λ x y _ _ → ext {A = A}{A} λ a →
              begin
                ⦅ y ↔ x ⦆ (f $ ⦅ y ↔ x ⦆ a)
              ≡˘⟨ cong (swap _ _) $ equiv-f _ _ ⟩
                ⦅ y ↔ x ⦆ ⦅ y ↔ x ⦆ f a
              ≡⟨ swap-sym′ ⟩
                f a
              ∎) , λ _ _ ()

        ↜ : Equivariant′ f
            ─────────────────
            Equivariant f
        ↜ (fin-f , refl) a b {x} =
          begin
            ⦅ a ↔ b ⦆ f x
          ≡˘⟨ cong (swap _ _ ∘ (_$ x)) $ fin-f .proj₂ .proj₁ _ _ (λ ()) (λ ()) ⟩
            ⦅ a ↔ b ⦆ ⦅ a ↔ b ⦆ f (⦅ a ↔ b ⦆ x)
          ≡⟨ swap-sym′ ⟩
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

    f≡g : f′ ≡ g′
    f≡g = ext {A = A}{A} λ _ → refl

    ∃fin-f : ∃FinSupp f′
    ∃fin-f = suppF′ , λ _ _ _ _ → ext {A = A}{A} λ _ → swap-sym′

    fin-f : FinSupp f′
    fin-f = suppF′ , (λ _ _ _ _ → ext {A = A}{A} λ _ → swap-sym′) , (λ _ _ ())

    equiv-f : Equivariant f′
    equiv-f _ _ = refl

    equiv-f′ : Equivariant′ f′
    equiv-f′ = fin-f , refl

    postulate x y : Atom

    f : Atom → Bool
    f z = (z == x) ∨ (z == y)
    suppF = List Atom ∋ x ∷ y ∷ []
    -- fresh f = False

    finF : ∃FinSupp f
    finF = -, (λ 𝕒 𝕓 𝕒∉ 𝕓∉ → ext {A = Atom}{Bool} λ z → go 𝕒 𝕓 𝕒∉ 𝕓∉ z)
      where
        ∀x∉suppF : ∀ {z} → z ∉ suppF → f z ≡ false
        ∀x∉suppF {z} z∉ with z ≟ x
        ... | yes refl = ⊥-elim $ z∉ $ here refl
        ... | no _ with z ≟ y
        ... | yes refl = ⊥-elim $ z∉ $ there $′ here refl
        ... | no _ = refl

        go : ∀ 𝕒 𝕓 → 𝕒 ∉ suppF → 𝕓 ∉ suppF → ∀ z → f (swap 𝕓 𝕒 z) ≡ f z
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

    finG : ∃FinSupp g
    finG = -, (λ 𝕒 𝕓 𝕒∉ 𝕓∉ → ext {A = Atom}{Bool} λ z → go 𝕒 𝕓 𝕒∉ 𝕓∉ z)
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
