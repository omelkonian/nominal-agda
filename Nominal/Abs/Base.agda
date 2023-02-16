open import Prelude.Init; open SetAsType
open L.Mem
open import Prelude.DecEq
open import Prelude.Setoid
open import Prelude.Bifunctor
open import Prelude.InferenceRules

module Nominal.Abs.Base (Atom : Type) ⦃ _ : DecEq Atom ⦄ where

open import Nominal.New     Atom
open import Nominal.Swap    Atom
open import Nominal.Support Atom

-- T0D0: maybe this is broken, user has access to `atom`
record Abs (A : Type ℓ) : Type ℓ where
  constructor abs
  field atom : Atom
        term : A
open Abs public

module _ {A : Type ℓ} ⦃ _ : Swap A ⦄ where

  conc : Abs A → Atom → A
  conc (abs 𝕒 x) 𝕓 = swap 𝕓 𝕒 x

  instance
    Swap-Abs : Swap (Abs A)
    Swap-Abs .swap 𝕒 𝕓 (abs 𝕔 x) = abs (swap 𝕒 𝕓 𝕔) (swap 𝕒 𝕓 x)
    -- this is the conjugation action for nominal abstractions
    -- (terminology from G-sets, sets with a group action)

  private
    variable
      𝕒 𝕓 𝕔 : Atom
      x : A

    _ : swap 𝕒 𝕓 (abs 𝕔 x)
      ≡ abs (swap 𝕒 𝕓 𝕔) (swap 𝕒 𝕓 x)
    _ = refl

    _ : conc (abs 𝕒 x) 𝕓 ≡ swap 𝕓 𝕒 x
    _ = refl

  module _ ⦃ is : ISetoid A ⦄ ⦃ _ : SetoidLaws A ⦄ ⦃ _ : SwapLaws A ⦄ where
    swap-conc : ∀ (f : Abs A) →
      ⦅ 𝕒 ↔ 𝕓 ⦆ (conc f 𝕔) ≈ conc (⦅ 𝕒 ↔ 𝕓 ⦆ f) (⦅ 𝕒 ↔ 𝕓 ⦆ 𝕔)
    swap-conc _ = swap-swap

    -- ** α-equivalence
    _≈α_ : Rel (Abs A) (is .relℓ)
    f ≈α g = И (λ 𝕩 → conc f 𝕩 ≈ conc g 𝕩)

    instance
      Setoid-Abs : ISetoid (Abs A)
      Setoid-Abs = λ where
        .relℓ → is .relℓ
        ._≈_  → _≈α_

    private variable f g h : Abs A

    ≈α-refl : f ≈α f
    ≈α-refl = [] , (λ _ _ → ≈-refl)

    ≈α-sym : f ≈α g → g ≈α f
    ≈α-sym = map₂′ (≈-sym ∘₂_)

    ≈α-trans : f ≈α g → g ≈α h → f ≈α h
    ≈α-trans (xs , f≈g) (ys , g≈h) = (xs ++ ys) , λ y y∉ →
      ≈-trans (f≈g y (y∉ ∘ L.Mem.∈-++⁺ˡ)) (g≈h y (y∉ ∘ L.Mem.∈-++⁺ʳ xs))

    instance
      SetoidLaws-Abs : SetoidLaws (Abs A)
      SetoidLaws-Abs .isEquivalence = record
        { refl = ≈α-refl ; sym = ≈α-sym ; trans = ≈α-trans }

    cong-abs : ∀ {t t′ : A} → t ≈ t′ → abs 𝕒 t ≈ abs 𝕒 t′
    cong-abs t≈ = [] , λ _ _ → cong-swap t≈

    cong-conc : ∀ {t̂ t̂′ : Abs A} →
      ∀ (eq : t̂ ≈ t̂′) →
      ∙ 𝕒 ∉ eq .proj₁
        ────────────────────
        conc t̂  𝕒
      ≈ conc t̂′ 𝕒
    cong-conc (_ , eq) = eq _

    cong-conc∘abs : ∀ {t t′ : A} →
      ∀ (eq : t ≈ t′) →
        ────────────────────
        conc (abs 𝕓 t)  𝕒
      ≈ conc (abs 𝕓 t′) 𝕒
    cong-conc∘abs eq = cong-conc (cong-abs eq) λ ()

    open ≈-Reasoning

    instance
      SwapLaws-Abs : SwapLaws (Abs A)
      SwapLaws-Abs .cong-swap {f@(abs 𝕩 t)}{g@(abs 𝕪 t′)}{a}{b} (xs , f≈g)
        = a ∷ b ∷ xs , λ x x∉  →
          begin
            conc (⦅ a ↔ b ⦆ f) x
          ≡⟨⟩
            conc (abs (⦅ a ↔ b ⦆ 𝕩) (⦅ a ↔ b ⦆ t)) x
          ≡⟨⟩
            ⦅ x ↔ ⦅ a ↔ b ⦆ 𝕩 ⦆ ⦅ a ↔ b ⦆ t
          ≡˘⟨ cong (λ ◆ → ⦅ ◆ ↔ ⦅ a ↔ b ⦆ 𝕩 ⦆ ⦅ a ↔ b ⦆ t)
                  $ swap-noop a b x (λ where ♯0 → x∉ ♯0; ♯1 → x∉ ♯1) ⟩
            ⦅ ⦅ a ↔ b ⦆ x ↔ ⦅ a ↔ b ⦆ 𝕩 ⦆ ⦅ a ↔ b ⦆ t
          ≈˘⟨ swap-conc f ⟩
            ⦅ a ↔ b ⦆ conc f x
          ≈⟨ cong-swap $ f≈g x (x∉ ∘′ there ∘′ there) ⟩
            ⦅ a ↔ b ⦆ conc g x
          ≈⟨ swap-conc g ⟩
            ⦅ ⦅ a ↔ b ⦆ x ↔ ⦅ a ↔ b ⦆ 𝕪 ⦆ ⦅ a ↔ b ⦆ t′
          ≡⟨ cong (λ ◆ → ⦅ ◆ ↔ ⦅ a ↔ b ⦆ 𝕪 ⦆ ⦅ a ↔ b ⦆ t′)
                $ swap-noop a b x (λ where ♯0 → x∉ ♯0; ♯1 → x∉ ♯1) ⟩
            ⦅ x ↔ ⦅ a ↔ b ⦆ 𝕪 ⦆ ⦅ a ↔ b ⦆ t′
          ≡⟨⟩
            conc (abs (⦅ a ↔ b ⦆ 𝕪) (⦅ a ↔ b ⦆ t′)) x
          ≡⟨⟩
            conc (⦅ a ↔ b ⦆ g) x
          ∎
      SwapLaws-Abs .swap-id {a}{abs x t} =
        begin
          ⦅ a ↔ a ⦆ abs x t
        ≡⟨⟩
          abs (⦅ a ↔ a ⦆ x) (⦅ a ↔ a ⦆ t)
        ≡⟨ cong (λ ◆ → abs ◆ (⦅ a ↔ a ⦆ t)) swap-id ⟩
          abs x (⦅ a ↔ a ⦆ t)
        ≈⟨ cong-abs swap-id ⟩
          abs x t
        ∎
      SwapLaws-Abs .swap-rev {a}{b}{f@(abs 𝕩 t)} =
        a ∷ b ∷ [] , λ x x∉ →
        begin
          conc (⦅ a ↔ b ⦆ f) x
        ≡⟨⟩
          conc (abs (⦅ a ↔ b ⦆ 𝕩) (⦅ a ↔ b ⦆ t)) x
        ≡⟨ cong (λ ◆ → conc (abs ◆ (⦅ a ↔ b ⦆ t)) x) swap-rev ⟩
          conc (abs (⦅ b ↔ a ⦆ 𝕩) (⦅ a ↔ b ⦆ t)) x
        ≈⟨ cong-abs swap-rev .proj₂ x (λ ()) ⟩
          conc (abs (⦅ b ↔ a ⦆ 𝕩) (⦅ b ↔ a ⦆ t)) x
        ≡⟨⟩
          conc (⦅ b ↔ a ⦆ f) x
        ∎
      SwapLaws-Abs .swap-sym {a}{b}{f@(abs 𝕩 t)} =
        a ∷ b ∷ [] , λ x x∉ →
        begin
          conc (⦅ a ↔ b ⦆ ⦅ b ↔ a ⦆ f) x
        ≡⟨⟩
          conc (abs (⦅ a ↔ b ⦆ ⦅ b ↔ a ⦆ 𝕩) (⦅ a ↔ b ⦆ ⦅ b ↔ a ⦆ t)) x
        ≡⟨ cong (λ ◆ → conc (abs ◆ (⦅ a ↔ b ⦆ ⦅ b ↔ a ⦆ t)) x) swap-sym ⟩
          conc (abs 𝕩 (⦅ a ↔ b ⦆ ⦅ b ↔ a ⦆ t)) x
        ≈⟨ cong-abs swap-sym .proj₂ x (λ ()) ⟩
          conc (abs 𝕩 t) x
        ≡⟨⟩
          conc f x
        ∎
      SwapLaws-Abs .swap-swap {a}{b}{c}{d}{f@(abs 𝕩 t)} =
        a ∷ b ∷ c ∷ d ∷ [] , λ x x∉ →
        begin
          conc (⦅ a ↔ b ⦆ ⦅ c ↔ d ⦆ f) x
        ≡⟨⟩
          conc (abs (⦅ a ↔ b ⦆ ⦅ c ↔ d ⦆ 𝕩) (⦅ a ↔ b ⦆ ⦅ c ↔ d ⦆ t)) x
        ≡⟨ cong (λ ◆ → conc (abs ◆ (⦅ a ↔ b ⦆ ⦅ c ↔ d ⦆ t)) x) swap-swap ⟩
          conc (abs (⦅ ⦅ a ↔ b ⦆ c ↔ ⦅ a ↔ b ⦆ d ⦆ ⦅ a ↔ b ⦆ 𝕩)
                    (⦅ a ↔ b ⦆ ⦅ c ↔ d ⦆ t)) x
        ≈⟨ cong-abs swap-swap .proj₂ x (λ ()) ⟩
          conc (⦅ ⦅ a ↔ b ⦆ c ↔ ⦅ a ↔ b ⦆ d ⦆ ⦅ a ↔ b ⦆ f) x
        ∎

    --   concₓ : Abs A → A
    --   concₓ = flip conc 𝕩

    --   mor : Abs A —𝔾→ A
    --   mor = record { f = concₓ ; equivariant = {!swap-swap!} }
