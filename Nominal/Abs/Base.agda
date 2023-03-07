{-# OPTIONS --v equivariance:100 #-}
open import Prelude.Init; open SetAsType
open L.Mem
open import Prelude.DecEq
open import Prelude.Bifunctor
open import Prelude.InferenceRules

module Nominal.Abs.Base (Atom : Type) ⦃ _ : DecEq Atom ⦄ where

open import Nominal.New     Atom
open import Nominal.Swap    Atom

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

  -- ** α-equivalence
  _≗α_ : Rel (Abs A) _
  f ≗α g = И (λ 𝕩 → conc f 𝕩 ≡ conc g 𝕩)

  private
    variable
      𝕒 𝕓 𝕔 : Atom
      x : A

    _ : swap 𝕒 𝕓 (abs 𝕔 x)
      ≡ abs (swap 𝕒 𝕓 𝕔) (swap 𝕒 𝕓 x)
    _ = refl

    _ : conc (abs 𝕒 x) 𝕓 ≡ swap 𝕓 𝕒 x
    _ = refl

  module _ ⦃ _ : SwapLaws A ⦄ where
    -- swap-conc : ∀ (f : Abs A) →
    --   ⦅ 𝕒 ↔ 𝕓 ⦆ (conc f 𝕔) ≡ conc (⦅ 𝕒 ↔ 𝕓 ⦆ f) (⦅ 𝕒 ↔ 𝕓 ⦆ 𝕔)
    swap-conc : Equivariant conc
    swap-conc _ _ = swap-swap

    postulate extᵃ : _≗α_ ⇒² _≡_

    private variable f g h : Abs A

    ≗α-refl : f ≗α f
    ≗α-refl = [] , (λ _ _ → refl)

    ≗α-sym : f ≗α g → g ≗α f
    ≗α-sym = map₂′ (sym ∘₂_)

    ≗α-trans : f ≗α g → g ≗α h → f ≗α h
    ≗α-trans (xs , f≡g) (ys , g≡h) = (xs ++ ys) , λ y y∉ →
      trans (f≡g y (y∉ ∘ L.Mem.∈-++⁺ˡ)) (g≡h y (y∉ ∘ L.Mem.∈-++⁺ʳ xs))

    -- cong-conc : ∀ {t̂ t̂′ : Abs A} →
    --   ∀ (eq : t̂ ≡ t̂′) →
    --   ∙ 𝕒 ∉ eq .proj₁
    --     ────────────────────
    --     conc t̂  𝕒
    --   ≡ conc t̂′ 𝕒
    -- cong-conc (_ , eq) = eq _

    open ≡-Reasoning

    instance
      SwapLaws-Abs : SwapLaws (Abs A)
      SwapLaws-Abs .swap-id {a}{abs x t} =
        begin
          ⦅ a ↔ a ⦆ abs x t
        ≡⟨⟩
          abs (⦅ a ↔ a ⦆ x) (⦅ a ↔ a ⦆ t)
        ≡⟨ cong (λ ◆ → abs ◆ (⦅ a ↔ a ⦆ t)) swap-id ⟩
          abs x (⦅ a ↔ a ⦆ t)
        ≡⟨ cong (abs _) swap-id ⟩
          abs x t
        ∎
      SwapLaws-Abs .swap-rev {a}{b}{f@(abs 𝕩 t)} = extᵃ $
        a ∷ b ∷ [] , λ x x∉ →
        begin
          conc (⦅ a ↔ b ⦆ f) x
        ≡⟨⟩
          conc (abs (⦅ a ↔ b ⦆ 𝕩) (⦅ a ↔ b ⦆ t)) x
        ≡⟨ cong (λ ◆ → conc (abs ◆ (⦅ a ↔ b ⦆ t)) x) swap-rev ⟩
          conc (abs (⦅ b ↔ a ⦆ 𝕩) (⦅ a ↔ b ⦆ t)) x
        ≡⟨ cong (λ ◆ → conc (abs _ ◆) x) swap-rev ⟩
          conc (abs (⦅ b ↔ a ⦆ 𝕩) (⦅ b ↔ a ⦆ t)) x
        ≡⟨⟩
          conc (⦅ b ↔ a ⦆ f) x
        ∎
      SwapLaws-Abs .swap-sym {a}{b}{f@(abs 𝕩 t)} = extᵃ $
        a ∷ b ∷ [] , λ x x∉ →
        begin
          conc (⦅ a ↔ b ⦆ ⦅ b ↔ a ⦆ f) x
        ≡⟨⟩
          conc (abs (⦅ a ↔ b ⦆ ⦅ b ↔ a ⦆ 𝕩) (⦅ a ↔ b ⦆ ⦅ b ↔ a ⦆ t)) x
        ≡⟨ cong (λ ◆ → conc (abs ◆ (⦅ a ↔ b ⦆ ⦅ b ↔ a ⦆ t)) x) swap-sym ⟩
          conc (abs 𝕩 (⦅ a ↔ b ⦆ ⦅ b ↔ a ⦆ t)) x
        ≡⟨ cong (λ ◆ → conc (abs _ ◆) x) swap-sym ⟩
          conc (abs 𝕩 t) x
        ≡⟨⟩
          conc f x
        ∎
      SwapLaws-Abs .swap-swap {a}{b}{c}{d}{f@(abs 𝕩 t)} = extᵃ $
        a ∷ b ∷ c ∷ d ∷ [] , λ x x∉ →
        begin
          conc (⦅ a ↔ b ⦆ ⦅ c ↔ d ⦆ f) x
        ≡⟨⟩
          conc (abs (⦅ a ↔ b ⦆ ⦅ c ↔ d ⦆ 𝕩) (⦅ a ↔ b ⦆ ⦅ c ↔ d ⦆ t)) x
        ≡⟨ cong (λ ◆ → conc (abs ◆ (⦅ a ↔ b ⦆ ⦅ c ↔ d ⦆ t)) x) swap-swap ⟩
          conc (abs (⦅ ⦅ a ↔ b ⦆ c ↔ ⦅ a ↔ b ⦆ d ⦆ ⦅ a ↔ b ⦆ 𝕩)
                    (⦅ a ↔ b ⦆ ⦅ c ↔ d ⦆ t)) x
        ≡⟨ cong (λ ◆ → conc (abs _ ◆) x) $ swap-swap ⟩
          conc (⦅ ⦅ a ↔ b ⦆ c ↔ ⦅ a ↔ b ⦆ d ⦆ ⦅ a ↔ b ⦆ f) x
        ∎

    --   concₓ : Abs A → A
    --   concₓ = flip conc 𝕩

    --   mor : Abs A —𝔾→ A
    --   mor = record { f = concₓ ; equivariant = {!swap-swap!} }
