open import Agda.Primitive using () renaming (Set to Type)
open import Prelude.Init
open import Prelude.DecEq
open import Prelude.General
open import Prelude.Closures
open import Prelude.InferenceRules
open import Prelude.Decidable
open import Prelude.Membership

-- ** α-equivalence.
module ULC.Alpha {- (Atom : Set) ⦃ _ : DecEq Atom ⦄ -} where

open import ULC.Base
open import Nominal Atom

data _≡α_ : Term → Term → Type₀ where

  ν≡ :
    ──────────
    ` x ≡α ` x

  ζ≡_ : ∀ {f g} →

    ∙ И (λ 𝕩 → conc f 𝕩 ≡α conc g 𝕩)
      ──────────────────────────────
      (ƛ f) ≡α (ƛ g)

  ξ≡ :
    ∙ L ≡α L′
    ∙ M ≡α M′
      ─────────────────
      (L · M) ≡α (L′ · M′)

_≢α_ = ¬_ ∘₂ _≡α_

private
  _ = (` a) ≡α (` a) ∋ ν≡

  _ : (ƛ a ⇒ ` a) ≡α (ƛ b ⇒ ` b)
  _ = ζ≡ (-, qed)
    where qed : ∀ y → y L.Mem.∉ [] → swap y a (` a) ≡α swap y b (` b)
          qed y _ rewrite swapʳ y a | swapʳ y b = ν≡

  -- _ : (ƛ c ⇒ ƛ a ⇒ ` c · ` a) ≡α (ƛ c ⇒ ƛ b ⇒ ` c · ` b)
  -- _ : (ƛ c ⇒ ƛ a ⇒ ` c · ` a) ≡α (ƛ d ⇒ ƛ b ⇒ ` d · ` b)
  -- _ : (ƛ c ⇒ ƛ a ⇒ ` c · ` a) ≢α (ƛ d ⇒ ƛ b ⇒ ` c · ` b)
