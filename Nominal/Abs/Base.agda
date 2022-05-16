open import Prelude.Init
open import Prelude.DecEq

module Nominal.Abs.Base (Atom : Set) ⦃ _ : DecEq Atom ⦄ where

open import Nominal.Swap Atom

-- T0D0: maybe this is broken, user has access to `atom`
record Abs (A : Set ℓ) : Set ℓ where
  constructor abs
  field atom : Atom
        term : A
open Abs public

module _ {ℓ} {A : Set ℓ} ⦃ _ : Swap A ⦄ where

  conc : Abs A → Atom → A
  conc (abs 𝕒 x) 𝕓 = swap 𝕓 𝕒 x
  -- T0D0: prove that conc is equivariant

  instance
    -- this is the conjugation action for nominal abstractions
    -- (terminology from G-sets, sets with a group action)
    Swap-Abs : Swap (Abs A)
    Swap-Abs .swap 𝕒 𝕓 (abs 𝕔 x) = abs (swap 𝕒 𝕓 𝕔) (swap 𝕒 𝕓 x)

  private
    variable
      𝕒 𝕓 𝕔 : Atom
      x : A

    _ : swap 𝕒 𝕓 (abs 𝕔 x)
      ≡ abs (swap 𝕒 𝕓 𝕔) (swap 𝕒 𝕓 x)
    _ = refl

    _ : conc (abs 𝕒 x) 𝕓 ≡ swap 𝕓 𝕒 x
    _ = refl

  postulate
    swap∘swap : ∀ a b c d (x : A) →
      swap a b (swap c d x) ≡ swap c d (swap a b x)
  -- swap∘swap a b c d x = {!!}

    swap∘swap∘swap : ∀ a b c d (x : A) →
      swap a (swap b c d) (swap b c x) ≡ swap b c (swap a d x)
  -- swap∘swap∘swap a b c d x
  --   with d ≟ b
  -- ... | yes refl
  --   = begin
  --     swap a c (swap b c x)
  --   ≡⟨ {!!} ⟩
  --     swap b c (swap a b x)
  --   ∎ where open ≡-Reasoning
  -- ... | no _
  --   with d ≟ c
  -- ... | yes refl
  --   = begin
  --     swap a b (swap b c x)
  --   ≡⟨ {!!} ⟩
  --     swap b c (swap a c x)
  --   ∎ where open ≡-Reasoning
  -- ... | no _ = swap∘swap _ _ _ _ x

  -- T0D0: pick И z, i.e. xs′ = x ∷ y ∷ xs
  conc∘swap : ∀ x y z f → conc (swap x y f) z ≡ swap x y (conc f z)
  conc∘swap x y z (abs 𝕩 t) =
    begin
      conc (swap x y (abs 𝕩 t)) z
    ≡⟨⟩
      conc (abs (swap x y 𝕩) (swap x y t)) z
    ≡⟨⟩
      conc (abs (swap x y 𝕩) (swap x y t)) z
    ≡⟨⟩
      swap z (swap x y 𝕩) (swap x y t)
    ≡⟨ swap∘swap∘swap _ _ _ _ _ ⟩
      swap x y (swap z 𝕩 t)
    ≡⟨⟩
      swap x y (conc (abs 𝕩 t) z)
    ∎ where open ≡-Reasoning
