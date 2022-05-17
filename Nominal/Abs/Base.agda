open import Prelude.Init
open SetAsType
open import Prelude.DecEq
open import Prelude.Membership
open import Prelude.Setoid
open import Prelude.Bifunctor

module Nominal.Abs.Base (Atom : Type) ⦃ _ : DecEq Atom ⦄ where

open import Nominal.Swap Atom

-- T0D0: maybe this is broken, user has access to `atom`
record Abs (A : Type ℓ) : Type ℓ where
  constructor abs
  field atom : Atom
        term : A
open Abs public

-- ** The И quantifier.
И : Pred (Pred Atom ℓ) ℓ
И φ = ∃ λ (xs : List Atom) → (∀ y → y ∉ xs → φ y)

-- И∗ : Pred (Pred (List Atom) ℓ) ℓ
-- И∗ φ = ∃ λ (xs : List Atom) → (∀ ys → All (_∉ xs) ys → φ ys)

И^_ : (n : ℕ) → Pred (Pred (Vec Atom n) ℓ) ℓ
(И^ n) φ = ∃ λ (xs : List Atom) → (∀ ys → V.All.All (_∉ xs) ys → φ ys)

И² : Pred (Atom → Atom → Type ℓ) ℓ
-- И² φ = (И^ 2) λ where (x ∷ y ∷ []) → φ x y
И² φ = ∃ λ (xs : List Atom) → (∀ y z → y ∉ xs → z ∉ xs → φ y z)

И³ : Pred (Atom → Atom → Atom → Type ℓ) ℓ
-- И³ φ = (И^ 3) λ where (x ∷ y ∷ z ∷ []) → φ x y z
И³ φ = ∃ λ (xs : List Atom) → (∀ y z w → y ∉ xs → z ∉ xs → w ∉ xs → φ y z w)

module _ {ℓ} {A : Type ℓ} ⦃ _ : Swap A ⦄ where

  conc : Abs A → Atom → A
  conc (abs 𝕒 x) 𝕓 = swap 𝕓 𝕒 x
  -- T0D0: prove that conc is equivariant
  -- ∀ (f : Abs A). conc (swap 𝕒 𝕓 f) 𝕔 ≈ swap 𝕒 𝕓 (conc f 𝕔)

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

  -- ** the co-finite construction leads to issues with universe levels.
  -- open import Cofinite.agda
  -- И : Pred (Pred Atom ℓ) (lsuc ℓ)
  -- И P = powᶜᵒᶠ P

  -- ** α-equivalence
  module _ ⦃ _ : Lawful-Setoid A ⦄ where
    _≈α_ : Rel (Abs A) relℓ
    f ≈α g = И (λ 𝕩 → conc f 𝕩 ≈ conc g 𝕩)

    instance
      Setoid-Abs : ISetoid (Abs A)
      Setoid-Abs = λ where
        .relℓ → relℓ
        ._≈_  → _≈α_

    private variable f g h : Abs A

    ≈α-refl : f ≈α f
    ≈α-refl = [] , (λ _ _ → ≈-refl)

    ≈α-sym : f ≈α g → g ≈α f
    ≈α-sym = map₂′ (≈-sym ∘₂_)

    ≈α-trans : f ≈α g → g ≈α h → f ≈α h
    ≈α-trans (xs , f≈g) (ys , g≈h) =
      (xs ++ ys) , λ y y∉ → ≈-trans (f≈g y (y∉ ∘ L.Mem.∈-++⁺ˡ)) (g≈h y (y∉ ∘ L.Mem.∈-++⁺ʳ xs))

    instance
      SetoidLaws-Abs : Setoid-Laws (Abs A)
      SetoidLaws-Abs .isEquivalence = record
        { refl = ≈α-refl ; sym = ≈α-sym ; trans = ≈α-trans }

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
      swap z (swap x y 𝕩) (swap x y t)
    ≡⟨ swap∘swap∘swap _ _ _ _ _ ⟩
      swap x y (swap z 𝕩 t)
    ≡⟨⟩
      swap x y (conc (abs 𝕩 t) z)
    ∎ where open ≡-Reasoning
