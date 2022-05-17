open import Prelude.Init
open L.Mem
open import Prelude.DecEq

module Nominal.Support (Atom : Set) ⦃ _ : DecEq Atom ⦄ where

open import Nominal.Swap Atom ⦃ it ⦄
open import Nominal.Abs  Atom ⦃ it ⦄

open import Prelude.Setoid

private variable
  a b : Level
  A : Set a
  B : Set b

instance
  Setoid-→ : ISetoid (A → B)
  Setoid-→ = λ where
    .relℓ → _
    ._≈_  → _≗_

  SetoidLaws-→ : Setoid-Laws (A → B)
  SetoidLaws-→ {A = A} {B = B} .isEquivalence = Setoid.isEquivalence (A PropEq.→-setoid B)

module _ ⦃ _ : Swap A ⦄ ⦃ _ : ISetoid A ⦄ ⦃ _ : Setoid-Laws A ⦄ where
  FinSupp : Pred A _
  -- FinSupp x = И λ 𝕒 → И λ 𝕓 → swap 𝕓 𝕒 x ≈ x
  FinSupp x = И² λ 𝕒 𝕓 → swap 𝕓 𝕒 x ≈ x

  supp : ∀ x → FinSupp x → List Atom
  supp _ = proj₁

-- instance
--   Swap-Atom→Bool : Swap (Atom → Bool)
--   Swap-Atom→Bool .swap 𝕒 𝕓 f = f ∘ swap 𝕒 𝕓

private

  postulate x y : Atom

  f : Atom → Bool
  f z = (z == x) ∨ (z == y)
  -- supp(f) = {x,y}
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

  _ = supp f finF ≡ suppF
    ∋ refl

  g : Atom → Bool
  g z = (z ≠ x) ∧ (z ≠ y)
  -- supp(g) = {x,y}
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
