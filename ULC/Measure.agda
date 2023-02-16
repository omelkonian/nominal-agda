open import Prelude.Init; open SetAsType
open import Prelude.DecEq
open import Prelude.General
open import Prelude.Closures
open import Prelude.InferenceRules
open import Prelude.Decidable
open import Prelude.Membership
open import Prelude.Setoid
open import Prelude.Bifunctor
open import Prelude.Measurable
open import Prelude.Ord
open import Prelude.InfEnumerable

-- ** Sizes for λ-terms, to be used as termination measures.
module ULC.Measure (Atom : Type) ⦃ _ : DecEq Atom ⦄ ⦃ _ : Enumerable∞ Atom ⦄ where

open import ULC.Base Atom
open import Nominal  Atom

private variable A : Type ℓ

-- module _ {A : Type}
--          ⦃ _ : LawfulSetoid A ⦄ ⦃ _ : Swap A ⦄ ⦃ _ : SwapLaws A ⦄
--          ⦃ _ : FinitelySupported A ⦄
--          ⦃ _ : Measurable A ⦄ where
--   mapAbs′ : (x' : Abs A) → ((x : A) → x ≺ᵐ x' → A) → Abs A
--   mapAbs′ x' f =
--     let a = fresh-var x'
--     in abs a (f (conc x' a) {!!})

instance
  Measurable-Abs : ⦃ Measurable A ⦄ → Measurable (Abs A)
  Measurable-Abs .∣_∣ (abs _ t) = suc ∣ t ∣

  Measurable-Shape : Measurable TermShape
  Measurable-Shape .∣_∣ = λ where
    `∎ → 1
    (l · r) → ∣ l ∣ + ∣ r ∣
    (ƛ s) → suc ∣ s ∣

  Measurable-Term : Measurable Term
  Measurable-Term .∣_∣ = ∣_∣ ∘ shape

-- swapping does not alter the size of a term
swap≡ : ∀ (t : Term) → ∣ swap x y t ∣ ≡ ∣ t ∣
swap≡ = cong ∣_∣ ∘ sym ∘ swap-shape≡ _ _

-- concretion reduces the size of a term by one
conc≡ : ∀ (f : Abs Term) x → ∣ conc f x ∣ ≡ Nat.pred ∣ f ∣
conc≡ (abs x t) _ = swap≡ t

-- ⇒ a concretized term is strictly smaller than the original
conc≺ : ∀ (f : Abs Term) x → ∣ conc f x ∣ ≺ ∣ f ∣
conc≺ f x rewrite conc≡ f x = Nat.≤-refl

-- the size of a term is always positive
measure⁺ : ∀ (t : Term) → ∣ t ∣ > 0
measure⁺ (` _) = s≤s z≤n
measure⁺ (l · m) with ∣ l ∣ | measure⁺ l | ∣ m ∣ | measure⁺ m
... | suc l′ | _ | suc m′ | _ = s≤s z≤n
measure⁺ (ƛ _) = s≤s z≤n

-- the size of an application's left operand is strictly smaller than the whole
_·≺ˡ_ : ∀ (L M : Term) → L ≺ (L · M)
_ ·≺ˡ M = Nat.m<m+n _ (measure⁺ M)

-- the size of an application's right operand is strictly smaller than the whole
_·≺ʳ_ : ∀ (L M : Term) → M ≺ (L · M)
L ·≺ʳ _ = Nat.m<n+m _ (measure⁺ L)
