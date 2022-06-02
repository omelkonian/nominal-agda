{- MOTTO: permutations distribute over everything -}
-- {-# OPTIONS --sized-types #-}
open import Prelude.Init
open SetAsType
open import Prelude.General
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.Setoid
open import Prelude.InferenceRules
open import Prelude.Measurable

module Nominal.Swap.Base2 (Atom : Set) ⦃ _ : DecEq Atom ⦄ where

Atoms = List Atom

Measure = ℕ
MType : ∀ ℓ → Type (lsuc ℓ)
MType ℓ = Measure → Type ℓ

private variable n m : Measure

record Swap (A : Type ℓ) ⦃ _ : Measurable A ⦄ : Set ℓ where
  field
    swap : Atom → Atom → A → A
    size-preserving : ∀ {x y a} → ∣ swap x y a ∣ ≡ ∣ a ∣
  infixr 10 ⦅_↔_⦆_
  ⦅_↔_⦆_ = swap

  swaps : List (Atom × Atom) → A → A
  swaps []             = id
  swaps ((x , y) ∷ as) = swap x y ∘ swaps as
open Swap ⦃...⦄ public

instance
  MAtom : Measurable Atom
  MAtom .∣_∣ = const 1

  Swap-Atom : Swap Atom
  Swap-Atom .swap a₁ a₂ a =
    if      a == a₁ then a₂
    else if a == a₂ then a₁
    else                 a
  Swap-Atom .size-preserving = refl

private
  data Seq : Type where
    ∙  : Seq
    ⟨_⟩_⊗_ : Atom → Seq → Seq → Seq

  instance
    MSeq : Measurable Seq
    MSeq .∣_∣ = λ where
      ∙ → 1
      (⟨ _ ⟩ l ⊗ r) → ∣ l ∣ + ∣ r ∣

    Swap-Seq : Swap Seq
    Swap-Seq .swap a b = λ where
      ∙ → ∙
      (⟨ c ⟩ x ⊗ y) → ⟨ swap a b c ⟩ swap a b x ⊗ swap a b y
      -- (⟨ c ⟩ x ⊗ y) → ⟨ swap a b c ⟩ swap a b x ⊗ ⟨ a ⟩ x ⊗ y
      -- ^ this isn't accepted
      -- (⟨ c ⟩ x ⊗ y) → ⟨ swap a b c ⟩ swap a b y ⊗ swap a b x
      -- ^ this is accepted, same size different shape

    Swap-Seq .size-preserving {x} {y} {∙} = refl
    Swap-Seq .size-preserving {x} {y} {⟨ _ ⟩ l ⊗ r}
      rewrite size-preserving {x = x}{y}{l}
            | size-preserving {x = x}{y}{r}
            -- | Nat.+-comm ∣ l ∣ ∣ r ∣
            = refl

{- -- sized types do not help us here, no 0
open import Size

private variable s s′ s″ n m : Size

record Swap (A : SizedSet ℓ) : Set ℓ where
  field swap : Atom → Atom → A s → A s
  infixr 10 ⦅_↔_⦆_
  ⦅_↔_⦆_ = swap

  swaps : List (Atom × Atom) → A s → A s
  swaps []             = id
  swaps ((x , y) ∷ as) = swap x y ∘ swaps as
open Swap ⦃...⦄ public

instance
  Swap-Atom : Swap (λ _ → Atom)
  Swap-Atom .swap a₁ a₂ a =
    if      a == a₁ then a₂
    else if a == a₂ then a₁
    else                 a

private
-- postulate 0s : Size
  data Seq : SizedSet 0ℓ where
    ∙   : Seq s
    ⟨_⟩_⊗_ : Atom → Seq n → Seq m → Seq (n ⊔ˢ m)

  instance
    Swap-Seq : Swap Seq
    Swap-Seq .swap a b = λ where
      ∙ → ∙
      (⟨ c ⟩ x ⊗ y) → ⟨ swap a b c ⟩ (swap a b x) ⊗ (swap a b y)
      -- (⟨ c ⟩ x ⊗ y) → ⟨ swap a b c ⟩ (swap a b x) ⊗ (⟨ a ⟩ x ⊗ y)
      -- ^ this shouldn't be accepted, need something like ∙ : Seq 0
-}
