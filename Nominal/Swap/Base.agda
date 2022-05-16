open import Prelude.Init
open import Prelude.General
open import Prelude.DecEq
open import Prelude.Decidable

module Nominal.Swap.Base (Atom : Set) ⦃ _ : DecEq Atom ⦄ where

private variable A : Set ℓ

record Swap (A : Set ℓ) : Set ℓ where
  field swap : Atom → Atom → A → A
  -- T0D0: ++ swap forms a group action by the group of atom permutations
  -- i.e. ∙ id x = x
  --      ∙ p (p′ x) = (p ∘ p′) x

  -- NB: equivariant functions commute with this group action
open Swap ⦃...⦄ public

instance
  Atom↔ : Swap Atom
  Atom↔ .swap a₁ a₂ a =
    if      a == a₁ then a₂
    else if a == a₂ then a₁
    else                 a

swapId : Atom → Atom → A → A
swapId _ _ = id

mkNameless : (A : Set) → Swap A
mkNameless A = λ where .swap → swapId

-- ** Nameless instances.
instance
  ⊤∅ = mkNameless ⊤
  𝔹∅ = mkNameless Bool
  ℕ∅ = mkNameless ℕ
  ℤ∅ = mkNameless ℤ
  Char∅   = mkNameless Char
  String∅ = mkNameless String

{-
record Nameless (A : Set ℓ) : Set ℓ where
  field ⦃ register ⦄ : ⊤
open Nameless ⦃...⦄

instance
  ⊤∅      = Nameless ⊤ ∋ it
  Bool∅   = Nameless Bool ∋ it
  ℕ∅      = Nameless ℕ ∋ it
  Char∅   = Nameless Char ∋ it
  String∅ = Nameless String ∋ it

  Nameless↔ : ⦃ Nameless A ⦄ → Swap A
  Nameless↔ .swap = swapId
-}

swapˡ : ∀ 𝕒 𝕓 → swap 𝕒 𝕓 𝕒 ≡ 𝕓
swapˡ 𝕒 𝕓 rewrite ≟-refl 𝕒 = refl

swapʳ : ∀ 𝕒 𝕓 → swap 𝕒 𝕓 𝕓 ≡ 𝕒
swapʳ 𝕒 𝕓 with 𝕓 ≟ 𝕒
... | yes refl = refl
... | no  𝕓≢
  rewrite T⇒true $ fromWitnessFalse {Q = 𝕓 ≟ 𝕒} 𝕓≢
        | ≟-refl 𝕓
        = refl

swap-noop : ∀ 𝕒 𝕓 x → x L.Mem.∉ 𝕒 ∷ 𝕓 ∷ []  → swap 𝕒 𝕓 x ≡ x
swap-noop 𝕒 𝕓 x x∉ with x ≟ 𝕒
... | yes refl = ⊥-elim $ x∉ $ here refl
... | no _ with x ≟ 𝕓
... | yes refl = ⊥-elim $ x∉ $ there $′ here refl
... | no _ = refl
