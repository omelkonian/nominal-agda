open import Prelude.Init
open import Prelude.General
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.Setoid

module Nominal.Swap.Base (Atom : Set) ⦃ _ : DecEq Atom ⦄ where

-- data Permutation
--   idᵖ  : Permutation A
--   _∘ᵖ_ : Permutation A → Permutation A → Permutation A
--   _∷ᵖ_ : (→ Permutation A → Permutation A

-- Perm =

-- instance
--   Semigroup-Perm : Semigroup Perm
--   Semigroup-Perm ._◇_ f g = f ∘ g

record Swap (A : Set ℓ) : Set ℓ where
  field swap : Atom → Atom → A → A
  -- T0D0: ++ swap forms a group action by the group of atom permutations
  -- i.e. ∙ id x = x
  --      ∙ p (p′ x) = (p ∘ p′) x

  -- NB: equivariant functions commute with this group action

  swaps : List (Atom × Atom) → A → A
  swaps []             = id
  swaps ((x , y) ∷ as) = swap x y ∘ swaps as
open Swap ⦃...⦄ public

private variable
  A : Set ℓ
  𝕒 𝕓 𝕔 𝕕 : Atom
  x y : A

-- record SwapLaws (A : Set ℓ) ⦃ _ : Swap A ⦄ ⦃ _ : ISetoid A ⦄ : Set ℓ where
--   field
--     -- swap∘swap : swap 𝕒 𝕓 (swap 𝕔 𝕕 x) ≈ swap swap
-- open SwapLaws ⦃...⦄ public

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
