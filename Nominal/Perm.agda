open import Prelude.Init; open SetAsType
open import Prelude.DecEq
open import Prelude.Semigroup
open import Prelude.Monoid
open import Prelude.Group
open import Prelude.Setoid

module Nominal.Perm (Atom : Type) ⦃ _ : DecEq Atom ⦄ where

open import Nominal.Swap Atom

-- ** permutations
Perm = Atom × Atom
Perms = List Perm
-- SwapList implements Perms
-- ???      implements Perms

module _ {ℓ} {A : Type ℓ} ⦃ _ : Swap A ⦄ where

  permute : Perm → A → A
  permute = uncurry swap

  permute∗ : Perms → A → A
  permute∗ = chain ∘ map permute
    where chain = foldr _∘′_ id

  instance
    Setoid-Perms : ISetoid Perms
    Setoid-Perms = λ where
      .relℓ → ℓ
      ._≈_ → _≗_ on permute∗

    Semigroup-Perms : Semigroup Perms
    Semigroup-Perms ._◇_ = _++_

    -- SemigroupLaws-Perms : SemigroupLaws≡ Perms
    -- SemigroupLaws-Perms = record { ◇-comm = {!◇-comm!} ; ◇-assocʳ = {!!} }

    Monoid-Perms : Monoid Perms
    Monoid-Perms .ε = []

    MonoidLaws-Perms : MonoidLaws≡ Perms
    MonoidLaws-Perms = MonoidLaws-List

    Group-Perms : Group Perms
    Group-Perms ._⁻¹ = L.reverse ∘ map Product.swap

{-
    GroupLaws-Perms : GroupLaws Perms _≈_
    GroupLaws-Perms = record {inverse = invˡ , invʳ; ⁻¹-cong = inv-cong}
      where
        open Alg _≈_
        -- open Group Group-Perms

        invˡ : LeftInverse [] _⁻¹ _++_
        invˡ [] = λ _ → refl
        invˡ (p ∷ ps)
          = {!!}

        -- rewrite invˡ ps x = {!!}

        invʳ : RightInverse [] _⁻¹ _++_
        invʳ = {!!}

        inv-cong : Congruent₁ _⁻¹
        inv-cong = {!!}
-}


  module _ ⦃ setoidA : ISetoid A ⦄ ⦃ _ : SetoidLaws A ⦄ ⦃ _ : SwapLaws A ⦄ where

    open Actionˡ

    swaps-++ : ∀ (ps ps′ : Perms) {x : A} →
      swaps (ps ++ ps′) x ≈ swaps ps (swaps ps′ x)
    swaps-++ [] _ = ≈-refl
    swaps-++ (_ ∷ ps) _ = cong-swap $ swaps-++ ps _

    Perms-Action : Actionˡ Perms A
    Perms-Action = λ where
      ._·_ → swaps
      .identity → ≈-refl
      .compatibility {ps}{ps′} → ≈-sym $ swaps-++ ps ps′

    instance
      Perms-GSet : GSet Perms A
      Perms-GSet .action = Perms-Action

    Perms-GSet′ : GSet′ Perms
    Perms-GSet′ = λ where
      .ℓₓ → ℓ
      .X  → A
      .setoidX → setoidA
      .action′ → Perms-Action

    open GSet-Morphisms Perms public
    -- equivariant maps betweens G-sets X and Y are denoted X —𝔾→ Y.
