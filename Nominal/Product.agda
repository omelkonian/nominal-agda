open import Prelude.Init; open SetAsType
open L.Mem
open import Prelude.Lists.Membership
open import Prelude.Lists.Dec
open import Prelude.General
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.InfEnumerable

module Nominal.Product (Atom : Type) ⦃ _ : DecEq Atom ⦄ where

open import Nominal.Swap Atom
open import Nominal.Support Atom

module _ {A : Type ℓ} {B : Type ℓ′} where

  open import Prelude.Setoid

  instance
    Setoid-× : ISetoid (A × B)
    Setoid-× = λ where
      .relℓ → _
      ._≈_ (a , b) (a′ , b′) → (a ≡ a′) × (b ≡ b′)

    SetoidLaws-× : SetoidLaws (A × B)
    SetoidLaws-× .isEquivalence = record
      { refl  = refl , refl
      ; sym   = λ (i , j) → sym i , sym j
      ; trans = λ (i , j) (k , l) → trans i k , trans j l
      }

  ext-× : _≈_ ⇒² _≡_ {A = A × B}
  ext-× (refl , refl) = refl

  ext-×˘ : _≡_ ⇒² _≈_ {A = A × B}
  ext-×˘ refl = refl , refl

module _ {A : Type ℓ} {B : Type ℓ′}
         ⦃ _ : Swap A ⦄ ⦃ _ : SwapLaws A ⦄
         ⦃ _ : Swap B ⦄ ⦃ _ : SwapLaws B ⦄ where

  instance
    SwapLaws-× : SwapLaws (A × B)
    SwapLaws-× = record
      { swap-id = ext-× $ swap-id , swap-id
      ; swap-rev = ext-× $ swap-rev , swap-rev
      ; swap-sym = ext-× $ swap-sym , swap-sym
      ; swap-swap = ext-× $ swap-swap , swap-swap
      }

  module _ ⦃ _ : Enumerable∞ Atom ⦄ where
    instance
      ∃FinSupp-× : ⦃ ∃FinitelySupported A ⦄
                 → ⦃ ∃FinitelySupported B ⦄
                 → ∃FinitelySupported (A × B)
      ∃FinSupp-× .∀∃fin (a , b) =
        let xs , p = ∀∃fin a
            ys , q = ∀∃fin b
        in xs ++ ys , λ y z y∉ z∉ → ext-×
          $ p y z (y∉ ∘ ∈-++⁺ˡ)   (z∉ ∘ ∈-++⁺ˡ)
          , q y z (y∉ ∘ ∈-++⁺ʳ _) (z∉ ∘ ∈-++⁺ʳ _)

      FinSupp-× : ⦃ FinitelySupported A ⦄
                → ⦃ FinitelySupported B ⦄
                → FinitelySupported (A × B)
      FinSupp-× .∀fin (a , b) =
        let xs , p , ¬p = ∀fin a
            ys , q , ¬q = ∀fin b
        in nub (xs ++ ys)
         , (λ y z y∉ z∉ → ext-×
              $ p y z (y∉ ∘ ∈-nub⁺ ∘ ∈-++⁺ˡ)   (z∉ ∘ ∈-nub⁺ ∘ ∈-++⁺ˡ)
              , q y z (y∉ ∘ ∈-nub⁺ ∘ ∈-++⁺ʳ xs) (z∉ ∘ ∈-nub⁺ ∘ ∈-++⁺ʳ xs)
           )
         , λ y z y∈′ z∉ pq →
           let z∉ˡ , z∉ʳ = ∉-++⁻ $ ∉-nub⁻ z∉
               p , q = ext-×˘ pq
           in case ∈-++⁻ xs $ ∈-nub⁻ y∈′ of λ where
             (inj₁ y∈) → ¬p y z y∈ z∉ˡ p
             (inj₂ y∈) → ¬q y z y∈ z∉ʳ q

private
  postulate
    𝕒 𝕓 : Atom
    𝕒≢𝕓 : 𝕒 ≢ 𝕓

  unquoteDecl Swap-Maybe = DERIVE Swap [ quote Maybe , Swap-Maybe ]

  justAtom : Atom × Maybe Atom
  justAtom = 𝕒 , just 𝕓

  justAtom′ : Atom × Maybe Atom
  justAtom′ = ⦅ 𝕒 ↔ 𝕓 ⦆ justAtom

  _ = justAtom .proj₁ ≡ 𝕒
    ∋ refl

  _ = justAtom .proj₂ ≡ just 𝕓
    ∋ refl

  _ : justAtom′ .proj₁ ≡ 𝕓
  _ rewrite dec-no (𝕒 ≟ 𝕓) 𝕒≢𝕓 .proj₂
          | ≟-refl 𝕒
          = refl

  _ : justAtom′ .proj₂ ≡ just 𝕒
  _ rewrite dec-no (𝕓 ≟ 𝕒) (≢-sym 𝕒≢𝕓) .proj₂
          | ≟-refl 𝕓
          = refl
