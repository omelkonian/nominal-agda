open import Prelude.Init
open SetAsType
open L.Mem
open import Prelude.DecEq
open import Prelude.Setoid
open import Prelude.InfEnumerable

module Nominal.Support (Atom : Type) ⦃ _ : DecEq Atom ⦄ where

open import Nominal.Swap Atom ⦃ it ⦄
open import Nominal.Abs  Atom ⦃ it ⦄

private variable
  a b : Level
  A : Type a
  B : Type b

instance
  Setoid-→ : ISetoid (A → B)
  Setoid-→ = λ where
    .relℓ → _
    ._≈_  → _≗_

  SetoidLaws-→ : Setoid-Laws (A → B)
  SetoidLaws-→ {A = A} {B = B} .isEquivalence = Setoid.isEquivalence (A PropEq.→-setoid B)

module _ ⦃ _ : Swap A ⦄ ⦃ ls : Lawful-Setoid A ⦄ where
  FinSupp : Pred A _
  FinSupp x = И² λ 𝕒 𝕓 → swap 𝕓 𝕒 x ≈ x

  ∀FinSupp = Unary.Universal FinSupp

  supp : ∀ x → FinSupp x → List Atom
  supp _ = proj₁

  infix 4 _♯_
  _♯_ : Atom → A → Type _
  𝕒 ♯ x = И λ 𝕓 → swap 𝕓 𝕒 x ≈ x

  module _ ⦃ _ : Enumerable∞ Atom ⦄ (x : A) (finX : FinSupp x) where

    ∃fresh : ∃ λ 𝕒 → ∃ λ 𝕓
      → (𝕒 ♯ x)
      × (𝕓 ♯ x)
      × (swap 𝕓 𝕒 x ≈ x)
    ∃fresh =
      let xs , swap≈ = finX
          -- ((a ∷ b ∷ []) , (a∉ V.All.∷ b∉ V.All.∷ V.All.[])) = (fresh^ 2) xs
          a , a∉ = fresh xs
          b , b∉ = fresh xs

          p : a ♯ x
          p = xs , λ y y∉ → swap≈ a y a∉ y∉

          q : b ♯ x
          q = xs , λ y y∉ → swap≈ b y b∉ y∉

      in a , b , p , q , swap≈ a b a∉ b∉

module _ {A : Type ℓ} ⦃ ls : Lawful-Setoid A ⦄ ⦃ _ : Lawful-Swap A ⦃ ls ⦄ ⦄ where
  -- abstractions over finitely supported types are themselves finitely
  ∀FinSupp-Abs : ∀FinSupp {A = A} ⦃ ls = ls ⦄ → ∀FinSupp {A = Abs A}
  ∀FinSupp-Abs fin (abs x t) =
    let xs , p = fin t
    in x ∷ xs , λ y z y∉ z∉ →
    begin
      ⦅ z ↔ y ⦆ (abs x t)
    ≡⟨⟩
      abs (⦅ z ↔ y ⦆ x) (⦅ z ↔ y ⦆ t)
    ≡⟨ cong (λ ◆ → abs ◆ (⦅ z ↔ y ⦆ t))
          $ swap-noop z y x (λ where ♯0 → z∉ ♯0; ♯1 → y∉ ♯0) ⟩
      abs x (⦅ z ↔ y ⦆ t)
    ≈⟨ cong-abs $ p y z (y∉ ∘ there) (z∉ ∘ there) ⟩
      abs x t
    ∎ where open ≈-Reasoning

private

  postulate x y : Atom

  f : Atom → Bool
  f z = (z == x) ∨ (z == y)
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
