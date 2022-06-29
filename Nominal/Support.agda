open import Prelude.Init
open SetAsType
open L.Mem
open import Prelude.DecEq
open import Prelude.Setoid
open import Prelude.InfEnumerable

module Nominal.Support (Atom : Type) ⦃ _ : DecEq Atom ⦄ ⦃ _ : Enumerable∞ Atom ⦄ where

open import Nominal.Swap Atom
open import Nominal.Abs  Atom

private variable A : Type ℓ

module _ ⦃ _ : Swap A ⦄ ⦃ _ : ISetoid A ⦄ where

  infix 4 _♯_
  _♯_ : Atom → A → Type _
  𝕒 ♯ x = И λ 𝕓 → swap 𝕓 𝕒 x ≈ x

  FinSupp : Pred A _
  FinSupp x = И² λ 𝕒 𝕓 → swap 𝕓 𝕒 x ≈ x

record FinitelySupported (A : Type ℓ)
  ⦃ ls : Lawful-Setoid A ⦄ ⦃ _ : Lawful-Swap A ⦃ ls ⦄ ⦄ : Setω where

  field ∀fin : Unary.Universal FinSupp

  supp : A → Atoms
  supp = proj₁ ∘ ∀fin

  _∙supp = supp

  -- T0D0: extract minimal support
  --   i.e. filter out elements of `supp` that already satisfy P
  -- module _ ⦃ _ : IDecSetoid A ⦄ where
  --   minSupp : A → Atoms
  --   minSupp a =
  --     let xs , P = ∀fin a
  --     in  filter ? xs
  --     ?
  -- NB: doesn't hold in general ⇒ leads to a solution to the halting problem
  -- T0D0: find a characterization of this decidable sub-space

  fresh∉ : (a : A) → ∃ (_∉ supp a)
  fresh∉ = fresh ∘ supp
  -- T0D0: optimize fresh to generates the *least* element (not `1 + ∑ support`)

  fresh-var : A → Atom
  fresh-var = proj₁ ∘ fresh∉

  ∃fresh : ∀ (x : A) → ∃ λ 𝕒 → ∃ λ 𝕓 →
      (𝕒 ♯ x)
    × (𝕓 ♯ x)
    × (swap 𝕓 𝕒 x ≈ x)
  ∃fresh x =
    let xs , swap≈ = ∀fin x
        -- ((a ∷ b ∷ []) , (a∉ V.All.∷ b∉ V.All.∷ V.All.[])) = (fresh^ 2) xs
        a , a∉ = fresh xs
        b , b∉ = fresh xs

        p : a ♯ x
        p = xs , λ y y∉ → swap≈ a y a∉ y∉

        q : b ♯ x
        q = xs , λ y y∉ → swap≈ b y b∉ y∉

    in a , b , p , q , swap≈ a b a∉ b∉

  -- T0D0: meta-programming tactic `fresh-in-context` (big sister to `deriveSwap`)
  -- NB: these tactics correspond to two fundamental axioms/notions in nominal sets
  -- (c.f. EZFA)

open FinitelySupported ⦃...⦄ public

module _ ⦃ ls : Lawful-Setoid A ⦄ ⦃ lsw : Lawful-Swap A ⦃ ls ⦄ ⦄ where

  -- abstractions over finitely supported types are themselves finite
  instance
    FinSupp-abs : ⦃ FinitelySupported A ⦃ ls ⦄ ⦃ lsw ⦄ ⦄ → FinitelySupported (Abs A)
    FinSupp-abs .∀fin (abs x t) =
      let xs , p = ∀fin t
      in x ∷ xs , λ y z y∉ z∉ →
      begin
        ⦅ z ↔ y ⦆ (abs x t)
      ≡⟨⟩
        -- ⦅ 𝕒 ↔ 𝕓 ⦆ (f 𝕔) ≈ (⦅ 𝕒 ↔ 𝕓 ⦆ f) (⦅ 𝕒 ↔ 𝕓 ⦆ 𝕔)
        abs (⦅ z ↔ y ⦆ x) (⦅ z ↔ y ⦆ t)
      ≡⟨ cong (λ ◆ → abs ◆ (⦅ z ↔ y ⦆ t))
            $ swap-noop z y x (λ where ♯0 → z∉ ♯0; ♯1 → y∉ ♯0) ⟩
        abs x (⦅ z ↔ y ⦆ t)
      ≈⟨ cong-abs $ p y z (y∉ ∘ there) (z∉ ∘ there) ⟩
        abs x t
      ∎ where open ≈-Reasoning

  module _ ⦃ _ : FinitelySupported A ⦄ where
    -- Two ways to fix functoriality:
      -- 1. require that (f : A → A) is equivariant
    --   2. ...or that it at least has finite support
    mapAbs : Op₁ A → Op₁ (Abs A)
        -- ≈ (A → A) → (Abs A → Abs A)
    -- T0D0: In order to resolve termination issues (via well-founded recursion),
    -- we need a more restrainted version of mapAbs with type:
    -- mapAbs : (x' : Abs A) → (f : (a : A) → a ≺ f → A) → Abs A
    -- NB: a generalisation would be to say that the size behaviour of
    --     `mapAbs f` corresponds to that of `f`
    mapAbs f x' =
      let a = fresh-var x' -- T0D0: ++ supp?? f
      in abs a (f $ conc x' a)

    freshen : Op₁ (Abs A)
    freshen f@(abs a t) =
      let xs , _ = ∀fin f
          b , b∉ = fresh xs
      in abs b (conc f b)

private

  private variable B : Type ℓ′

  instance
    Setoid-→ : ISetoid (A → B)
    Setoid-→ = λ where
      .relℓ → _
      ._≈_  → _≗_

    SetoidLaws-→ : Setoid-Laws (A → B)
    SetoidLaws-→ {A = A} {B = B} .isEquivalence = Setoid.isEquivalence (A PropEq.→-setoid B)

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

  _ = finF .proj₁ ≡ suppF
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
