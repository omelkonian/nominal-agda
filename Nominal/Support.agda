open import Prelude.Init; open SetAsType
open L.Mem
open import Prelude.DecEq
open import Prelude.Setoid
open import Prelude.InfEnumerable
open import Prelude.InferenceRules

module Nominal.Support (Atom : Type) ⦃ _ : DecEq Atom ⦄ ⦃ _ : Enumerable∞ Atom ⦄ where

open import Nominal.New  Atom
open import Nominal.Swap Atom

private variable A : Type ℓ; B : Type ℓ′

module _ ⦃ _ : Swap A ⦄ ⦃ _ : ISetoid A ⦄ where

  infix 4 _♯_
  _♯_ : Atom → A → Type _
  𝕒 ♯ x = И λ 𝕓 → swap 𝕓 𝕒 x ≈ x

  FinSupp : Pred A _
  FinSupp x = И² λ 𝕒 𝕓 → swap 𝕓 𝕒 x ≈ x

  -- alternative definition of equivariance based on (finite) support
  --  * equivariant(x) := supp(x) = ∅
  Equivariant′ : Pred A _
  Equivariant′ x = ∃ λ (fin-x : FinSupp x) → fin-x .proj₁ ≡ []

  MinSupp : Pred (List Atom × A) _
  MinSupp (xs , a) =
    (∀ x y → x ∉ xs → y ∉ xs → swap x y a ≈ a)
    ×
    (∀ x y → x ∈ xs → y ∉ xs → swap x y a ≉ a)

  -- И⅁ λ 𝕒 𝕓 → swap 𝕓 𝕒 x ≉ x

  MinFinSupp : ∀ {a : A} → Pred (FinSupp a) _
  MinFinSupp {a = a} (xs , p) =
    -- MinSupp (xs , a)
    (∀ x y → x ∈ xs → y ∉ xs → swap x y a ≉ a)

-- counter-example
-- λ x → (x == 𝕒) ∨ (x == 𝕓)

record FinitelySupported (A : Type ℓ)
  ⦃ _ : ISetoid A ⦄ ⦃ _ : Setoid-Laws A ⦄
  ⦃ _ : Swap A ⦄ ⦃ _ : SwapLaws A ⦄ : Typeω
  where

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
  fresh∉ = minFresh ∘ supp
  -- NB: optimized fresh that generates the *least* element

  fresh-var : A → Atom
  fresh-var = proj₁ ∘ fresh∉

  ∃fresh : ∀ (x : A) → ∃ λ 𝕒 → ∃ λ 𝕓 →
      (𝕒 ♯ x)
    × (𝕓 ♯ x)
    × (swap 𝕓 𝕒 x ≈ x)
  ∃fresh x =
    let xs , swap≈ = ∀fin x
        -- ((a ∷ b ∷ []) , (a∉ V.All.∷ b∉ V.All.∷ V.All.[])) = (fresh^ 2) xs
        a , a∉ = minFresh xs
        b , b∉ = minFresh xs

        p : a ♯ x
        p = xs , λ y y∉ → swap≈ a y a∉ y∉

        q : b ♯ x
        q = xs , λ y y∉ → swap≈ b y b∉ y∉

    in a , b , p , q , swap≈ a b a∉ b∉

  -- T0D0: meta-programming tactic `fresh-in-context` (big sister to `deriveSwap`)
  -- NB: these tactics correspond to two fundamental axioms/notions in nominal sets
  -- (c.f. EZFA)
open FinitelySupported ⦃...⦄ public

instance
  FinSupp-Atom : FinitelySupported Atom
  FinSupp-Atom .∀fin 𝕒 = [ 𝕒 ] , λ _ _ y∉ z∉ →
    swap-noop _ _ _ λ where ♯0 → z∉ ♯0; ♯1 → y∉ ♯0
