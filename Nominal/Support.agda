open import Prelude.Init; open SetAsType
open L.Mem
open import Prelude.DecEq
open import Prelude.InfEnumerable
open import Prelude.InferenceRules

module Nominal.Support (Atom : Type) ⦃ _ : DecEq Atom ⦄ ⦃ _ : Enumerable∞ Atom ⦄ where

open import Nominal.New  Atom
open import Nominal.Swap Atom

freshAtom : Atoms → Atom
freshAtom = proj₁ ∘ minFresh

freshAtom∉ : ∀ {xs : Atoms} → freshAtom xs ∉ xs
freshAtom∉ {xs} = minFresh xs .proj₂

private variable A : Type ℓ; B : Type ℓ′

module _ ⦃ _ : Swap A ⦄ where

  ∃FinSupp FinSupp ∃Equivariant′ Equivariant′ : Pred A _

  -- NB: this is an over-approximation!
  -- e.g. ∃supp (ƛ x ⇒ x) = {x}
  ∃FinSupp x = И² λ 𝕒 𝕓 → swap 𝕓 𝕒 x ≡ x

  -- ** a proper notion of support
  -- e.g. in λ-calculus this would correspond to the free variables of a term
  FinSupp a = ∃ λ (xs : Atoms) →
    (∀ x y → x ∉ xs → y ∉ xs → swap y x a ≡ a)
    ×
    (∀ x y → x ∈ xs → y ∉ xs → swap y x a ≢ a)

  -- alternative definition of equivariance based on (finite) support
  --  * equivariant(x) := supp(x) = ∅
  ∃Equivariant′ x = ∃ λ (fin-x : ∃FinSupp x) → fin-x .proj₁ ≡ []
  Equivariant′  x = ∃ λ (fin-x : FinSupp x)  → fin-x .proj₁ ≡ []

-- counter-example: a function with infinite support
-- e.g. λ x → (x == 𝕒) ∨ (x == 𝕓)

record ∃FinitelySupported (A : Type ℓ) ⦃ _ : Swap A ⦄ ⦃ _ : SwapLaws A ⦄ : Typeω where

  field ∀∃fin : Unary.Universal ∃FinSupp

  ∃supp : A → Atoms
  ∃supp = proj₁ ∘ ∀∃fin

  _∙∃supp = ∃supp

  ∃fresh∉ : (a : A) → ∃ (_∉ ∃supp a)
  ∃fresh∉ = minFresh ∘ ∃supp
  -- NB: optimized fresh that generates the *least* element

  ∃fresh-var : A → Atom
  ∃fresh-var = proj₁ ∘ ∃fresh∉

  swap-∃fresh : ∀ {𝕒 𝕓} (x : A) →
    ∙ 𝕒 ∉ ∃supp x
    ∙ 𝕓 ∉ ∃supp x
      ────────────────
      ⦅ 𝕒 ↔ 𝕓 ⦆ x ≡ x
  swap-∃fresh x = flip (∀∃fin x .proj₂ _ _)

{-
  supp-swap : ∀ {𝕒 𝕓} (t : A) → supp (swap 𝕒 𝕓 t) ⊆ 𝕒 ∷ 𝕓 ∷ t ∷ []
  -- ≡ swap 𝕒 𝕓 (supp t) -- [swap 𝕒 𝕓 x₁, swap 𝕒 𝕓 x₂, ...]
  supp-swap {x}{a}{b} x∉ = ?

  swap-∉ : ∀ {x 𝕒 𝕓} (t : A) → x ∉ supp t → swap 𝕒 𝕓 x ∉ supp (swap 𝕒 𝕓 t)
  -- T0D0: add hypothesis `x ∉ [a, b]`
  swap-∉ {x}{a}{b} x∉
    with x ≟ a
  ... | yes refl
    -- b ∉ supp (swap a b t)
    = ?
  ... | no x≢a
    with x ≟ b
  ... | yes refl
    -- a ∉ supp (swap a b t)
    = ?
  ... | no x≢b
    -- x ∉ supp (swap a b t)
    = ?
-}
open ∃FinitelySupported ⦃...⦄ public

instance
  ∃FinSupp-Atom : ∃FinitelySupported Atom
  ∃FinSupp-Atom .∀∃fin 𝕒 = [ 𝕒 ] , λ _ _ y∉ z∉ →
    swap-noop _ _ _ λ where 𝟘 → z∉ 𝟘; 𝟙 → y∉ 𝟘

-- T0D0: generalize this to more complex types than Atom (c.f. supp-swap above)
∃supp-swap-atom : ∀ {𝕒 𝕓} (t : Atom) → ∃supp (swap 𝕒 𝕓 t) ⊆ 𝕒 ∷ 𝕓 ∷ t ∷ []
-- supp (swap 𝕒 𝕓 t) ≡ swap 𝕒 𝕓 (supp t)
∃supp-swap-atom {a}{b} t
  with t ≟ a
... | yes refl = λ where 𝟘 → 𝟙
... | no _
  with t ≟ b
... | yes refl = λ where 𝟘 → 𝟘
... | no _     = λ where 𝟘 → 𝟚

record FinitelySupported (A : Type ℓ) ⦃ _ : Swap A ⦄ ⦃ _ : SwapLaws A ⦄ : Typeω where

  field ∀fin : Unary.Universal FinSupp

  supp : A → Atoms
  supp = proj₁ ∘ ∀fin

  _∙supp = supp

  infix 4 _♯_
  _♯_ : Atom → A → Type _
  𝕒 ♯ x = 𝕒 ∉ supp x

  fresh∉-min : (a : A) → ∃ (_∉ supp a)
  fresh∉-min = fresh ∘ supp
  -- NB: optimized fresh that generates the *least* element

  fresh-var-min : A → Atom
  fresh-var-min = proj₁ ∘ fresh∉-min

  swap-fresh-min : ∀ {𝕒 𝕓} (x : A) →
    ∙ 𝕒 ∉ supp x
    ∙ 𝕓 ∉ supp x
      ────────────────
      ⦅ 𝕒 ↔ 𝕓 ⦆ x ≡ x
  swap-fresh-min x = flip (∀fin x .proj₂ .proj₁ _ _)

  ∃fresh : ∀ (x : A) → ∃ λ 𝕒 → ∃ λ 𝕓 →
      (𝕒 ♯ x)
    × (𝕓 ♯ x)
    × (swap 𝕓 𝕒 x ≡ x)
  ∃fresh x =
    let xs , swap≡ , swap≢ = ∀fin x
        -- (a ∷ b ∷ [] , a∉ ∷ b∉ ∷ []) = (fresh^ 2) xs
        a , a∉ = minFresh xs
        b , b∉ = minFresh xs
    in a , b , a∉ , b∉ , swap≡ a b a∉ b∉

  -- T0D0: meta-programming tactic `fresh-in-context` (big sister to `deriveSwap`)
  -- NB: these tactics correspond to two fundamental axioms/notions in nominal sets
  -- (c.f. EZFA)

open FinitelySupported ⦃...⦄ public

instance
  FinSupp-Atom : FinitelySupported Atom
  FinSupp-Atom .∀fin 𝕒 = [ 𝕒 ] , eq , ¬eq
    where
      eq : ∀ x y → x ∉ [ 𝕒 ] → y ∉ [ 𝕒 ] → swap y x 𝕒 ≡ 𝕒
      eq _ _ x∉ y∉ = swap-noop _ _ _ λ where 𝟘 → y∉ 𝟘; 𝟙 → x∉ 𝟘

      ¬eq : ∀ x y → x ∈ [ 𝕒 ] → y ∉ [ 𝕒 ] → swap y x 𝕒 ≢ 𝕒
      ¬eq _ y 𝟘 y∉
        rewrite ≟-refl 𝕒 | ≟-refl y
        with 𝕒 ≟ y
      ... | yes refl = ⊥-elim $ y∉ 𝟘
      ... | no y≢    = ≢-sym y≢


-- T0D0: generalize this to more complex types than Atom (c.f. supp-swap above)
supp-swap-atom : ∀ {𝕒 𝕓} (t : Atom) → supp (swap 𝕒 𝕓 t) ⊆ 𝕒 ∷ 𝕓 ∷ t ∷ []
supp-swap-atom {a}{b} t
  with t ≟ a
... | yes refl = λ where 𝟘 → 𝟙
... | no _
  with t ≟ b
... | yes refl = λ where 𝟘 → 𝟘
... | no _     = λ where 𝟘 → 𝟚
