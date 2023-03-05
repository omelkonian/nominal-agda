open import Prelude.Init; open SetAsType
open L.Mem
open import Prelude.DecEq
open import Prelude.Setoid
open import Prelude.InfEnumerable
open import Prelude.InferenceRules

module Nominal.MinSupport (Atom : Type) ⦃ _ : DecEq Atom ⦄ ⦃ _ : Enumerable∞ Atom ⦄ where

open import Nominal.New  Atom
open import Nominal.Swap Atom

private variable A : Type ℓ; B : Type ℓ′

module _ ⦃ _ : Swap A ⦄ ⦃ _ : ISetoid A ⦄ where

  MinFinSupp : Pred A _
  MinFinSupp a = ∃ λ (xs : Atoms) →
    (∀ x y → x ∉ xs → y ∉ xs → swap y x a ≈ a)
    ×
    (∀ x y → x ∈ xs → y ∉ xs → swap y x a ≉ a)

  -- alternative definition of equivariance based on (finite) support
  --  * equivariant(x) := supp(x) = ∅
  MinEquivariant′ : Pred A _
  MinEquivariant′ x = ∃ λ (fin-x : MinFinSupp x) → fin-x .proj₁ ≡ []

record MinFinitelySupported (A : Type ℓ)
  ⦃ _ : ISetoid A ⦄ ⦃ _ : SetoidLaws A ⦄
  ⦃ _ : Swap A ⦄ ⦃ _ : SwapLaws A ⦄ : Typeω
  where

  field ∀minFin : Unary.Universal MinFinSupp

  minSupp : A → Atoms
  minSupp = proj₁ ∘ ∀minFin

  _∙minSupp = minSupp

  fresh∉-min : (a : A) → ∃ (_∉ minSupp a)
  fresh∉-min = minFresh ∘ minSupp
  -- NB: optimized fresh that generates the *least* element

  fresh-var-min : A → Atom
  fresh-var-min = proj₁ ∘ fresh∉-min

  swap-fresh-min : ∀ {𝕒 𝕓} (x : A) →
    ∙ 𝕒 ∉ minSupp x
    ∙ 𝕓 ∉ minSupp x
      ────────────────
      ⦅ 𝕒 ↔ 𝕓 ⦆ x ≈ x
  swap-fresh-min x = flip (∀minFin x .proj₂ .proj₁ _ _)

open MinFinitelySupported ⦃...⦄ public

instance
  MinFinSupp-Atom : MinFinitelySupported Atom
  MinFinSupp-Atom .∀minFin 𝕒 = [ 𝕒 ] , eq , ¬eq
    where
      eq : ∀ x y → x ∉ [ 𝕒 ] → y ∉ [ 𝕒 ] → swap y x 𝕒 ≈ 𝕒
      eq _ _ x∉ y∉ = swap-noop _ _ _ λ where 𝟘 → y∉ 𝟘; 𝟙 → x∉ 𝟘

      ¬eq : ∀ x y → x ∈ [ 𝕒 ] → y ∉ [ 𝕒 ] → swap y x 𝕒 ≉ 𝕒
      ¬eq _ y 𝟘 y∉
        rewrite ≟-refl 𝕒 | ≟-refl y
        with 𝕒 ≟ y
      ... | yes refl = ⊥-elim $ y∉ 𝟘
      ... | no y≢    = ≢-sym y≢


-- T0D0: generalize this to more complex types than Atom (c.f. supp-swap above)
minSupp-swap-atom : ∀ {𝕒 𝕓} (t : Atom) → minSupp (swap 𝕒 𝕓 t) ⊆ 𝕒 ∷ 𝕓 ∷ t ∷ []
minSupp-swap-atom {a}{b} t
  with t ≟ a
... | yes refl = λ where 𝟘 → 𝟙
... | no _
  with t ≟ b
... | yes refl = λ where 𝟘 → 𝟘
... | no _     = λ where 𝟘 → 𝟚
