open import Prelude.Init; open SetAsType
open L.Mem
open import Prelude.DecEq
open import Prelude.General
open import Prelude.Closures
open import Prelude.InferenceRules
open import Prelude.Decidable
open import Prelude.Setoid
open import Prelude.Bifunctor
open import Prelude.Measurable
open import Prelude.Ord
open import Prelude.InfEnumerable

-- ** α-equivalence.
module ULC.Alpha (Atom : Type) ⦃ _ : DecEq Atom ⦄ ⦃ _ : Enumerable∞ Atom ⦄ where

open import ULC.Base    Atom ⦃ it ⦄
open import ULC.Measure Atom ⦃ it ⦄
open import Nominal     Atom

private variable A : Type ℓ; f g h : Abs A

-- T0D0: factor out abstractions, deal with them generically
data _≡α_ : Term → Term → Type₀ where

  ν≈ :
    x ≈ y
    ──────────
    ` x ≡α ` y

  ξ≡ :
    ∙ L ≡α L′
    ∙ M ≡α M′
      ────────────────────
      (L · M) ≡α (L′ · M′)

  ζ≡_ : ∀ {f g : Abs Term} →
    -- f ≗α g
    И (λ 𝕩 → conc f 𝕩 ≡α conc g 𝕩)
    ──────────────────────────────
    (ƛ f) ≡α (ƛ g)

_≢α_ = ¬_ ∘₂ _≡α_

pattern ν≡ = ν≈ refl

instance
  Setoid-Term : ISetoid Term
  Setoid-Term = λ where
    .relℓ → 0ℓ
    ._≈_  → _≡α_

_≗α_ : Rel₀ (Abs Term)
f ≗α g = И (λ 𝕩 → conc f 𝕩 ≡α conc g 𝕩)

data _≡α⊎_ : Rel₀ (Term ⊎ Abs Term) where
  ≡_ :
    t ≡α t′
    ──────────────────
    inj₁ t ≡α⊎ inj₁ t′

  ≗_ : ∀ {f g} →
    f ≗α g
    ─────────────────
    inj₂ f ≡α⊎ inj₂ g

≡˘_ : inj₁ t ≡α⊎ inj₁ t′ → t ≡α t′
≡˘ (≡ p) = p

≗˘_ : ∀ {f g} → inj₂ f ≡α⊎ inj₂ g → f ≗α g
≗˘ (≗ p) = p

≡α⊎-refl : ∀ x → x ≡α⊎ x
≡α⊎-refl = ≺-rec _ go
  where
    go : ∀ x → (∀ y → y ≺ x → y ≡α⊎ y) → x ≡α⊎ x
    go x rec with x
    ... | inj₁ (` _)   = ≡ ν≡
    ... | inj₁ (l · m) = ≡ ξ≡ (≡˘ rec _ (l ·≺ˡ m)) (≡˘ rec _ (l ·≺ʳ m))
    ... | inj₁ (ƛ f)   = ≡ ζ≡ ≗˘ go (inj₂ f) rec
    ... | inj₂ f       = ≗ ([] , (λ y _ → ≡˘ rec _ (conc≺ f y)))

≡α-refl : ∀ t → t ≡α t
≡α-refl t = ≡˘ ≡α⊎-refl (inj₁ t)

≗α-refl : ∀ f → f ≗α f
≗α-refl f = ≗˘ ≡α⊎-refl (inj₂ f)

≡α⊎-sym : ∀ x y → x ≡α⊎ y → y ≡α⊎ x
≡α⊎-sym = ≺-rec _ go
  where
    go : ∀ x → (∀ y → y ≺ x → (∀ z → y ≡α⊎ z → z ≡α⊎ y))
             → (∀ y → x ≡α⊎ y → y ≡α⊎ x)
    go x rec _ eq with x | eq
    ... | inj₁ (` _) | ≡ ν≡
        = ≡ ν≡
    ... | inj₁ (l · m) | ≡ ξ≡ p q
        = ≡ ξ≡ (≡˘ rec _ (l ·≺ˡ m) _ (≡ p)) (≡˘ rec _ (l ·≺ʳ m) _ (≡ q))
    ... | inj₁ (ƛ f) | ≡ ζ≡ p
        = ≡ ζ≡ ≗˘ go (inj₂ f) rec _ (≗ p)
    ... | inj₂ f | ≗ (xs , p)
        = ≗ (xs , λ y y∉ → ≡˘ rec _ (conc≺ f y) _ (≡ p y y∉))

≗α-sym : f ≗α g → g ≗α f
≗α-sym = ≗˘_ ∘ ≡α⊎-sym _ _ ∘ ≗_

≡α-sym : t ≡α t′ → t′ ≡α t
≡α-sym = ≡˘_ ∘ ≡α⊎-sym _ _ ∘ ≡_

mutual
  ≗α-trans : f ≗α g → g ≗α h → f ≗α h
  ≗α-trans (xs , f≈g) (ys , g≈h) =
    (xs ++ ys) , λ y y∉ → ≡α-trans (f≈g y (y∉ ∘ L.Mem.∈-++⁺ˡ)) (g≈h y (y∉ ∘ L.Mem.∈-++⁺ʳ xs))

  ≡α-trans : t ≡α t′ → t′ ≡α t″ → t ≡α t″
  ≡α-trans ν≡ q = q
  ≡α-trans (ξ≡ p₁ p₂) (ξ≡ q₁ q₂) = ξ≡ (≡α-trans p₁ q₁) (≡α-trans p₂ q₂)
  ≡α-trans (ζ≡ f≈g) (ζ≡ g≈h) = ζ≡ ≗α-trans f≈g g≈h

instance
  SetoidLaws-Term : SetoidLaws Term
  SetoidLaws-Term .isEquivalence = record {refl = ≡α-refl _; sym = ≡α-sym; trans = ≡α-trans}

  {-# TERMINATING #-}
  SwapLaws-Term : SwapLaws Term
  SwapLaws-Term .cong-swap = λ where
    ν≡       → ν≡
    (ξ≡ p q) → ξ≡ (cong-swap p) (cong-swap q)
    (ζ≡ f≈g) → ζ≡ (cong-swap f≈g)
  SwapLaws-Term .swap-id {a}{t} with t
  ... | ` x   = ν≈ swap-id
  ... | l · r = ξ≡ swap-id swap-id
  ... | ƛ f   = ζ≡ swap-id
  SwapLaws-Term .swap-rev {a}{b}{t} with t
  ... | ` x   = ν≈ swap-rev
  ... | l · r = ξ≡ swap-rev swap-rev
  ... | ƛ f   = ζ≡ swap-rev
  SwapLaws-Term .swap-sym {a}{b}{t} with t
  ... | ` x   = ν≈ swap-sym
  ... | l · r = ξ≡ swap-sym swap-sym
  ... | ƛ f   = ζ≡ swap-sym
  SwapLaws-Term .swap-swap {a}{b}{c}{d}{t} with t
  ... | ` x   = ν≈ swap-swap
  ... | l · r = ξ≡ swap-swap swap-swap
  ... | ƛ f   = ζ≡ swap-swap

  FinSupp-Term : FinitelySupported Term
  FinSupp-Term .∀fin = λ where
    (` x) → [ x ] , λ a b a∉ b∉ →
      ≈-reflexive $ cong `_ $
        swap-noop b a x λ where ♯0 → b∉ ♯0; ♯1 → a∉ ♯0
    (l · m) →
      let supˡ , pˡ = ∀fin l
          supᵐ , pᵐ = ∀fin m
      in (supˡ ++ supᵐ) , λ a b a∉ b∉ →
      ξ≡ (pˡ a b (a∉ ∘ ∈-++⁺ˡ) (b∉ ∘ ∈-++⁺ˡ))
         (pᵐ a b (a∉ ∘ ∈-++⁺ʳ _) (b∉ ∘ ∈-++⁺ʳ _))
    (ƛ x ⇒ t) → fin-ƛ t (∀fin t) x
     where
      cong-ƛ : t ≡α t′ → (ƛ x ⇒ t) ≡α (ƛ x ⇒ t′)
      cong-ƛ t≡ = ζ≡ ([] , λ _ _ → cong-swap t≡)

      fin-ƛ : ∀ (t : Term) → FinSupp t → (∀ x → FinSupp (ƛ x ⇒ t))
      fin-ƛ t (sup , p) x = x ∷ sup , λ a b a∉ b∉ →
        begin
          ⦅ b ↔ a ⦆ (ƛ x ⇒ t)
        ≡⟨⟩
          (ƛ ⦅ b ↔ a ⦆ x ⇒ ⦅ b ↔ a ⦆ t)
        ≡⟨ cong (λ ◆ → ƛ ◆ ⇒ ⦅ b ↔ a ⦆ t)
              $ swap-noop b a x (λ where ♯0 → b∉ ♯0; ♯1 → a∉ ♯0) ⟩
          (ƛ x ⇒ ⦅ b ↔ a ⦆ t)
        ≈⟨ cong-ƛ $ p a b (a∉ ∘ there) (b∉ ∘ there) ⟩
          (ƛ x ⇒ t)
        ∎ where open ≈-Reasoning

supp-var : supp (` x) ≡ [ x ]
supp-var = refl

supp-ξ : supp (L · M) ≡ supp L ++ supp M
supp-ξ = refl

supp-ƛ : supp (ƛ x ⇒ N) ≡ x ∷ supp N
supp-ƛ = refl

-- T0D0: this does not hold in the current setting I believe
postulate
  supp-abs⊆ : ∀ (t̂ : Abs Term) {a b} (a∉ : a ∉ supp t̂) (b∉ : b ∉ supp t̂) →
    (∀fin t̂ .proj₂ a b) a∉ b∉ .proj₁ ⊆ supp t̂
