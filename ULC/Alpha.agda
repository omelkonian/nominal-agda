open import Prelude.Init
open SetAsType
open import Prelude.DecEq
open import Prelude.General
open import Prelude.Closures
open import Prelude.InferenceRules
open import Prelude.Decidable
open import Prelude.Membership
open import Prelude.Setoid
open import Prelude.Bifunctor
open import Prelude.Measurable
open import Prelude.Ord


-- ** α-equivalence.
module ULC.Alpha (Atom : Set) ⦃ _ : DecEq Atom ⦄ where

open import ULC.Base Atom ⦃ it ⦄
open import Nominal  Atom ⦃ it ⦄

private variable A : Type ℓ; f g h : Abs A

data _≡α_ : Term → Term → Type₀ where
  ν≡ :
    ──────────
    ` x ≡α ` x
  ζ≡_ : ∀ {f g : Abs Term} →
    -- f ≗α g
    И (λ 𝕩 → conc f 𝕩 ≡α conc g 𝕩)
    ──────────────────────────────
    (ƛ f) ≡α (ƛ g)
  ξ≡ :
    ∙ L ≡α L′
    ∙ M ≡α M′
      ────────────────────
      (L · M) ≡α (L′ · M′)
_≢α_ = ¬_ ∘₂ _≡α_

instance
  Setoid-Term : ISetoid Term
  Setoid-Term = λ where
    .relℓ → 0ℓ
    ._≈_  → _≡α_

_≗α_ : Rel₀ (Abs Term)
f ≗α g = И (λ 𝕩 → conc f 𝕩 ≡α conc g 𝕩)

instance
  Measurable-Term : Measurable Term
  Measurable-Term .∣_∣ t with t
  ... | ` _     = 1
  ... | l · m   = ∣ l ∣ + ∣ m ∣
  ... | ƛ _ ⇒ t = suc ∣ t ∣
  -- ... | ƛ _ ⇒  = ∣ f ∣

  Measurable-Abs : ⦃ Measurable A ⦄ → Measurable (Abs A)
  Measurable-Abs .∣_∣ f = suc ∣ f .term ∣

swap≡ : ∀ x y (t : Term) → ∣ swap x y t ∣ ≡ ∣ t ∣
swap≡ x y (` _) = refl
swap≡ x y (l · m) rewrite swap≡ x y l | swap≡ x y m = refl
swap≡ x y (ƛ z ⇒ t) = cong suc (swap≡ x y t)

conc≡ : ∀ (f : Abs Term) x → ∣ conc f x ∣ ≡ ∣ f .term ∣
conc≡ (abs x t) y = swap≡ y x t

conc≺ : ∀ (f : Abs Term) x → ∣ conc f x ∣ ≺ ∣ f ∣
conc≺ f x rewrite conc≡ f x = Nat.≤-refl

measure⁺ : ∀ (t : Term) → ∣ t ∣ > 0
measure⁺ (l · m) with ∣ l ∣ | measure⁺ l | ∣ m ∣ | measure⁺ m
... | suc l′ | _ | suc m′ | _ = s≤s z≤n
measure⁺ (` _)   = s≤s z≤n
measure⁺ (ƛ _)   = s≤s z≤n
_·≺ˡ_ : ∀ L M → L ≺ (L · M)
_ ·≺ˡ M = Nat.m<m+n _ (measure⁺ M)
_·≺ʳ_ : ∀ L M → M ≺ (L · M)
L ·≺ʳ _ = Nat.m<n+m _ (measure⁺ L)


X = Term ⊎ Abs Term

data _≡α⊎_ : Rel₀ X where
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
    go (inj₁ (` x)) rec   = ≡ ν≡
    go (inj₁ (l · m)) rec = ≡ (ξ≡ (≡˘ rec _ (l ·≺ˡ m)) (≡˘ rec _ (l ·≺ʳ m)))
    go (inj₁ (ƛ f)) rec   = ≡ ζ≡ ≗˘ go (inj₂ f) rec
    go (inj₂ f) rec       = ≗ ([] , (λ y _ → ≡˘ rec _ (conc≺ f y)))

≡α-refl : ∀ t → t ≡α t
≡α-refl t = ≡˘ ≡α⊎-refl (inj₁ t)

≗α-refl : ∀ f → f ≗α f
≗α-refl f = ≗˘ ≡α⊎-refl (inj₂ f)

≡α⊎-sym : ∀ x y → x ≡α⊎ y → y ≡α⊎ x
≡α⊎-sym = ≺-rec _ go
  where
    go : ∀ x → (∀ y → y ≺ x → (∀ z → y ≡α⊎ z → z ≡α⊎ y))
             → (∀ y → x ≡α⊎ y → y ≡α⊎ x)
    go (inj₁ (` _))   rec _
      (≡ ν≡) = ≡ ν≡
    go (inj₁ (l · m)) rec _
      (≡ ξ≡ p q) = ≡ (ξ≡ (≡˘ rec _ (l ·≺ˡ m) _ (≡ p)) (≡˘ rec _ (l ·≺ʳ m) _ (≡ q)))
    go (inj₁ (ƛ f))   rec _
      (≡ (ζ≡ p)) = ≡ (ζ≡ (≗˘ go (inj₂ f) rec _ (≗ p)))
    go (inj₂ f)       rec _
      (≗ (xs , p)) = ≗ (xs , λ y y∉ → ≡˘ rec _ (conc≺ f y) _ (≡ (p y y∉)))

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
  SetoidLaws-Term : Setoid-Laws Term
  SetoidLaws-Term .isEquivalence = record
    { refl = ≡α-refl _ ; sym = ≡α-sym ; trans = ≡α-trans }

-- Equivariant _~_ = x ~ y → swap a b x ~ swap a b y
