open import Prelude.Init; open SetAsType
open L.Mem
open import Prelude.DecEq
open import Prelude.General
open import Prelude.Closures
open import Prelude.InferenceRules
open import Prelude.Decidable
open import Prelude.Bifunctor
open import Prelude.Measurable
open import Prelude.Ord
open import Prelude.InfEnumerable
open import Prelude.Lists.Dec

-- ** α-equivalence.
module ULC.Alpha (Atom : Type) ⦃ _ : DecEq Atom ⦄ ⦃ _ : Enumerable∞ Atom ⦄ where

open import ULC.Base    Atom ⦃ it ⦄
open import ULC.Measure Atom ⦃ it ⦄
open import Nominal     Atom

private variable A : Type ℓ; f g h : Abs A

data _≡α_ : Term → Term → Type₀ where

  ν≡ :
    ──────────
    ` x ≡α ` x

  ξ≡ :
    ∙ L ≡α L′
    ∙ M ≡α M′
      ────────────────────
      (L · M) ≡α (L′ · M′)

  ζ≡_ :
    t̂ ≗α t̂′
    ───────────────
    (ƛ t̂) ≡α (ƛ t̂′)

_≢α_ = ¬_ ∘₂ _≡α_

ν≈ : x ≡ y → ` x ≡α ` y
ν≈ refl = ν≡

-- ** extensionality principle for α-equivalence of λ-terms
extˡ : _≡α_ ⇒² _≡_
extˡ = λ where
  ν≡ → refl
  (ξ≡ p q) → cong₂ _·_ (extˡ p) (extˡ q)
  (ζ≡ p) → cong ƛ_ (extᵃ p)

-- ** INCONSISTENT!!
absurd : ∀ {𝕒 𝕓 : Atom} → 𝕒 ≢ 𝕓 → ⊥
absurd {𝕒}{𝕓} 𝕒≢𝕓 = ¬eq (extˡ $ ζ≡ (-, eq))
  where
    ¬eq : (ƛ 𝕒 ⇒ ` 𝕒) ≢ (ƛ 𝕓 ⇒ ` 𝕓)
    ¬eq refl = 𝕒≢𝕓 refl

    eq : ∀ x → x ∉ 𝕒 ∷ 𝕓 ∷ [] → conc (abs 𝕒 $ ` 𝕒) x ≡ conc (abs 𝕓 $ ` 𝕓) x
    eq x x∉ rewrite swapʳ x 𝕒 | swapʳ x 𝕓 = refl

open ≡-Reasoning

instance
  ∃FinSupp-Term : ∃FinitelySupported Term
  ∃FinSupp-Term .∀∃fin = λ where
    (` x) → [ x ] , λ a b a∉ b∉ →
      cong `_ $ swap-noop b a x λ where 𝟘 → b∉ 𝟘; 𝟙 → a∉ 𝟘
    (l · m) →
      let supˡ , pˡ = ∀∃fin l
          supᵐ , pᵐ = ∀∃fin m
      in (supˡ ++ supᵐ) , λ a b a∉ b∉ →
      cong₂ _·_ (pˡ a b (a∉ ∘ ∈-++⁺ˡ) (b∉ ∘ ∈-++⁺ˡ))
                (pᵐ a b (a∉ ∘ ∈-++⁺ʳ _) (b∉ ∘ ∈-++⁺ʳ _))
    (ƛ x ⇒ t) → fin-ƛ t (∀∃fin t) x
     where
      fin-ƛ : ∀ (t : Term) → ∃FinSupp t → (∀ x → ∃FinSupp (ƛ x ⇒ t))
      fin-ƛ t (sup , p) x = x ∷ sup , λ a b a∉ b∉ →
        begin
          ⦅ b ↔ a ⦆ (ƛ x ⇒ t)
        ≡⟨⟩
          (ƛ ⦅ b ↔ a ⦆ x ⇒ ⦅ b ↔ a ⦆ t)
        ≡⟨ cong (λ ◆ → ƛ ◆ ⇒ ⦅ b ↔ a ⦆ t)
              $ swap-noop b a x (λ where 𝟘 → b∉ 𝟘; 𝟙 → a∉ 𝟘) ⟩
          (ƛ x ⇒ ⦅ b ↔ a ⦆ t)
        ≡⟨ cong (ƛ x ⇒_) $ p a b (a∉ ∘ there) (b∉ ∘ there) ⟩
          (ƛ x ⇒ t)
        ∎

  FinSupp-Term : FinitelySupported Term
  FinSupp-Term .∀fin (` x) = xs , eq , ¬eq
    where
      xs = [ x ]

      eq : ∀ a b → a ∉ xs → b ∉ xs → swap b a (` x) ≡ ` x
      eq a b a∉ b∉ = cong `_ $ swap-noop b a x λ where 𝟘 → b∉ 𝟘; 𝟙 → a∉ 𝟘

      ¬eq : ∀ a b → a ∈ xs → b ∉ xs → swap b a (` x) ≢ ` x
      ¬eq a b 𝟘 b∉ rewrite swapʳ b a = λ where refl → b∉ 𝟘

  FinSupp-Term .∀fin (l · m)
    with supˡ , pˡ , ¬pˡ ← ∀fin l
    with supᵐ , pᵐ , ¬pᵐ ← ∀fin m
    = xs , eq , ¬eq -- same as Nominal.Product
    where
      xs = nub (supˡ ++ supᵐ)

      eq : ∀ a b → a ∉ xs → b ∉ xs → swap b a (l · m) ≡ l · m
      eq a b a∉ b∉ =
        cong₂ _·_ (pˡ a b (a∉ ∘ ∈-nub⁺ ∘ ∈-++⁺ˡ)      (b∉ ∘ ∈-nub⁺ ∘ ∈-++⁺ˡ))
                  (pᵐ a b (a∉ ∘ ∈-nub⁺ ∘ ∈-++⁺ʳ supˡ) (b∉ ∘ ∈-nub⁺ ∘ ∈-++⁺ʳ supˡ))

      -- TODO: should not hold, argument might remain unused
      -- *WRONG* the problem only arises when considering _normal forms_
      postulate ¬eq : ∀ a b → a ∈ xs → b ∉ xs → swap b a (l · m) ≢ l · m
  FinSupp-Term .∀fin t̂@(ƛ x ⇒ t)
    with xs , p , ¬p ← ∀fin t
    = xs′ , eq , ¬eq -- same as Nominal.Abs
    where
      xs′ = filter (¬? ∘ (_≟ x)) xs
      -- TODO: both should be provable
      postulate
        eq  : ∀ y z → y ∉ xs′ → z ∉ xs′ → swap z y t̂ ≡ t̂
        ¬eq : ∀ y z → y ∈ xs′ → z ∉ xs′ → swap z y t̂ ≢ t̂

∃supp-var : ∃supp (` x) ≡ [ x ]
∃supp-var = refl

supp-var : supp (` x) ≡ [ x ]
supp-var = refl

∃supp-ξ : ∃supp (L · M) ≡ ∃supp L ++ ∃supp M
∃supp-ξ = refl

supp-ξ : supp (L · M) ≡ nub (supp L ++ supp M)
supp-ξ = refl

∃supp-ƛ : ∃supp (ƛ x ⇒ N) ≡ x ∷ ∃supp N
∃supp-ƛ = refl

supp-ƛ : supp (ƛ x ⇒ N) ≡ filter (¬? ∘ (_≟ x)) (supp N)
supp-ƛ = refl

∃supp-id : ∃supp (ƛ x ⇒ ` x) ≡ x ∷ x ∷ []
∃supp-id = refl

supp-id : supp (ƛ x ⇒ ` x) ≡ []
supp-id {x = x} rewrite ≟-refl x = refl

-- supp-abs⊆ : ∀ (t̂ : Abs Term) {a b} (a∉ : a ∉ supp t̂) (b∉ : b ∉ supp t̂) →
--   (∀fin t̂ .proj₂ a b) a∉ b∉ .proj₁ ⊆ supp t̂
