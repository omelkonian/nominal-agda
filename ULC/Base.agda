open import Prelude.Init; open SetAsType
open import Prelude.DecEq
open import Prelude.General
open import Prelude.Closures
open import Prelude.InferenceRules
open import Prelude.Decidable
open import Prelude.Membership
open import Prelude.Bifunctor

module ULC.Base (Atom : Type) ⦃ _ : DecEq Atom ⦄ where

open import Nominal Atom

-- ** ULC terms.
data Term : Type where
  `_  : Atom → Term
  _·_ : Op₂ Term
  ƛ_  : Abs Term → Term
{-# TERMINATING #-}
unquoteDecl Swap-Term = DERIVE Swap [ quote Term , Swap-Term ]

infix  30 `_
infixl 20 _·_
infixr 10 ƛ_
infixr 5 ƛ_⇒_
pattern ƛ_⇒_ x y = ƛ abs x y

variable
  x y z w x′ y′ z′ w′ 𝕩 𝕪 𝕫 𝕨 : Atom
  t t′ t″ L L′ M M′ N N′ M₁ M₂ : Term
  t̂ t̂′ t̂″ : Abs Term

-- ** utilities

data TermShape : Type where
  `∎  : TermShape
  ƛ_  : TermShape → TermShape
  _·_ : TermShape → TermShape → TermShape

shape : Term → TermShape
shape = λ where
  (ƛ t)   → ƛ shape (t .term)
  (L · M) → shape L · shape M
  (` _)   → `∎

private
  postulate 𝕒 𝕓 : Atom

  _ : shape (ƛ 𝕒 ⇒ ƛ 𝕓 ⇒ ` 𝕒 · (` 𝕓 · ` 𝕒))
    ≡ (ƛ ƛ `∎ · (`∎ · `∎))
  _ = refl

isVarShape isLamShape isAppShape : Pred₀ TermShape
isVarShape = λ where
  `∎ → ⊤
  _ → ⊥
isLamShape = λ where
  (ƛ _) → ⊤
  _ → ⊥
isAppShape = λ where
  (_ · _) → ⊤
  _ → ⊥

isƛ isApp isVar : Pred₀ Term
isƛ   = isLamShape ∘ shape
isApp = isAppShape ∘ shape
isVar = isVarShape ∘ shape

unƛ : (t : Term) {_ : isƛ t} → Abs Term
unƛ (ƛ t̂) {tt} = t̂

unApp : (t : Term) {_ : isApp t} → Term × Term
unApp (L · M) {tt} = L , M

unVar : (t : Term) {_ : isVar t} → Atom
unVar (` v) {tt} = v

_≡⦅shape⦆_ = _≡_ on shape

app-shape≡ : (L · M) ≡⦅shape⦆ (L′ · M′) → (L ≡⦅shape⦆ L′) × (M ≡⦅shape⦆ M′)
app-shape≡ {L}{M}{L′}{M′} eq
  with shape L | shape L′ | shape M | shape M′ | eq
... | _ | _ | _ | _ | refl = refl , refl

app-shape≡˘ : (L ≡⦅shape⦆ L′) → (M ≡⦅shape⦆ M′) → (L · M) ≡⦅shape⦆ (L′ · M′)
app-shape≡˘ {L}{M}{L′}{M′} L≡ M≡
  with shape L | shape L′ | L≡
... | _ | _ | refl
  with shape M | shape M′ | M≡
... | _ | _ | refl = refl

lam-shape≡ : (ƛ t̂) ≡⦅shape⦆ (ƛ t̂′) → t̂ .term ≡⦅shape⦆ t̂′ .term
lam-shape≡ {t̂}{t̂′} eq
  with shape (t̂ .term) | shape (t̂′ .term) | eq
... | _ | _ | refl = refl

lam-shape≡˘ :  t̂ .term ≡⦅shape⦆ t̂′ .term → (ƛ t̂) ≡⦅shape⦆ (ƛ t̂′)
lam-shape≡˘ {t̂}{t̂′} eq
  with shape (t̂ .term) | shape (t̂′ .term) | eq
... | _ | _ | refl = refl

swap-shape≡ : ∀ x y t → t ≡⦅shape⦆ swap x y t
swap-shape≡ x y = λ where
  (` _) → refl
  (L · M) → app-shape≡˘ (swap-shape≡ x y L) (swap-shape≡ x y M)
  (ƛ t̂) → lam-shape≡˘ {t̂}{swap x y t̂} $ swap-shape≡ x y (t̂ .term)

swap-shape : ∀ t t′ → t ≡⦅shape⦆ t′ → swap x y t ≡⦅shape⦆ swap x′ y′ t′
swap-shape t t′ = flip trans (swap-shape≡ _ _ t′)
                ∘ trans (sym $ swap-shape≡ _ _ t)

conc-shape : ∀ t̂ t̂′ → t̂ .term ≡⦅shape⦆ t̂′ .term → conc t̂ x ≡⦅shape⦆ conc t̂′ y
conc-shape t̂ t̂′ eq = swap-shape (t̂ .term) (t̂′ .term) eq

conc-shape≡ : ∀ t̂ → t̂ .term ≡⦅shape⦆ conc t̂ x
conc-shape≡ t̂ = swap-shape≡ _ _ (t̂ .term)
