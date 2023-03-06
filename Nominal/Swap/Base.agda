{- MOTTO: permutations distribute over everything -}
open import Prelude.Init; open SetAsType
open L.Mem
open import Prelude.General
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.Setoid
open import Prelude.InferenceRules

module Nominal.Swap.Base (Atom : Type) ⦃ _ : DecEq Atom ⦄ where

Atoms = List Atom

-- T0D0: use sized types to enforce size-preserving swap
record Swap (A : Type ℓ) : Type ℓ where
  field swap : Atom → Atom → A → A
  -- T0D0: ++ swap forms a group action by the group of atom permutations
  -- i.e. ∙ id x = x
  --      ∙ p (p′ x) = (p ∘ p′) x

  infixr 10 ⦅_↔_⦆_
  ⦅_↔_⦆_ = swap
  -- NB: equivariant functions commute with this group action

  swaps : List (Atom × Atom) → A → A
  swaps []             = id
  swaps ((x , y) ∷ as) = swap x y ∘ swaps as

open Swap ⦃...⦄ public

instance
  Swap-Atom : Swap Atom
  Swap-Atom .swap x y z =
    if      z == x then y
    else if z == y then x
    else                z

-- T0D0: permutations as bijections on `Atom` (infinite variant)

-- T0D0: to connect everything with the group theory behind
-- π∘π′ = (π′^π)∘π, where _^_ is the group conjugation action
--      = (π∘π′∘π⁻¹)∘π
--      = (π·π′)∘π

record CongSetoid (A : Set ℓ) ⦃ _ : ISetoid A ⦄ ⦃ _ : SetoidLaws A ⦄ : Setω where
  field ≈-cong : ∀ {B : Set ℓ′} ⦃ _ : ISetoid B ⦄ ⦃ _ : SetoidLaws B ⦄ →
                 ∀ (f : A → B) → Congruent _≈_ _≈_ f
open CongSetoid ⦃...⦄ public

instance
  Setoid-Atom : ISetoid Atom
  Setoid-Atom = λ where
    .relℓ → 0ℓ
    ._≈_  → _≡_

  SetoidLaws-Atom : SetoidLaws Atom
  SetoidLaws-Atom .isEquivalence = PropEq.isEquivalence

  CongSetoid-Atom : CongSetoid Atom
  CongSetoid-Atom .≈-cong _ refl = ≈-refl

swapˡ : ∀ 𝕒 𝕓 → ⦅ 𝕒 ↔ 𝕓 ⦆ 𝕒 ≡ 𝕓
swapˡ 𝕒 𝕓 rewrite ≟-refl 𝕒 = refl

swapʳ : ∀ 𝕒 𝕓 → ⦅ 𝕒 ↔ 𝕓 ⦆ 𝕓 ≡ 𝕒
swapʳ 𝕒 𝕓 with 𝕓 ≟ 𝕒
... | yes refl = refl
... | no  𝕓≢
  rewrite T⇒true $ fromWitnessFalse {Q = 𝕓 ≟ 𝕒} 𝕓≢
        | ≟-refl 𝕓
        = refl

swap-noop : ∀ 𝕒 𝕓 x → x ∉ 𝕒 ∷ 𝕓 ∷ []  → ⦅ 𝕒 ↔ 𝕓 ⦆ x ≡ x
swap-noop 𝕒 𝕓 x x∉ with x ≟ 𝕒
... | yes refl = ⊥-elim $ x∉ $ here refl
... | no _ with x ≟ 𝕓
... | yes refl = ⊥-elim $ x∉ $ there $′ here refl
... | no _ = refl

pattern 𝟘 = here refl
pattern 𝟙 = there 𝟘
pattern 𝟚 = there 𝟙
pattern 𝟛 = there 𝟚

module _ (A : Type ℓ) ⦃ _ : Swap A ⦄ ⦃ _ : LawfulSetoid A ⦄ where

  private variable
    x y : A
    𝕒 𝕓 𝕔 𝕕 : Atom

  record SwapLaws : Type (ℓ ⊔ₗ relℓ) where
    field
      cong-swap : x ≈ y → ⦅ 𝕒 ↔ 𝕓 ⦆ x ≈ ⦅ 𝕒 ↔ 𝕓 ⦆ y
      swap-id   : ⦅ 𝕒 ↔ 𝕒 ⦆ x ≈ x
      swap-rev  : ⦅ 𝕒 ↔ 𝕓 ⦆ x ≈ ⦅ 𝕓 ↔ 𝕒 ⦆ x
      swap-sym  : ⦅ 𝕒 ↔ 𝕓 ⦆ ⦅ 𝕓 ↔ 𝕒 ⦆ x ≈ x
      swap-swap : ⦅ 𝕒 ↔ 𝕓 ⦆ ⦅ 𝕔 ↔ 𝕕 ⦆ x
                ≈ ⦅ ⦅ 𝕒 ↔ 𝕓 ⦆ 𝕔 ↔ ⦅ 𝕒 ↔ 𝕓 ⦆ 𝕕 ⦆ ⦅ 𝕒 ↔ 𝕓 ⦆ x

    -- ** derived properties
    swap-comm :
      Disjoint (𝕒 ∷ 𝕓 ∷ []) (𝕔 ∷ 𝕕 ∷ [])
      ─────────────────────────────────────────────
      ⦅ 𝕒 ↔ 𝕓 ⦆ ⦅ 𝕔 ↔ 𝕕 ⦆ x ≈ ⦅ 𝕔 ↔ 𝕕 ⦆ ⦅ 𝕒 ↔ 𝕓 ⦆ x
    swap-comm {𝕒 = a}{b}{c}{d}{x} ab♯cd
      with eq ← swap-swap {𝕒 = a}{b}{c}{d}{x}
      rewrite swap-noop a b c $ ab♯cd ∘ (_, 𝟘)
            | swap-noop a b d $ ab♯cd ∘ (_, 𝟙)
            = eq

    swap-sym′ : ⦅ 𝕒 ↔ 𝕓 ⦆ ⦅ 𝕒 ↔ 𝕓 ⦆ x ≈ x
    swap-sym′ = ≈-trans (cong-swap swap-rev) swap-sym

    swap-id≈ : x ≈ y → ⦅ 𝕒 ↔ 𝕒 ⦆ x ≈ y
    swap-id≈ x≈y = ≈-trans (cong-swap x≈y) swap-id

    swap-rev≈ : x ≈ y → ⦅ 𝕒 ↔ 𝕓 ⦆ x ≈ ⦅ 𝕓 ↔ 𝕒 ⦆ y
    swap-rev≈ x≈y = ≈-trans swap-rev (cong-swap x≈y)

    swap-sym≈ : x ≈ y → ⦅ 𝕒 ↔ 𝕓 ⦆ ⦅ 𝕓 ↔ 𝕒 ⦆ x ≈ y
    swap-sym≈ x≈y = ≈-trans swap-sym x≈y

    swap-swap≈ : x ≈ y → ⦅ 𝕒 ↔ 𝕓 ⦆ ⦅ 𝕔 ↔ 𝕕 ⦆ x
                       ≈ ⦅ ⦅ 𝕒 ↔ 𝕓 ⦆ 𝕔 ↔ ⦅ 𝕒 ↔ 𝕓 ⦆ 𝕕 ⦆ ⦅ 𝕒 ↔ 𝕓 ⦆ y
    swap-swap≈ x≈y = ≈-trans swap-swap (cong-swap $ cong-swap x≈y)


open SwapLaws ⦃...⦄ public

private variable A : Type ℓ

instance
  SwapLaws-Atom : SwapLaws Atom
  SwapLaws-Atom .cong-swap = λ where refl → refl
  SwapLaws-Atom .swap-id {a}{x}
    with x ≟ a
  ... | yes refl = refl
  ... | no  _    = refl
  SwapLaws-Atom .swap-rev {a}{b}{c} with c ≟ a | c ≟ b
  ... | yes refl | yes refl = refl
  ... | yes refl | no _     = refl
  ... | no _     | yes refl = refl
  ... | no _     | no _     = refl
  SwapLaws-Atom .swap-sym {a}{b}{x}
    with x ≟ b
  ... | yes refl rewrite ≟-refl a = refl
  ... | no x≢b
    with x ≟ a
  ... | yes refl
    rewrite ≟-refl a
          | dec-no (b ≟ x) (≢-sym x≢b) .proj₂
          | ≟-refl b
          = refl
  ... | no x≢a
    rewrite dec-no (x ≟ a) x≢a .proj₂
          | dec-no (x ≟ b) x≢b .proj₂
          = refl
  SwapLaws-Atom .swap-swap {𝕒 = a}{b}{c}{d}{x}
  {- ⦅ 𝕒 ↔ 𝕓 ⦆ ⦅ 𝕔 ↔ 𝕕 ⦆ x
   ≈ ⦅ ⦅ 𝕒 ↔ 𝕓 ⦆ 𝕔 ↔ ⦅ 𝕒 ↔ 𝕓 ⦆ 𝕕 ⦆ ⦅ 𝕒 ↔ 𝕓 ⦆ x -}
    with a ≟ b | c ≟ d
  ... | yes refl | _
  {- ⦅ 𝕒 ↔ a ⦆ ⦅ 𝕔 ↔ 𝕕 ⦆ x
   ≈ ⦅ ⦅ 𝕒 ↔ a ⦆ 𝕔 ↔ ⦅ 𝕒 ↔ a ⦆ 𝕕 ⦆ ⦅ 𝕒 ↔ a ⦆ x -}
     rewrite swap-id {𝕒 = a} {x = ⦅ c ↔ d ⦆ x}
           | swap-id {𝕒 = a} {x = c}
           | swap-id {𝕒 = a} {x = d}
           | swap-id {𝕒 = a} {x = x}
           = refl
  ... | _ | yes refl
  {- ⦅ 𝕒 ↔ 𝕓 ⦆ ⦅ 𝕔 ↔ c ⦆ x
   ≈ ⦅ ⦅ 𝕒 ↔ 𝕓 ⦆ 𝕔 ↔ ⦅ 𝕒 ↔ 𝕓 ⦆ c ⦆ ⦅ 𝕒 ↔ 𝕓 ⦆ x -}
     rewrite swap-id {𝕒 = c} {x = x}
           | swap-id {𝕒 = ⦅ a ↔ b ⦆ c} {x = ⦅ a ↔ b ⦆ x}
           = refl
  ... | no a≢b | no c≢d
  {- ⦅ 𝕒 ↔ 𝕓 ⦆ ⦅ 𝕔 ↔ 𝕕 ⦆ x
   ≈ ⦅ ⦅ 𝕒 ↔ 𝕓 ⦆ 𝕔 ↔ ⦅ 𝕒 ↔ 𝕓 ⦆ 𝕕 ⦆ ⦅ 𝕒 ↔ 𝕓 ⦆ x -}
    with x ≟ c
  SwapLaws-Atom .swap-swap {𝕒 = a}{b}{c}{d}{x}
    | no a≢b | no c≢d | yes refl
  {- ⦅ 𝕒 ↔ 𝕓 ⦆ 𝕕
   ≈ ⦅ ⦅ 𝕒 ↔ 𝕓 ⦆ 𝕔 ↔ ⦅ 𝕒 ↔ 𝕓 ⦆ 𝕕 ⦆ ⦅ 𝕒 ↔ 𝕓 ⦆ c -}
     rewrite swapˡ (⦅ a ↔ b ⦆ c) (⦅ a ↔ b ⦆ d) = refl
  SwapLaws-Atom .swap-swap {𝕒 = a}{b}{c}{d}{x}
    | no a≢b | no c≢d | no x≢c
    with x ≟ d
  {- ⦅ 𝕒 ↔ 𝕓 ⦆ ⦅ ✓𝕔 ↔ 𝕕 ⦆ x
   ≈ ⦅ ⦅ 𝕒 ↔ 𝕓 ⦆ 𝕔 ↔ ⦅ 𝕒 ↔ 𝕓 ⦆ 𝕕 ⦆ ⦅ 𝕒 ↔ 𝕓 ⦆ x -}
  ... | yes refl
  {- ⦅ 𝕒 ↔ 𝕓 ⦆ 𝕔
   ≈ ⦅ ⦅ 𝕒 ↔ 𝕓 ⦆ 𝕔 ↔ ⦅ 𝕒 ↔ 𝕓 ⦆ 𝕕 ⦆ ⦅ 𝕒 ↔ 𝕓 ⦆ d -}
     rewrite swapʳ (⦅ a ↔ b ⦆ c) (⦅ a ↔ b ⦆ d) = refl
  ... | no x≢d
  {- ⦅ 𝕒 ↔ 𝕓 ⦆ x
   ≈ ⦅ ⦅ 𝕒 ↔ 𝕓 ⦆ 𝕔 ↔ ⦅ 𝕒 ↔ 𝕓 ⦆ 𝕕 ⦆ ⦅ 𝕒 ↔ 𝕓 ⦆ x -}
     with x ≟ a
  SwapLaws-Atom .swap-swap {𝕒 = a}{b}{c}{d}{x}
    | no a≢b | no c≢d | no a≢c | no a≢d | yes refl {-x≡a-}
  {- 𝕓 ≈ ⦅ ⦅ 𝕒 ↔ 𝕓 ⦆ 𝕔 ↔ ⦅ 𝕒 ↔ 𝕓 ⦆ 𝕕 ⦆ 𝕓 -}
    rewrite dec-no (c ≟ a) (≢-sym a≢c) .proj₂
  {- 𝕓 ≈ ⦅ ⦅ ✓𝕒 ↔ 𝕓 ⦆ 𝕔 ↔ ⦅ 𝕒 ↔ 𝕓 ⦆ 𝕕 ⦆ 𝕓 -}
    rewrite dec-no (d ≟ a) (≢-sym a≢d) .proj₂
  {- 𝕓 ≈ ⦅ ⦅ ✓𝕒 ↔ 𝕓 ⦆ 𝕔 ↔ ⦅ ✓𝕒 ↔ 𝕓 ⦆ 𝕕 ⦆ 𝕓 -}
    with c ≟ b | d ≟ b
  ... | yes refl {-c≡b-} | yes refl {-d≡b-} {- 𝕓 ≈ ⦅ 𝕒 ↔ 𝕒 ⦆ 𝕓 -}
    rewrite swap-id {𝕒 = a} {x = b} = refl
  ... | yes refl {-c≡b-} | no d≢b {- 𝕓 ≈ ⦅ 𝕒 ↔ 𝕕 ⦆ 𝕓 -}
    rewrite swap-noop a d b (λ where 𝟘 → a≢b refl; 𝟙 → d≢b refl) = refl
  ... | no c≢b | yes refl {-d≡b-} {- 𝕓 ≈ ⦅ 𝕔 ↔ 𝕒 ⦆ 𝕓 -}
    rewrite swap-noop c a b (λ where 𝟘 → c≢b refl; 𝟙 → a≢b refl) = refl
  ... | no c≢b | no d≢b {- 𝕓 ≈ ⦅ 𝕔 ↔ 𝕕 ⦆ 𝕓 -}
    rewrite swap-noop c d b (λ where 𝟘 → c≢b refl; 𝟙 → d≢b refl) = refl
  SwapLaws-Atom .swap-swap {𝕒 = a}{b}{c}{d}{x}
    | no a≢b | no c≢d | no x≢c | no x≢d | no x≢a
  {- ⦅ 𝕒 ↔ 𝕓 ⦆ x ≈ ⦅ ⦅ 𝕒 ↔ 𝕓 ⦆ 𝕔 ↔ ⦅ 𝕒 ↔ 𝕓 ⦆ 𝕕 ⦆ ⦅ ✓𝕒 ↔ 𝕓 ⦆ x -}
     with x ≟ b
  SwapLaws-Atom .swap-swap {𝕒 = a}{b}{c}{d}{x}
    | no a≢b | no c≢d | no b≢c | no b≢d | no b≢a | yes refl {-x≡b-}
  {- 𝕒 ≈ ⦅ ⦅ 𝕒 ↔ 𝕓 ⦆ 𝕔 ↔ ⦅ 𝕒 ↔ 𝕓 ⦆ 𝕕 ⦆ 𝕒 -}
    with c ≟ a | d ≟ a
  ... | yes refl {-c≡a-} | yes refl {-d≡a-} = ⊥-elim $ c≢d refl
  ... | yes refl {-c≡a-} | no d≢a {- 𝕒 ≈ ⦅ 𝕓 ↔ ⦅ ✓𝕒 ↔ 𝕓 ⦆ 𝕕 ⦆ 𝕒 -}
    rewrite dec-no (d ≟ b) (≢-sym b≢d) .proj₂
          | swap-noop b d a (λ where 𝟘 → a≢b refl; 𝟙 → d≢a refl)
          = refl
  ... | no c≢a | yes refl {-d≡a-} {- 𝕒 ≈ ⦅ ⦅ ✓𝕒 ↔ 𝕓 ⦆ 𝕔 ↔ 𝕓 ⦆ 𝕒 -}
    rewrite dec-no (c ≟ b) (≢-sym b≢c) .proj₂
          | swap-noop c b a (λ where 𝟘 → c≢a refl; 𝟙 → a≢b refl)
          = refl
  ... | no c≢a | no d≢a {- 𝕒 ≈ ⦅ ⦅ ✓𝕒 ↔ 𝕓 ⦆ 𝕔 ↔ ⦅ ✓𝕒 ↔ 𝕓 ⦆ 𝕕 ⦆ 𝕒 -}
    rewrite dec-no (c ≟ b) (≢-sym b≢c) .proj₂
          | dec-no (d ≟ b) (≢-sym b≢d) .proj₂
          | swap-noop c d a (λ where 𝟘 → c≢a refl; 𝟙 → d≢a refl)
          = refl
  SwapLaws-Atom .swap-swap {𝕒 = a}{b}{c}{d}{x}
    | no a≢b | no c≢d | no x≢c | no x≢d | no x≢a | no x≢b
  {- ⦅ 𝕒 ↔ 𝕓 ⦆ x ≈ ⦅ ⦅ 𝕒 ↔ 𝕓 ⦆ 𝕔 ↔ ⦅ 𝕒 ↔ 𝕓 ⦆ 𝕕 ⦆ x -}
    rewrite swap-noop a b x (λ where 𝟘 → x≢a refl; 𝟙 → x≢b refl)
  {- x ≈ ⦅ ⦅ 𝕒 ↔ 𝕓 ⦆ 𝕔 ↔ ⦅ 𝕒 ↔ 𝕓 ⦆ 𝕕 ⦆ x -}
    with c ≟ a | c ≟ b | d ≟ a | d ≟ b
  ... | yes refl | _ | yes refl | _ = ⊥-elim $ c≢d refl
  ... | yes refl | _ | no d≢a   | yes refl
    {- x ≈ ⦅ 𝕓 ↔ 𝕒 ⦆ x -}
    rewrite swap-noop b a x (λ where 𝟘 → x≢b refl; 𝟙 → x≢a refl) = refl
  ... | yes refl | _ | no d≢a   | no d≢b
    {- x ≈ ⦅ 𝕓 ↔ 𝕕 ⦆ x -}
    rewrite swap-noop b d x (λ where 𝟘 → x≢b refl; 𝟙 → x≢d refl) = refl
  ... | _ | yes refl | _ | yes refl = ⊥-elim $ c≢d refl
  ... | no c≢a | yes refl | yes refl | _
    {- x ≈ ⦅ 𝕒 ↔ 𝕓 ⦆ x -}
    rewrite swap-noop a b x (λ where 𝟘 → x≢a refl; 𝟙 → x≢b refl) = refl
  ... | no c≢a | yes refl | no d≢a | no d≢b
    {- x ≈ ⦅ 𝕒 ↔ d ⦆ x -}
    rewrite swap-noop a d x (λ where 𝟘 → x≢a refl; 𝟙 → x≢d refl) = refl
  ... | no c≢a | no c≢b | yes refl | _
    {- x ≈ ⦅ 𝕔 ↔ 𝕓 ⦆ x -}
    rewrite swap-noop c b x (λ where 𝟘 → x≢c refl; 𝟙 → x≢b refl) = refl
  ... | no c≢a | no c≢b | no d≢a | yes refl
    {- x ≈ ⦅ 𝕔 ↔ 𝕒 ⦆ x -}
    rewrite swap-noop c a x (λ where 𝟘 → x≢c refl; 𝟙 → x≢a refl) = refl
  ... | no c≢a | no c≢b | no d≢a | no d≢b
    {- x ≈ ⦅ 𝕔 ↔ 𝕕 ⦆ x -}
    rewrite swap-noop c d x (λ where 𝟘 → x≢c refl; 𝟙 → x≢d refl) = refl

-- ** Nameless instances.
swapId : Atom → Atom → A → A
swapId _ _ = id

mkNameless : (A : Type) → Swap A
mkNameless A = λ where .swap → swapId

instance
  ⊤∅ = mkNameless ⊤
  𝔹∅ = mkNameless Bool
  ℕ∅ = mkNameless ℕ
  ℤ∅ = mkNameless ℤ
  Char∅   = mkNameless Char
  String∅ = mkNameless String

swap-≢ : ∀ {z w x y} → z ≢ w → swap x y z ≢ swap x y w
swap-≢ {z}{w}{x}{y} z≢w
  with z ≟ x
swap-≢ {z}{w}{x}{y} z≢w | yes refl
  rewrite dec-no (w ≟ z) (≢-sym z≢w) .proj₂
  with w ≟ y
... | yes refl = ≢-sym z≢w
... | no w≢y = ≢-sym w≢y
swap-≢ {z}{w}{x}{y} z≢w | no z≢x
  with z ≟ y
... | yes refl
  = QED
  where
  QED : x ≢ swap x z w
  QED with w ≟ x
  ... | yes refl = ≢-sym z≢x
  ... | no w≢x
    rewrite dec-no (w ≟ z) (≢-sym z≢w) .proj₂
    = ≢-sym w≢x
... | no z≢y
  with w ≟ x
... | yes refl = z≢y
... | no _
  with w ≟ y
... | yes refl = z≢x
... | no _     = z≢w
