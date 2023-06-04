{-# OPTIONS --allow-unsolved-metas #-}
open import Prelude.Init; open SetAsType
open L.Mem
open import Prelude.DecEq
open import Prelude.Bifunctor
open import Prelude.InferenceRules
open import Prelude.InfEnumerable

module Nominal.Abs.Support (Atom : Type) ⦃ _ : DecEq Atom ⦄ ⦃ _ : Enumerable∞ Atom ⦄ where

open import Nominal.New Atom
open import Nominal.Swap Atom
open import Nominal.Support Atom
open import Nominal.Abs.Base Atom

module _ {A : Type ℓ} ⦃ _ : Swap A ⦄ ⦃ _ : SwapLaws A ⦄ where

  open ≡-Reasoning

  module _ ⦃ _ : ∃FinitelySupported A ⦄ where
    -- abstractions over finitely supported types are themselves finite
    instance
      ∃FinSupp-Abs : ∃FinitelySupported (Abs A)
      ∃FinSupp-Abs .∀∃fin (abs x t) =
        let xs , p = ∀∃fin t
        in x ∷ xs , λ y z y∉ z∉ →
        begin
          ⦅ z ↔ y ⦆ (abs x t)
        ≡⟨⟩
          -- ⦅ 𝕒 ↔ 𝕓 ⦆ (f 𝕔) ≡ (⦅ 𝕒 ↔ 𝕓 ⦆ f) (⦅ 𝕒 ↔ 𝕓 ⦆ 𝕔)
          abs (⦅ z ↔ y ⦆ x) (⦅ z ↔ y ⦆ t)
        ≡⟨ cong (λ ◆ → abs ◆ (⦅ z ↔ y ⦆ t))
              $ swap-noop z y x (λ where 𝟘 → z∉ 𝟘; 𝟙 → y∉ 𝟘) ⟩
          abs x (⦅ z ↔ y ⦆ t)
        ≡⟨ cong (abs _) $ p y z (y∉ ∘ there) (z∉ ∘ there) ⟩
          abs x t
        ∎ where open ≡-Reasoning

    -- Two ways to fix functoriality:
      -- 1. require that (f : A → A) is equivariant
    --   2. ...or that it at least has finite support
    mapAbs : Op₁ A → Op₁ (Abs A)
        -- ≡ (A → A) → (Abs A → Abs A)
    -- T0D0: In order to resolve termination issues (via well-founded recursion),
    -- we need a more restrainted version of mapAbs with type:
    -- mapAbs : (x' : Abs A) → (f : (a : A) → a ≺ f → A) → Abs A
    -- NB: a generalisation would be to say that the size behaviour of
    --     `mapAbs f` corresponds to that of `f`
    mapAbs f x' =
      let a = ∃fresh-var x' -- T0D0: ++ supp?? f
      in abs a (f $ conc x' a)

    freshen : Op₁ (Abs A)

    -- freshen f@(abs a t) =
    --   let xs , _ = ∀∃fin f
    --       b , b∉ = minFresh (a ∷ xs)
    --   in abs b (conc f b)

    freshen f@(abs a t) =
      let xs , _ = ∀∃fin f
          b , b∉ = minFresh xs
      in abs b (conc f b)

    safe-conc : Abs A → Atom → A
    safe-conc = conc ∘ freshen
{-

x  := abs a  (a  , T{b})
· a ♯ T
x' := abs a' (a' , T{b})
· a' ♯ T

safe-conc x b
conc (freshen x) b
swap b {T{b} ─ a}^a (conc (abs a (a, T{b})) ^a)
swap b {T{b} ─ a}^a (swap ^a a (a, T{b}))
swap b {T{b} ─ a}^a (^a, swap ^a a T{b})
swap b {T{b} ─ a}^a (^a, T{b})
(T{b} , ^a)
(T{b} , swap b ^a (swap ^a a b))
(T{b} , swap (swap b ^a ^a) (swap b ^a a) (swap b ^a b))
(T{b} , swap b (swap b ^a a) ^a

swap b ^a (swap ^a a T{b})
≡
swap b ^a T{b}
T{^a}
≟
T{^a'}
swap b ^a' T{b}



minFresh {T{b}} ≡ minFresh {T{b}}





minFresh {b} ≟ minFresh {b}

-- minFresh {a,b} ≟ minFresh {a',b}

(b , ^a')
swap b {a',b}^a' (^a', b)
swap b {a',b}^a' (swap ^a' a' (a', b))
swap b {a',b}^a' (conc (abs a' (a', b)) ^a')
conc (freshen x') b
safe-conc x' b

-}
  module _ ⦃ _ : FinitelySupported A ⦄ where

    -- abstractions over finitely supported types are themselves finite
    instance
      FinSupp-Abs : FinitelySupported (Abs A)
      FinSupp-Abs .∀fin t̂@(abs x t)
        with xs , p , ¬p ← ∀fin t
        = xs′ , eq , ¬eq
        where
          xs′ = filter (¬? ∘ (_≟ x)) xs

          eq : ∀ y z → y ∉ xs′ → z ∉ xs′ → swap z y t̂ ≡ t̂
          eq y z y∉′ z∉′
            with y ≟ x | z ≟ x
          ... | yes refl | yes refl
            = swap-id
          ... | yes refl | no z≢
            rewrite ≟-refl y
                  | dec-no (y ≟ z) (≢-sym z≢) .proj₂
            =
            begin
              abs z (⦅ z ↔ x ⦆ t)
            ≡⟨ extᵃ $ x ∷ xs , (λ w w∉ →
              begin
                conc (abs z (⦅ z ↔ x ⦆ t)) w
              ≡⟨⟩
                ⦅ w ↔ z ⦆ ⦅ z ↔ x ⦆ t
              ≡⟨ swap-swap ⟩
                ⦅ ⦅ w ↔ z ⦆ z ↔ ⦅ w ↔ z ⦆ x ⦆ ⦅ w ↔ z ⦆ t
              ≡⟨ cong (λ ◆ → ⦅ ◆ ↔ ⦅ w ↔ z ⦆ x ⦆ ⦅ w ↔ z ⦆ t)
                    $ swapʳ w z ⟩
                ⦅ w ↔ ⦅ w ↔ z ⦆ x ⦆ ⦅ w ↔ z ⦆ t
              ≡⟨ cong (λ ◆ → ⦅ w ↔ ◆ ⦆ ⦅ w ↔ z ⦆ t)
                    $ swap-noop w z x (λ where 𝟘 → w∉ 𝟘; 𝟙 → z≢ refl) ⟩
                ⦅ w ↔ x ⦆ ⦅ w ↔ z ⦆ t
              ≡⟨ cong (swap _ _) $ p z w z∉ (w∉ ∘ there) ⟩
                ⦅ w ↔ x ⦆ t
              ≡⟨⟩
                conc (abs x t) w
              ∎) ⟩
              abs x t
            ∎
            where
              z∉ : z ∉ xs
              z∉ z∈ = z∉′ $ ∈-filter⁺ (¬? ∘ (_≟ x)) z∈ z≢
          ... | no y≢ | yes refl
            rewrite ≟-refl z
            -- abs y (⦅ x ↔ y ⦆ t)
            =
            begin
              abs y (⦅ x ↔ y ⦆ t)
            ≡⟨ extᵃ $ x ∷ xs , (λ w w∉ →
              begin
                conc (abs y (⦅ x ↔ y ⦆ t)) w
              ≡⟨⟩
                ⦅ w ↔ y ⦆ ⦅ x ↔ y ⦆ t
              ≡⟨ swap-swap ⟩
                ⦅ ⦅ w ↔ y ⦆ x ↔ ⦅ w ↔ y ⦆ y ⦆ ⦅ w ↔ y ⦆ t
              ≡⟨ cong (λ ◆ → ⦅ ⦅ w ↔ y ⦆ x ↔ ◆ ⦆ ⦅ w ↔ y ⦆ t)
                    $ swapʳ w y ⟩
                ⦅ ⦅ w ↔ y ⦆ x ↔ w ⦆ ⦅ w ↔ y ⦆ t
              ≡⟨ cong (λ ◆ → ⦅ ◆ ↔ w ⦆ ⦅ w ↔ y ⦆ t)
                    $ swap-noop w y x (λ where 𝟘 → w∉ 𝟘; 𝟙 → y≢ refl) ⟩
                ⦅ x ↔ w ⦆ ⦅ w ↔ y ⦆ t
              ≡⟨ swap-rev ⟩
                ⦅ w ↔ x ⦆ ⦅ w ↔ y ⦆ t
              ≡⟨ cong (swap _ _) $ p y w y∉ (w∉ ∘ there) ⟩
                ⦅ w ↔ x ⦆ t
              ≡⟨⟩
                conc (abs x t) w
              ∎) ⟩
              abs x t
            ∎
            where
              y∉ : y ∉ xs
              y∉ y∈ = y∉′ $ ∈-filter⁺ (¬? ∘ (_≟ x)) y∈ y≢
          ... | no y≢ | no z≢
            rewrite swap-noop z y x (λ where 𝟘 → z≢ refl; 𝟙 → y≢ refl)
            = cong (abs _ ) $ p y z y∉ z∉
            where
              y∉ : y ∉ xs
              y∉ y∈ = y∉′ $ ∈-filter⁺ (¬? ∘ (_≟ x)) y∈ y≢

              z∉ : z ∉ xs
              z∉ z∈ = z∉′ $ ∈-filter⁺ (¬? ∘ (_≟ x)) z∈ z≢

          ¬eq : ∀ y z → y ∈ xs′ → z ∉ xs′ → swap z y t̂ ≢ t̂
          ¬eq y z y∈′ z∉′
            with y∈ , y≢ ← ∈-filter⁻ (¬? ∘ (_≟ x)) {xs = xs} y∈′
{-
begin
  swap z y t̂
≡⟨⟩
  abs (swap z y x) (swap z y t)
≉⟨ ? ⟩
  abs x t
≡⟨⟩
  t̂
∎
-}
            with z ≟ x
          ... | yes refl
            -- abs y (⦅ x ↔ y ⦆ t) ≉ abs x t
{-
begin
  swap x y t̂
≡⟨⟩
  abs (swap x y x) (swap x y t)
≡⟨ swapˡ ⟩
  abs y (swap x y t)
≉⟨ ? ⟩
  abs x t
≡⟨⟩
  t̂
∎
-}
            = {!¬p y z y∈ !}
          ... | no z≢
            rewrite dec-no (z ≟ x) z≢ .proj₂
            -- abs x (⦅ z ↔ y ⦆ t) ≉ abs x t
{-
¬p y z y∈ (∉-∷⁺ z≢ z∉) : swap z y t ≉ t

begin
  swap z y t̂
≡⟨⟩
  abs (swap z y x) (swap z y t)
≡⟨ swap-noop z y z z≢ y≢ ⟩
  abs x (swap z y t)
≉⟨ ? ⟩
  abs x t
≡⟨⟩
  t̂
∎
-}
            = {!¬p y z y∈ (∉-∷⁺ z≢ z∉′)!}
