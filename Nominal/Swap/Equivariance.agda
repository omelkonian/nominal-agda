{-# OPTIONS --v equivariance:100 #-}
open import Prelude.Init
open L.Mem
open import Prelude.DecEq
open import Prelude.Functor
open import Prelude.Monad
open import Prelude.Semigroup
open import Prelude.Show
open import Prelude.Setoid
open import Prelude.Lists
open import Prelude.ToN

open import Prelude.Generics
open Meta
open Debug ("equivariance" , 100)

module Nominal.Swap.Equivariance (Atom : Set) ⦃ _ : DecEq Atom ⦄ where

open import Nominal.Swap.Base Atom

-- ** derive the statement of equivariance for given term of arbitrary arity,
-- be it a definition, constructor, or local variable

deriveEquivarianceType : Term → TC Type
deriveEquivarianceType t = do
  ty ← inferType t
  print $ show t ◇ " : " ◇ show ty
  printCurrentContext
  ctx ← getContext
  let
    as₀ = argTys ty
    as  = map (fmap $ mapVars (_+ 2)) as₀
    n = length as

    headFn : Args Term → Term
    headFn as = case t of λ where
      (def f as₀) → def f (as₀ ++ as)
      (con c as₀) → con c (as₀ ++ as)
      (var i as₀) → var (i + 2 + n) (as₀ ++ as)
      _           → unknown

    mkSwap : Op₁ Term
    mkSwap t = quote swap ∙⟦ {-𝕒-} ♯ (suc n) ∣ {-𝕓-} ♯ n ∣ t ⟧

    mkTerm : Op₁ Term → Term
    mkTerm f = headFn $ flip map (enumerate as) λ where
      (i , arg v _) →
        arg v (f $ ♯ (n ∸ suc (toℕ i)))

    lhs = mkTerm id
    rhs = mkTerm mkSwap

    equivTy = vΠ[ "𝕒" ∶ ♯ (length ctx ∸ 1) ]
              vΠ[ "𝕓" ∶ ♯ (length ctx) ]
              -- ∀args as (quote _≡_ ∙⟦ mkSwap lhs ∣ rhs ⟧)
              ∀args as (quote _≈_ ∙⟦ mkSwap lhs ∣ rhs ⟧)
  print $ "Equivariant " ◇ show t ◇ " := " ◇ show equivTy
  print "-------------------------------------------------"
  return equivTy
  where
    ∀args : Args Type → (Type → Type)
    ∀args [] = id
    ∀args (a ∷ as) t = hΠ[ "_" ∶ unArg a ] ∀args as t

open import Prelude.Tactics.PostulateIt

macro
  Equivariant : Term → Hole → TC ⊤
  Equivariant t hole = deriveEquivarianceType t >>= unify hole

  equivariant : Term → Hole → TC ⊤
  equivariant t hole = do
    n ← genPostulate =<< deriveEquivarianceType t
    unify hole (n ∙)

private

  data X : Set where
    mkX : ℕ → ℕ → X

  variable
    𝕒 𝕓 𝕔 𝕕 : Atom
  postulate
    n m : ℕ
    f : ℕ → ℕ
    g : ℕ → ℕ → ℕ

    instance
      _ : ISetoid ℕ
      _ : ISetoid X
      _ : Swap X

  module _ 𝕒 𝕓 where postulate
    equiv-f : ∀ {n} → swap 𝕒 𝕓 (f n) ≈ f (swap 𝕒 𝕓 n)
    equiv-g : ∀ {n m} → swap 𝕒 𝕓 (g n m) ≈ g (swap 𝕒 𝕓 n) (swap 𝕒 𝕓 m)
    equiv-mkX : ∀ {n m} → swap 𝕒 𝕓 (mkX n m) ≈ mkX (swap 𝕒 𝕓 n) (swap 𝕒 𝕓 m)
  module _ {f : ℕ → ℕ} 𝕒 𝕓 where postulate
    equiv-∀f : ∀ {n} → swap 𝕒 𝕓 (f n) ≈ f (swap 𝕒 𝕓 n)

  _ = Equivariant f ∋ equiv-f
  _ = Equivariant f ∋ equivariant f
  _ = Equivariant g ∋ equiv-g
  _ = Equivariant g ∋ equivariant g
  _ = Equivariant mkX ∋ equiv-mkX
  _ = Equivariant mkX ∋ equivariant mkX
  module _ {f : ℕ → ℕ} where
    _ = Equivariant f ∋ equivariant f
    _ = Equivariant f ∋ equiv-∀f

  -- ** deriving ⊥ from non-equivariant function
  module Contradiction (𝕒≠𝕓 : 𝕒 ≢ 𝕓) (𝕔≠𝕕 : 𝕔 ≢ 𝕕) (𝕔∉ : 𝕔 ∉ 𝕒 ∷ 𝕓 ∷ []) where
    nonEq : Atom → Atom
    nonEq x = if x == 𝕒 then 𝕔 else 𝕕

    equiv-nonEq : Equivariant nonEq
    equiv-nonEq = equivariant nonEq

    equiv-nonEq-at : swap 𝕒 𝕓 (nonEq 𝕒) ≡ nonEq (swap 𝕒 𝕓 𝕒)
    equiv-nonEq-at = equiv-nonEq 𝕒 𝕓

    equiv-nonEq-at♯not : swap 𝕒 𝕓 (nonEq 𝕒) ≢ nonEq (swap 𝕒 𝕓 𝕒)
    equiv-nonEq-at♯not
    -- swap 𝕒 𝕓 (f x)
    -- => swap 𝕒 𝕓 (f 𝕒)
    -- => swap 𝕒 𝕓 𝕔
    -- => 𝕔

    -- f (swap 𝕒 𝕓 x)
    -- => f (swap 𝕒 𝕓 𝕒)
    -- => f 𝕓
    -- => 𝕕
      rewrite swapˡ 𝕒 𝕓
            | dec-no (𝕓 ≟ 𝕒) (≢-sym 𝕒≠𝕓) .proj₂
            | ≟-refl 𝕒
            | swap-noop 𝕒 𝕓 𝕔 𝕔∉
            = 𝕔≠𝕕

    bottom : ⊥
    bottom = equiv-nonEq-at♯not equiv-nonEq-at

  -- ** simpler example for deriving ⊥
  module SimpleContradiction (𝕒≠𝕓 : 𝕒 ≢ 𝕓) where
    nonEq : Atom → Atom
    nonEq _ = 𝕓

    equiv-nonEq : Equivariant nonEq
    equiv-nonEq = equivariant nonEq

    equiv-nonEq-at : swap 𝕒 𝕓 (nonEq 𝕒) ≡ nonEq (swap 𝕒 𝕓 𝕒)
    equiv-nonEq-at = equiv-nonEq 𝕒 𝕓 {𝕒}

    equiv-nonEq-at♯not : swap 𝕒 𝕓 (nonEq 𝕒) ≢ nonEq (swap 𝕒 𝕓 𝕒)
    equiv-nonEq-at♯not rewrite swapʳ 𝕒 𝕓 = 𝕒≠𝕓
    -- swap 𝕒 𝕓 (f x)
    -- => swap 𝕒 𝕓 𝕓
    -- => 𝕒

    -- f (swap 𝕒 𝕓 x)
    -- => 𝕓

    bottom : ⊥
    bottom = equiv-nonEq-at♯not equiv-nonEq-at
