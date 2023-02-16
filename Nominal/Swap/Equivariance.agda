{-# OPTIONS --v equivariance:100 #-}
open import Prelude.Init
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
macro
  Equivariant : Term → Hole → TC ⊤
  Equivariant t hole = do
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
                ∀args as (quote _≈_ ∙⟦ mkSwap lhs ∣ rhs ⟧)
    print $ "Equivariant " ◇ show t ◇ " := " ◇ show equivTy
    unify hole equivTy
    print "-------------------------------------------------"
    where
      ∀args : Args Type → (Type → Type)
      ∀args [] = id
      ∀args (a ∷ as) t = hΠ[ "_" ∶ unArg a ] ∀args as t

private

  data X : Set where
    mkX : ℕ → ℕ → X

  postulate
    𝕒 𝕓 : Atom
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
    equiv-∀f : ∀ {f : ℕ → ℕ} {n} → swap 𝕒 𝕓 (f n) ≈ f (swap 𝕒 𝕓 n)

  _ : Equivariant f
  _ = equiv-f

  _ : Equivariant g
  _ = equiv-g

  _ : Equivariant mkX
  _ = equiv-mkX

  test-equiv∀f : ∀ {f : ℕ → ℕ} → Equivariant f
  test-equiv∀f {f = f} 𝕒 𝕓 = equiv-∀f 𝕒 𝕓 {f = f}
