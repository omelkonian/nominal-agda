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
open import Prelude.Tactics.PostulateIt

open import Prelude.Generics
open Meta
open Debug ("equivariance" , 100)

module Nominal.Swap.Equivariance (Atom : Set) ⦃ _ : DecEq Atom ⦄ where

open import Nominal.Swap.Base Atom

-- ** generically postulate the axiom scheme expressing distributivity of swapping:
{- ∀ (𝕒 𝕓 : Atom).
     ∙[n = 0]
       ∀ (x : A).
         swap 𝕒 𝕓 x ≈ swap 𝕒 𝕓 x
     ∙[n = 1]
       ∀ (f : A → B) (x : A).
         swap 𝕒 𝕓 (f x) ≈ (swap 𝕒 𝕓 f) (swap 𝕒 𝕓 x)
     ∙[n = 2]
       ∀ (f : A → B → C) (x : A) (y : B).
         swap 𝕒 𝕓 (f x y) → (swap 𝕒 𝕓 f) (swap 𝕒 𝕓 x) (swap 𝕒 𝕓 y)
     ⋮
-}
deriveSwapDistributiveType : Bool → Term → TC Type
deriveSwapDistributiveType equiv? t = do
  ty ← inferType t
  print $ show t ◇ " : " ◇ show ty
  printCurrentContext
  ctx ← getContext
  let
    as₀ = argTys ty
    as  = map (fmap $ mapVars (_+ 2)) as₀
    n = length as

    mkSwaps : Args Term → Term
    mkSwaps as = def (quote swap) $ map vArg ({-𝕒-} ♯ (suc n) ∷ {-𝕓-} ♯ n ∷ []) ++ as

    mkSwap : Op₁ Term
    mkSwap t = mkSwaps [ vArg t ]

    mkHead : Args Term → Term
    mkHead as = case t of λ where
      (def f as₀) → def f (as₀ ++ as)
      (con c as₀) → con c (as₀ ++ as)
      (var i as₀) → var (i + 2 + n) (as₀ ++ as)
      _           → unknown

    mkSwapHead : Args Term → Term
    mkSwapHead as =
      let
        a = case t of λ where
          (def f as₀) → def f as₀
          (con c as₀) → con c as₀
          (var i as₀) → var (i + 2 + n) as₀
          _           → unknown
      in mkSwaps (vArg a ∷ as)

    mkTerm : Op₁ Term → Args Term
    mkTerm mk = flip map (enumerate as) λ where
      (i , arg v _) → arg v $ mk (♯ (n ∸ suc (toℕ i)))

    lhs = mkSwap $ mkHead (mkTerm id)
    rhs = (if equiv? then mkHead else mkSwapHead) (mkTerm mkSwap)

    equivTy = vΠ[ "𝕒" ∶ ♯ (length ctx ∸ 1) ]
              vΠ[ "𝕓" ∶ ♯ (length ctx) ]
              ∀args as (quote _≈_ ∙⟦ lhs ∣ rhs ⟧)
  print $ "Equivariant " ◇ show t ◇ " := " ◇ show equivTy
  print "-------------------------------------------------"
  return equivTy
  where
    ∀args : Args Type → (Type → Type)
    ∀args [] = id
    ∀args (a ∷ as) t = hΠ[ "_" ∶ unArg a ] ∀args as t

deriveSwap↔       = deriveSwapDistributiveType false

macro
  Swap↔ : Term → Hole → TC ⊤
  Swap↔ t hole = deriveSwap↔ t >>= unify hole

  swap↔ : Term → Hole → TC ⊤
  swap↔ t hole = do
    n ← genPostulate =<< deriveSwap↔ t
    unify hole (n ∙)

postulateSwap↔ : Name → Term → TC ⊤
postulateSwap↔ f t = declarePostulate (vArg f) =<< deriveSwap↔ t

-- ** derive the statement of equivariance for given term of arbitrary arity,
-- be it a definition, constructor, or local variable
{- ∀ (𝕒 𝕓 : Atom).
     ∙[n = 0]
       ∀ (x : A).
         swap 𝕒 𝕓 x ≈ x
     ∙[n = 1]
       ∀ (f : A → B) (x : A).
         swap 𝕒 𝕓 (f x) ≈ f (swap 𝕒 𝕓 x)
     ∙[n = 2]
       ∀ (f : A → B → C) (x : A) (y : B).
         swap 𝕒 𝕓 (f x y) → f (swap 𝕒 𝕓 x) (swap 𝕒 𝕓 y)
     ⋮
-}
macro
  Equivariant : Term → Hole → TC ⊤
  Equivariant t hole = deriveSwapDistributiveType true t >>= unify hole

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
      _ : Swap (ℕ → ℕ)
      _ : Swap (ℕ → ℕ → ℕ)
      _ : Swap (ℕ → ℕ → X)

  module _ 𝕒 𝕓 where postulate
    distr-f : ∀ {n} →
      swap 𝕒 𝕓 (f n) ≈ (swap 𝕒 𝕓 f) (swap 𝕒 𝕓 n)
    equiv-f : ∀ {n} →
      swap 𝕒 𝕓 (f n) ≈ f (swap 𝕒 𝕓 n)
    distr-g : ∀ {n m} →
      swap 𝕒 𝕓 (g n m) ≈ (swap 𝕒 𝕓 g) (swap 𝕒 𝕓 n) (swap 𝕒 𝕓 m)
    equiv-g : ∀ {n m} →
      swap 𝕒 𝕓 (g n m) ≈ g (swap 𝕒 𝕓 n) (swap 𝕒 𝕓 m)
    distr-mkX : ∀ {n m} →
      swap 𝕒 𝕓 (mkX n m) ≈ (swap 𝕒 𝕓 mkX) (swap 𝕒 𝕓 n) (swap 𝕒 𝕓 m)
    equiv-mkX : ∀ {n m} →
      swap 𝕒 𝕓 (mkX n m) ≈ mkX (swap 𝕒 𝕓 n) (swap 𝕒 𝕓 m)
  module _ {f : ℕ → ℕ} 𝕒 𝕓 where postulate
    distr-∀f : ∀ {n} → swap 𝕒 𝕓 (f n) ≈ (swap 𝕒 𝕓 f) (swap 𝕒 𝕓 n)
    equiv-∀f : ∀ {n} → swap 𝕒 𝕓 (f n) ≈ f (swap 𝕒 𝕓 n)

  _ = Swap↔ f ∋ distr-f
  _ = Swap↔ f ∋ swap↔ f
  _ = Equivariant f ∋ equiv-f
  _ = Swap↔ g ∋ distr-g
  _ = Swap↔ g ∋ swap↔ g
  _ = Equivariant g ∋ equiv-g
  _ = Swap↔ mkX ∋ distr-mkX
  _ = Swap↔ mkX ∋ swap↔ mkX
  _ = Equivariant mkX ∋ equiv-mkX
  module _ {f : ℕ → ℕ} where
    _ = Swap↔ f ∋ swap↔ f
    _ = Swap↔ f ∋ distr-∀f
    _ = Equivariant f ∋ equiv-∀f

  unquoteDecl distr-f′ = postulateSwap↔ distr-f′ (quoteTerm f)
  unquoteDecl distr-g′ = postulateSwap↔ distr-g′ (quoteTerm g)
  unquoteDecl distr-mkX′ = postulateSwap↔ distr-mkX′ (quoteTerm mkX)
  module _ {f : ℕ → ℕ} where
    unquoteDecl distr-∀f′ = postulateSwap↔ distr-∀f′ (quoteTerm f)
