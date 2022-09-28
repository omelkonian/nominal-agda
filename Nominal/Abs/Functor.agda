open import Prelude.Init
open SetAsType
open import Prelude.DecEq

module Nominal.Abs.Functor (Atom : Type) ⦃ _ : DecEq Atom ⦄ where

open import Nominal.Swap     Atom
open import Nominal.Abs.Base Atom

  -- postulate New : (Atom → Set) → Set

  -- mutual
  --   fresh : (Atom → X) → X
  --   fresh = {!!}

  --   mapAbs : (A → B) → (Abs A → Abs B)
  --   mapAbs f x' = fresh λ 𝕒 →
  --   -- New 𝕒. mapAbs f x' =
  --     abs 𝕒 (f $ conc x' 𝕒)

-- instance
--   Functor-AbsAtom : Functor Abs
--   Functor-AbsAtom ._<$>_ f (abs 𝕒 x) = abs 𝕒 (f x)
--   Functor-AbsAtom ._<$>_ f x' = fresh λ 𝕒 → abs 𝕒 (f $ conc x' 𝕒)

  -- fresh : (Atom → X) → X

  -- New a. f <$> x' = [a] (f (x' @ a))

  -- modulo some subtleties, Abs captures the monadic version of И
  --   * Abs∗: n-ary version
  --   * etc...
  -- instance
  --   -- should be ≃ И
  --   Monad-Abs : Monad Abs
  --   Monad-Abs = ?

  -- _≈_ : Rel (Abs A) _
  -- x ≈ y = let 𝕔 = freshAtom in conc x 𝕔 ≡ conc y 𝕔
  --   where postulate freshAtom : Atom

  -- instance
  --   DecEq-Abs : ⦃ DecEq A ⦄ → DecEq (Abs A)
  --   DecEq-Abs ._≟_ (abs 𝕒 x) (abs 𝕓 y) = {!!}
