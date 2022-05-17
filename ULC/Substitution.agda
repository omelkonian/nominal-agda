open import Prelude.Init
open import Prelude.DecEq

-- ** Substitution.
module ULC.Substitution {- (Atom : Set) ⦃ _ : DecEq Atom ⦄ -} where

open import ULC.Base
open import Nominal Atom

{-# TERMINATING #-}
_[_↝_] : Term → Atom → Term → Term
t₀ [ 𝕒 ↝ s ] = go t₀
  where
    go : Term → Term
    go = λ where
      (` x)    → if x == 𝕒 then s else ` x
      (t · t′) → go t · go t′
      (ƛ f)    → ƛ (mapAbs go f)

private
  _ = (` a) [ a ↝ ` b ] ≡ ` b
    ∋ refl

  _ = (` a) [ a ↝ ` b · ` b ] ≡ ` b · ` b
    ∋ refl

  _ = (` a · ` a) [ a ↝ ` b ] ≡ ` b · ` b
    ∋ refl

  _ = (` a · ` a) [ a ↝ ` b · ` b ]
    ≡ (` b · ` b) · (` b · ` b)
    ∋ refl

  -- _ = (` a · (ƛ a ⇒ ` a)) [ a ↝ ` b ]
  --   ≡ ` b · (ƛ a ⇒ ` a)
  --   ∋ {!!}

  -- _ = (` a · (ƛ c ⇒ ` c · ` a)) [ a ↝ ` b ]
  --   ≡ (` b · (ƛ c ⇒ ` c · ` b))
  --   ∋ {!!}
