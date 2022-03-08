-- ** Substitution.
module ULC.Substitution {- (Atom : Set) ⦃ _ : DecEq Atom ⦄ -} where

open import ULC.Base
open import Nominal Atom

{-
_[_] : Abs Term → Term → Term
(abs 𝕒 t) [ s ] = (ƛ 𝕒 ⇒ t) · s

_[_↝_] : Term → Atom → Term → Term
t [ 𝕒 ↝ s ] = go t
  where
    go : Term → Term
    go = λ where
      (tˡ · tʳ)  → go tˡ · go tʳ
      (` 𝕓)      → if 𝕓 == 𝕒 then s else ` 𝕓
      (ƛ 𝕓 ⇒ t′) → ƛ 𝕓 ⇒ (if 𝕓 == 𝕒 then t′ else go t′)

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

  _ = (` a · (ƛ a ⇒ ` a)) [ a ↝ ` b ]
    ≡ ` b · (ƛ a ⇒ ` a)
    ∋ refl

  _ = (` a · (ƛ c ⇒ ` c · ` a)) [ a ↝ ` b ]
    ≡ (` b · (ƛ c ⇒ ` c · ` b))
    ∋ refl
-}
