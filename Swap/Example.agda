{-# OPTIONS -v nominal:100 #-}
module Swap.Example where

open import Prelude.Init
open import Prelude.DecEq

-- ** instantiate atoms to be the natural numbers
data Atom : Set where
  `_ : ℕ → Atom
unquoteDecl DecEq-Atom = DERIVE DecEq [ quote Atom , DecEq-Atom ]
open import Swap Atom ⦃ it ⦄
𝕒 = ` 0; 𝕓 = ` 1

data λTerm : Set where
  _-APP-_ : λTerm → λTerm → λTerm
  VAR : Atom → λTerm
-- {-# TERMINATING #-}
-- unquoteDecl λTerm↔ = DERIVE Swap [ quote λTerm , λTerm↔ ]
instance
  λTerm↔ : Swap λTerm
  λTerm↔ .swap = λ 𝕒 𝕓 → λ where
    (l -APP- r) → swap 𝕒 𝕓 l -APP- swap 𝕒 𝕓 r
    (VAR x)     → VAR (swap 𝕒 𝕓 x)

-- ** example swapping in a λ-term
_ = swap 𝕒 𝕓 (VAR 𝕒 -APP- VAR 𝕓) ≡ VAR 𝕓 -APP- VAR 𝕒
  ∋ refl

-- ** derive and check ad-hoc example datatypes
record TESTR : Set where
  field atom : Atom
open TESTR

-- [T0D0] derive outside module
-- unquoteDecl TESTR↔ = DERIVE Swap [ quote TESTR , TESTR↔ ]
instance
  TESTR↔ : Swap TESTR
  TESTR↔ .swap 𝕒 𝕓 (record {atom = x}) = record {atom = swap 𝕒 𝕓 x}

_ = swap 𝕒 𝕓 (record {atom = 𝕒}) ≡ record {atom = 𝕓} ∋ refl

data TEST : Set where
  ATOM : Atom → TEST
-- unquoteDecl TEST↔ = DERIVE Swap [ quote TEST , TEST↔ ]
instance
  TEST↔ : Swap TEST
  TEST↔ .swap 𝕒 𝕓 (ATOM x) = ATOM (swap 𝕒 𝕓 x)

_ = swap 𝕒 𝕓 (ATOM 𝕒) ≡ ATOM 𝕓
  ∋ refl
