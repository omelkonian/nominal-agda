{-# OPTIONS -v nominal:100 #-}
module Swap.Example where

open import Prelude.Init hiding (swap)
open import Prelude.DecEq

-- ** instantiate atoms to be the natural numbers
Atom = ℕ
open import Swap ℕ ⦃ it ⦄
𝕒 = 0; 𝕓 = 1

-- ** example swapping in a λ-term
`term : λTerm
`term = VAR 𝕒 -APP- VAR 𝕓

term↔ : swap 𝕒 𝕓 `term ≡ VAR 𝕓 -APP- VAR 𝕒
term↔ = refl

-- ** derive and check ad-hoc example datatypes
record TESTR : Set where
  field atom : Atom
open TESTR

-- [T0D0] derive outside module
-- unquoteDecl TESTR↔ = DERIVE Swap [ quote TESTR , TESTR↔ ]
instance
  TESTR↔ : Swap TESTR
  TESTR↔ .swap 𝕒 𝕓 (record {atom = x}) = record {atom = swap 𝕒 𝕓 x}

_ : swap 𝕒 𝕓 (record {atom = 𝕒}) ≡ record {atom = 𝕓}
_ = refl

data TEST : Set where
  ATOM : Atom → TEST

-- [T0D0] derive outside module
-- unquoteDecl TEST↔ = DERIVE Swap [ quote TEST , TEST↔ ]

-- _ : swap 𝕒 𝕓 (ATOM 𝕒) ≡ ATOM 𝕓
-- _ = refl
