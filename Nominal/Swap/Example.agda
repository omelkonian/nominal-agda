{-# OPTIONS -v nominal:100 #-}
module Nominal.Swap.Example where

open import Prelude.Init
open import Prelude.DecEq

-- ** instantiate atoms to be the natural numbers
data Atom : Set where
  `_ : โ โ Atom
unquoteDecl DecEq-Atom = DERIVE DecEq [ quote Atom , DecEq-Atom ]
open import Nominal.Swap Atom
๐ = ` 0; ๐ = ` 1

data ฮปTerm : Set where
  _-APP-_ : ฮปTerm โ ฮปTerm โ ฮปTerm
  VAR : Atom โ ฮปTerm
-- {-# TERMINATING #-}
-- unquoteDecl ฮปTermโ = DERIVE Swap [ quote ฮปTerm , ฮปTermโ ]
instance
  ฮปTermโ : Swap ฮปTerm
  ฮปTermโ .swap = ฮป ๐ ๐ โ ฮป where
    (l -APP- r) โ swap ๐ ๐ l -APP- swap ๐ ๐ r
    (VAR x)     โ VAR (swap ๐ ๐ x)

-- ** example swapping in a ฮป-term
_ = swap ๐ ๐ (VAR ๐ -APP- VAR ๐) โก VAR ๐ -APP- VAR ๐
  โ refl

-- ** derive and check ad-hoc example datatypes
record TESTR : Set where
  field atom : Atom
open TESTR

-- [T0D0] derive outside module
-- unquoteDecl TESTRโ = DERIVE Swap [ quote TESTR , TESTRโ ]
instance
  TESTRโ : Swap TESTR
  TESTRโ .swap ๐ ๐ (record {atom = x}) = record {atom = swap ๐ ๐ x}

_ = swap ๐ ๐ (record {atom = ๐}) โก record {atom = ๐} โ refl

data TEST : Set where
  ATOM : Atom โ TEST
-- unquoteDecl TESTโ = DERIVE Swap [ quote TEST , TESTโ ]
instance
  TESTโ : Swap TEST
  TESTโ .swap ๐ ๐ (ATOM x) = ATOM (swap ๐ ๐ x)

_ = swap ๐ ๐ (ATOM ๐) โก ATOM ๐
  โ refl
