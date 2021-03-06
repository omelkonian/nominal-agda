{-# OPTIONS -v nominal:100 #-}
module Example where

open import Prelude.Init
open L.Mem
open import Prelude.DecEq
open import Prelude.Generics hiding (`_)
open import Prelude.General
open import Prelude.Lists

-- ** instantiate atoms to be the natural numbers
data Atom : Set where
  `_ : β β Atom
unquoteDecl DecEq-Atom = DERIVE DecEq [ quote Atom , DecEq-Atom ]
open import Nominal Atom β¦ it β¦

π = ` 0; π = ` 1; π = ` 2

-- ** swapping

record TESTR : Set where
  constructor ATOM
  field atom : Atom
open TESTR
-- unquoteDecl TESTRβ = DERIVE Swap [ quote TESTR , TESTRβ ]
unquoteDecl TESTRβ = DERIVE-SWAP (quote Swap ββ¦_β§) (quote TESTR) TESTRβ
-- instance
--   TESTRβ : Swap TESTR
--   TESTRβ .swap π π (record {atom = x}) = record {atom = swap π π x}

_ = swap π π (ATOM π) β‘ ATOM π
  β refl

data TEST : Set where
  ATOM : Atom β TEST
-- unquoteDecl TESTβ = DERIVE Swap [ quote TEST , TESTβ ]
unquoteDecl TESTβ = DERIVE-SWAP (quote Swap ββ¦_β§) (quote TEST) TESTβ
-- instance
--   TESTβ : Swap TEST
--   TESTβ .swap π π (ATOM x) = ATOM (swap π π x)

_ = swap π π (TEST β ATOM π) β‘ ATOM π
  β refl

-- ** abstraction

-- Input a name and output two local binding scopes using that name
_ = (Ξ» a β (abs a a , abs a a)) π β‘ (abs π π , abs π π)
  β refl

-- Unpack a pair of local scopes and concrete them at two names
_ = (Ξ» (x , y) β conc x π , conc y π) ((Ξ» a β abs a a , abs a a) π) β‘ (π , π)
  β refl

data Term : Set where
  _-APP-_ : Opβ Term
  VAR : Atom β Term
  LAM : Abs Term β Term
-- unquoteDecl Swap-Term = DERIVE-SWAP (quote Swap ββ¦_β§) (quote Term) Swap-Term
instance
  {-# TERMINATING #-}
  Swap-Term : Swap Term
  Swap-Term .swap π π = Ξ» where
    (t -APP- tβ²) β swap π π t -APP- swap π π tβ²
    (VAR x) β VAR (swap π π x)
    (LAM f) β LAM (swap π π f)

_ = swap π π (VAR π -APP- VAR π) β‘ VAR π -APP- VAR π
  β refl

`id = LAM $ abs π (VAR π)

_ = swap π π `id β‘ LAM (abs π (VAR π))
  β refl

`idβπ = LAM (abs π (VAR π)) -APP- VAR π

-- t = (\a.a) a
-- tβ = swap a b t =? (\a.a) b ΓΓΓ
--                 =? (\b.b) b βββ
_ = swap π π `idβπ β’ LAM (abs π (VAR π)) -APP- VAR π
  β Ξ» ()

-- this is the expected behaviour, doesn't matter denotationally
-- only need a smarter `swap` for efficiency (e.g. using support indices)
-- e.g. in `swap a b (\{β―aβ―bβ―}. xβ * a * β― xα΅’ β― * (b + β―))`
--      do not go inside the term as an optimization
-- FUTURE: name restriction (e.g. used in iEUTxO instead of abstraction)
_ = swap π π `idβπ β‘ LAM (abs π (VAR π)) -APP- VAR π
  β refl


-- ** freshness
_ : π # (VAR π -APP- VAR π)
_ = -, qed
  where
    qed : β x β x β π β· π β· [] β swap x π (VAR π -APP- VAR π) β‘ VAR π -APP- VAR π
    qed x xβ with π β x
    ... | yes refl = case xβ (here refl) of Ξ» ()
    ... | no  _ with π β x
    ... | yes refl = case xβ (there $β² here refl) of Ξ» ()
    ... | no  _    = refl

APP-injective : β {L M Lβ² Mβ²} β L -APP- M β‘ Lβ² -APP- Mβ² β (L β‘ Lβ²) Γ (M β‘ Mβ²)
APP-injective refl = refl , refl

VAR-injective : β {x y} β VAR x β‘ VAR y β x β‘ y
VAR-injective refl = refl

f : Β¬ π # (VAR π -APP- VAR π)
f (xs , qed) = case absurd of Ξ» ()
  where
    H : β x β x β xs β x β‘ π
    H x xβ
      with swapβ‘ β APP-injective (qed x xβ) .projβ
      rewrite swapΚ³ x π
      = VAR-injective swapβ‘

    next : Opβ Atom
    next (` n) = ` suc n

    `-injective : β x y β ` x β‘ ` y β x β‘ y
    `-injective _ _ refl = refl

    toβ : Atom β β
    toβ (` n) = n

    sumAtoms : List Atom β Atom
    sumAtoms xs = ` sum (map toβ xs)

    x = next (sumAtoms xs)

    -- holds by definition of `sum`
    postulate xβ  : x β xs
              xββ² : next x β xs

    next[x]β‘x : next x β‘ x
    next[x]β‘x rewrite H _ xββ² | H x xβ = refl

    absurd : β Ξ» n β suc n β‘ n
    absurd = -, `-injective _ _ next[x]β‘x
