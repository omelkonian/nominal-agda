{-# OPTIONS -v nominal:100 #-}

open import Prelude.Init hiding (swap)
open import Prelude.DecEq
open import Prelude.General

Atom = ℕ
open import Swap ℕ
open import Perm ℕ
open import Abs ℕ
𝕒 = 0; 𝕓 = 1

-- ** swapping

record TESTR : Set where
  constructor ATOM
  field atom : Atom
open TESTR
-- unquoteDecl TESTR↔ = DERIVE Swap [ quote TESTR , TESTR↔ ]
instance
  TESTR↔ : Swap TESTR
  TESTR↔ .swap 𝕒 𝕓 (record {atom = x}) = record {atom = swap 𝕒 𝕓 x}

_ : swap 𝕒 𝕓 (ATOM 𝕒) ≡ ATOM 𝕓
_ = refl

--

data TEST : Set where
  ATOM : Atom → TEST
-- unquoteDecl TEST↔ = DERIVE Swap [ quote TEST , TEST↔ ]
instance
  TEST↔ : Swap TEST
  TEST↔ .swap 𝕒 𝕓 (ATOM x) = ATOM (swap 𝕒 𝕓 x)

_ : swap 𝕒 𝕓 (TEST ∋ ATOM 𝕒) ≡ ATOM 𝕓
_ = refl

--

`ex : λTerm
`ex = VAR 𝕒 -APP- VAR 𝕓

ex↔ : swap 𝕒 𝕓 `ex ≡ VAR 𝕓 -APP- VAR 𝕒
ex↔ = refl

-- ** abstraction

-- Input a name and output two local binding scopes using that name
_ : (λ a → (abs a a , abs {A = ℕ} a a)) 𝕒
  ≡ (abs 𝕒 𝕒 , abs 𝕒 𝕒)
_ = refl

-- -- Unpack a pair of local scopes and concrete them at two names
_ : (λ (x , y) → conc x 𝕒 , conc y 𝕓) ((λ a → abs a a , abs {A = ℕ} a a) 𝕒)
   ≡ (𝕒 , 𝕓)
_ = refl

--

mutual
  data Term : Set where
    _-APP-_ : Op₂ Term
    VAR : Atom → Term
    LAM : Abs Term → Term
  -- unquoteDecl Swap-Term = DERIVE Swap [ quote Term , Swap-Term ]
  instance
    {-# TERMINATING #-}
    Swap-Term : Swap Term
    Swap-Term .swap 𝕒 𝕓 = λ where
      (t -APP- t′) → swap 𝕒 𝕓 t -APP- swap 𝕒 𝕓 t′
      (VAR x) → VAR (swap 𝕒 𝕓 x)
      (LAM f) → LAM (swap 𝕒 𝕓 f)

`𝕒∙𝕓 : Term
`𝕒∙𝕓 = VAR 𝕒 -APP- VAR 𝕓

_ : swap 𝕒 𝕓 `𝕒∙𝕓 ≡ VAR 𝕓 -APP- VAR 𝕒
_ = refl

`id : Term
`id = LAM $ abs 𝕒 (VAR 𝕒)

_ : swap 𝕒 𝕓 `id ≡ LAM (abs 𝕓 (VAR 𝕓))
_ = refl

`id∙𝕒 : Term
`id∙𝕒 = LAM (abs 𝕒 (VAR 𝕒)) -APP- VAR 𝕒


-- t = (\a.a) a
-- t↔ = swap a b t =? (\a.a) b ×××
--                 =? (\b.b) b ←——
_ : swap 𝕒 𝕓 `id∙𝕒 ≢ LAM (abs 𝕒 (VAR 𝕒)) -APP- VAR 𝕓
_ = λ ()

-- this is the expected behaviour, doesn't matter denotationally
-- only need a smarter `swap` for efficiency (e.g. using support indices)
-- e.g. in `swap a b (\{⋯a⋯b⋯}. x₁ * a * ⋯ xᵢ ⋯ * (b + ⋯))`
--      do not go inside the term as an optimization
-- FUTURE: name restriction (e.g. used in iEUTxO instead of abstraction)
_ : swap 𝕒 𝕓 `id∙𝕒 ≡ LAM (abs 𝕓 (VAR 𝕓)) -APP- VAR 𝕓
_ = refl
