{-# OPTIONS -v nominal:100 #-}
module Example where

open import Prelude.Init
open SetAsType
open L.Mem
open import Prelude.DecEq
open import Prelude.Generics hiding (`_)
open import Prelude.General
open import Prelude.Lists

-- ** instantiate atoms to be the natural numbers
data Atom : Type where
  `_ : ℕ → Atom
unquoteDecl DecEq-Atom = DERIVE DecEq [ quote Atom , DecEq-Atom ]
open import Nominal Atom ⦃ it ⦄

𝕒 = ` 0; 𝕓 = ` 1; 𝕔 = ` 2

-- ** swapping

record TESTR : Type where
  constructor ATOM
  field atom : Atom
open TESTR
-- unquoteDecl TESTR↔ = DERIVE Swap [ quote TESTR , TESTR↔ ]
unquoteDecl TESTR↔ = DERIVE-SWAP (quote Swap ∙⟦_⟧) (quote TESTR) TESTR↔
-- instance
--   TESTR↔ : Swap TESTR
--   TESTR↔ .swap 𝕒 𝕓 (record {atom = x}) = record {atom = swap 𝕒 𝕓 x}

_ = swap 𝕒 𝕓 (ATOM 𝕒) ≡ ATOM 𝕓
  ∋ refl

data TEST : Type where
  ATOM : Atom → TEST
-- unquoteDecl TEST↔ = DERIVE Swap [ quote TEST , TEST↔ ]
unquoteDecl TEST↔ = DERIVE-SWAP (quote Swap ∙⟦_⟧) (quote TEST) TEST↔
-- instance
--   TEST↔ : Swap TEST
--   TEST↔ .swap 𝕒 𝕓 (ATOM x) = ATOM (swap 𝕒 𝕓 x)

_ = swap 𝕒 𝕓 (TEST ∋ ATOM 𝕒) ≡ ATOM 𝕓
  ∋ refl

-- ** abstraction

-- Input a name and output two local binding scopes using that name
_ = (λ a → (abs a a , abs a a)) 𝕒 ≡ (abs 𝕒 𝕒 , abs 𝕒 𝕒)
  ∋ refl

-- Unpack a pair of local scopes and concrete them at two names
_ = (λ (x , y) → conc x 𝕒 , conc y 𝕓) ((λ a → abs a a , abs a a) 𝕒) ≡ (𝕒 , 𝕓)
  ∋ refl

data Term : Type where
  _-APP-_ : Op₂ Term
  VAR : Atom → Term
  LAM : Abs Term → Term
-- unquoteDecl Swap-Term = DERIVE-SWAP (quote Swap ∙⟦_⟧) (quote Term) Swap-Term
instance
  {-# TERMINATING #-}
  Swap-Term : Swap Term
  Swap-Term .swap 𝕒 𝕓 = λ where
    (t -APP- t′) → swap 𝕒 𝕓 t -APP- swap 𝕒 𝕓 t′
    (VAR x) → VAR (swap 𝕒 𝕓 x)
    (LAM f) → LAM (swap 𝕒 𝕓 f)

_ = swap 𝕒 𝕓 (VAR 𝕒 -APP- VAR 𝕓) ≡ VAR 𝕓 -APP- VAR 𝕒
  ∋ refl

`id = LAM $ abs 𝕒 (VAR 𝕒)

_ = swap 𝕒 𝕓 `id ≡ LAM (abs 𝕓 (VAR 𝕓))
  ∋ refl

`id∙𝕒 = LAM (abs 𝕒 (VAR 𝕒)) -APP- VAR 𝕒

-- t = (\a.a) a
-- t↔ = swap a b t =? (\a.a) b ×××
--                 =? (\b.b) b ←——
_ = swap 𝕒 𝕓 `id∙𝕒 ≢ LAM (abs 𝕒 (VAR 𝕒)) -APP- VAR 𝕓
  ∋ λ ()

-- this is the expected behaviour, doesn't matter denotationally
-- only need a smarter `swap` for efficiency (e.g. using support indices)
-- e.g. in `swap a b (\{⋯a⋯b⋯}. x₁ * a * ⋯ xᵢ ⋯ * (b + ⋯))`
--      do not go inside the term as an optimization
-- FUTURE: name restriction (e.g. used in iEUTxO instead of abstraction)
_ = swap 𝕒 𝕓 `id∙𝕒 ≡ LAM (abs 𝕓 (VAR 𝕓)) -APP- VAR 𝕓
  ∋ refl


-- ** freshness
_ : 𝕒 # (VAR 𝕓 -APP- VAR 𝕔)
_ = -, qed
  where
    qed : ∀ x → x ∉ 𝕓 ∷ 𝕔 ∷ [] → swap x 𝕒 (VAR 𝕓 -APP- VAR 𝕔) ≡ VAR 𝕓 -APP- VAR 𝕔
    qed x x∉ with 𝕓 ≟ x
    ... | yes refl = case x∉ (here refl) of λ ()
    ... | no  _ with 𝕔 ≟ x
    ... | yes refl = case x∉ (there $′ here refl) of λ ()
    ... | no  _    = refl

APP-injective : ∀ {L M L′ M′} → L -APP- M ≡ L′ -APP- M′ → (L ≡ L′) × (M ≡ M′)
APP-injective refl = refl , refl

VAR-injective : ∀ {x y} → VAR x ≡ VAR y → x ≡ y
VAR-injective refl = refl

f : ¬ 𝕓 # (VAR 𝕓 -APP- VAR 𝕔)
f (xs , qed) = case absurd of λ ()
  where
    H : ∀ x → x ∉ xs → x ≡ 𝕓
    H x x∉
      with swap≡ ← APP-injective (qed x x∉) .proj₁
      rewrite swapʳ x 𝕓
      = VAR-injective swap≡

    next : Op₁ Atom
    next (` n) = ` suc n

    `-injective : ∀ x y → ` x ≡ ` y → x ≡ y
    `-injective _ _ refl = refl

    toℕ : Atom → ℕ
    toℕ (` n) = n

    sumAtoms : List Atom → Atom
    sumAtoms xs = ` sum (map toℕ xs)

    x = next (sumAtoms xs)

    -- holds by definition of `sum`
    postulate x∉  : x ∉ xs
              x∉′ : next x ∉ xs

    next[x]≡x : next x ≡ x
    next[x]≡x rewrite H _ x∉′ | H x x∉ = refl

    absurd : ∃ λ n → suc n ≡ n
    absurd = -, `-injective _ _ next[x]≡x
