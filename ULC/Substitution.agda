{-# OPTIONS --allow-unsolved-metas #-}
-- {-# OPTIONS --auto-inline #-}
open import Prelude.Init hiding ([_]); open SetAsType
open L.Mem
open import Prelude.General
open import Prelude.DecEq
-- open import Prelude.Lists.Dec
-- open import Prelude.Measurable
open import Prelude.InfEnumerable
open import Prelude.Setoid
open import Prelude.InferenceRules

-- ** Substitution.
module ULC.Substitution (Atom : Type) ⦃ _ : DecEq Atom ⦄ ⦃ _ : Enumerable∞ Atom ⦄ where

open import ULC.Base    Atom ⦃ it ⦄
open import ULC.Measure Atom ⦃ it ⦄ ⦃ it ⦄
open import ULC.Alpha   Atom ⦃ it ⦄ ⦃ it ⦄
open import Nominal Atom
open import Nominal.Product Atom

-- enforce the Barendregt convention: no shadowing, distinct bound variables
{-# TERMINATING #-}
barendregt : Op₁ Term
barendregt = go []
  where
    go : List Atom → Op₁ Term
    go xs = λ where
      (` x)     → ` x
      (l · r)   → go xs l · go xs r
      (ƛ x ⇒ t) → let x′ = freshAtom (xs ++ supp t)
                  in ƛ x′ ⇒ go (x ∷ xs) (swap x′ x t)

infix 6 _[_/_]
{-# TERMINATING #-}
_[_/_] : Term → Atom → Term → Term
(` x) [ 𝕒 / N ] = if x == 𝕒 then N else ` x
(L · M) [ 𝕒 / N ] =
  let L′ = L [ 𝕒 / N ]
      M′ = M [ 𝕒 / N ]
  in L′ · M′
(ƛ t̂) [ 𝕒 / N ] =
  -- let y = fresh-var (𝕒 , t̂ , N)
  let y = freshAtom (𝕒 ∷ supp t̂ ++ supp N)
  in ƛ y ⇒ conc t̂ y [ 𝕒 / N ]

infix 6 _[_]
_[_] : Abs Term → Term → Term
(abs x t) [ s ] = (ƛ x ⇒ t) [ x / s ]

infix 6 _[_/_]↑
_[_/_]↑ : Abs Term → Atom → Term → Abs Term
(abs 𝕒 t) [ x / N ]↑ = unƛ $ (ƛ 𝕒 ⇒ t) [ x / N ]

{- ** well-founded version
t₀ [ 𝕒 / s ] = ≺-rec _ go t₀
  module ∣Substitution∣ where
    go : ∀ x → (∀ y → y ≺ x → Term) → Term
    go x rec with x
    ... | ` x   = if x == 𝕒 then s else ` x
    ... | l · m = rec l (l ·≺ˡ m) · rec m (l ·≺ʳ m)
    -- Cannot simply use `ƛ (mapAbs go f)` here; need well-founded recursion
    -- ... | ƛ f   = ƛ mapAbs-Term f (λ t t≺ → rec t t≺)
    ... | ƛ f =
      let y , _ = fresh (nub $ 𝕒 ∷ supp f ++ supp s)
      in  ƛ y ⇒ rec (conc f y) (conc≺ f y)
-}

-- ** postulate equivariance of substitution for now...
postulate swap-subst : Equivariant _[_/_]
-- swap-subst = ? -- equivariant _[_/_]

-- ** we will also need the following lemmas for proving Reduction.sub-par (β case)

subst-commute : N [ x / L ] [ y / M [ x / L ] ] ≈ N [ y / M ] [ x / L ]
subst-commute {` n} {x} {L} {y} {M}
  with n ≟ x | n ≟ y
... | yes refl | yes refl
  -- exclude with x ≠ y
  = {!subst-commute !}
... | yes refl | no n≠y
  rewrite ≟-refl n
  = {!!}
  -- prove with y ♯ L
... | no n≠x | yes refl
  rewrite ≟-refl n
  = ≈-refl
... | no n≠x | no n≠y
  rewrite dec-no (n ≟ x) n≠x .proj₂
        | dec-no (n ≟ y) n≠y .proj₂
        = ≈-refl
subst-commute {Nˡ · Nʳ} {x} {L} {y} {M}
  = ξ≡ (subst-commute {Nˡ}) (subst-commute {Nʳ})
subst-commute {ƛ t̂} {x} {L} {y} {M}
  with xˡ ← freshAtom (x ∷ supp t̂ ++ supp L)
  -- (ƛ xˡ ⇒ conc t̂ xˡ [ x / L ]) [ y / M [ x / L ] ]
  with yˡ ← freshAtom (y ∷ supp (abs xˡ $ conc t̂ xˡ [ x / L ]) ++ supp (M [ x / L ]))
  -- ƛ yˡ ⇒ conc (abs xˡ $ conc t̂ xˡ [ x / L ]) yˡ [ y / M [ x / L ] ]
  --      ≡ conc t̂ yˡ [ x / L ] [ y / M [ x / L ] ]

  with yʳ ← freshAtom (y ∷ supp t̂ ++ supp M)
  -- (ƛ yʳ ⇒ conc t̂ yʳ [ y / M ]) [ x / L ]
  with xʳ ← freshAtom (x ∷ supp (abs yʳ $ conc t̂ yʳ [ y / M ]) ++ supp L)
  -- ƛ xʳ ⇒ conc (abs yʳ $ conc t̂ yʳ [ y / M ]) xʳ [ x / L ]
  --      ≡ conc t̂ xʳ [ y / M ] [ x / L ]
  = ζ≡ ({!!} , (λ z z∉ → {!!}))

postulate cong-subst : t ≈ t′ → t [ x / M ] ≈ t′ [ x / M ]

-- {-# TERMINATING #-}
swap∘subst : swap y x N [ y / M ] ≈ N [ x / M ]
swap∘subst {y} {x} {` n} {M}
  with n ≟ x | n ≟ y
... | yes refl | yes refl
  rewrite ≟-refl y
  = ≈-refl
... | yes refl | no n≠y
  rewrite ≟-refl y
  = ≈-refl
... | no n≠x | yes refl
  rewrite dec-no (x ≟ y) (≢-sym n≠x) .proj₂
  = {!!} -- prove with y ♯ N
... | no n≠x | no n≠y
  rewrite dec-no (n ≟ y) n≠y .proj₂
  = ≈-refl
swap∘subst {y} {x} {L · R} {M}
  = ξ≡ (swap∘subst {N = L}) (swap∘subst {N = R})
swap∘subst {y} {x} {ƛ t̂} {M}
{-
swap y x (ƛ z ⇒ t) [ y / M ]
≡ (ƛ swap y x z ⇒ swap y x t) [ y / M ]
≡ let zˡ = freshAtom (y ∷ supp (swap y z (ƛ z ⇒ t) ++ supp M)
  in ƛ zˡ → conc (swap y x $ abs z t) zˡ [ y / M ]
          ≡ conc (swap y x $ abs z t) zˡ [ swap y x x / M ]
          ≡ conc (swap y x $ abs z t) (swap y x zˡ) [ swap y x x / M ]

≡ let zʳ = freshAtom (x ∷ z ∷ supp t ++ supp M)
  in ƛ zʳ → conc (ƛ z ⇒ t) zʳ [ x / M ]
≡ (ƛ z ⇒ t) [ x / M ]
∎

conc (ƛ zˡ → conc (ƛ swap y x z ⇒ swap y x t) zˡ [ y / M ]) w
≡ swap w zˡ $ conc (ƛ swap y x z ⇒ swap y x t) zˡ [ y / M ]
≡ swap w zˡ $ conc (ƛ swap y x z ⇒ swap y x t) zˡ [ swap y x x / M ]

≡ conc (swap w zˡ $ ƛ swap y x z ⇒ swap y x t) w [ y / M ]
≡ conc (ƛ swap w zˡ (swap y x z) ⇒ swap w zˡ $ swap y x t) w [ y / M ]
≡ conc (ƛ swap w zˡ (swap y x z) ⇒ swap w zˡ $ swap y x t) w [ y / M ]

≈?
≡ swap w z t [ x / M ]
≡ conc (ƛ z ⇒ t) w [ x / M ]
≡ conc (swap w zʳ $ ƛ z ⇒ t) w [ x / M ]
≡ swap w zʳ $ conc (ƛ z ⇒ t) zʳ [ x / M ]
conc (ƛ zʳ → conc (ƛ z ⇒ t) zʳ [ x / M ]) w
-}
  = ζ≡ ({!!} , λ w w∉ → {!!})
