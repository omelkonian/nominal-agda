-- {-# OPTIONS --allow-unsolved-metas #-}
open import Prelude.Init hiding ([_]); open SetAsType
open import Prelude.General
open import Prelude.DecEq
open import Prelude.DecLists
open import Prelude.Measurable
open import Prelude.InfEnumerable
open import Prelude.Setoid
open import Prelude.InferenceRules

-- ** Substitution.
module ULC.Substitution2 (Atom : Type) ⦃ _ : DecEq Atom ⦄ ⦃ _ : Enumerable∞ Atom ⦄ where

open import ULC.Base    Atom ⦃ it ⦄
open import ULC.Measure Atom ⦃ it ⦄ ⦃ it ⦄
open import ULC.Alpha   Atom ⦃ it ⦄ ⦃ it ⦄
open import Nominal Atom
open import Nominal.Product Atom

freshAtom : Atoms → Atom
freshAtom = proj₁ ∘ minFresh

-- ** GROWN-UP SUBSTITUTION: most robust/safe version, but sometimes too much
-- T0D0: unifying with `conc` (OPTIONAL)
-- ** optimised version, minimum amount of freshness checks
--    ∙ t̂@(abs x t) [ s ] = ƛ t̂ [ x / s ]
infix 6 _[_]
{-# TERMINATING #-}
_[_] : Abs Term → Term → Term
t̂ [ s ] = let x = freshAtom (supp t̂ ++ supp s) in
  case conc t̂ x of λ where
    (` v) → if v == x then s else (` v)
    (L · M) → (abs x L [ s ]) · (abs x M [ s ])
    (ƛ t̂′) → let x′ = freshAtom (x ∷ supp t̂ ++ supp s ++ supp t̂′) in
             ƛ x′ ⇒ (abs x (conc t̂′ x′) [ s ])
{-
  case swap x (t̂ .atom) (t̂ .term) of λ where
    (` v) → if v == x then s else (` v)
    (L · M) → (abs x L [ s ]) · (abs x M [ s ])
    (ƛ t̂′) → let x′ = freshAtom (x ∷ supp t̂ ++ supp s ++ supp t̂′) in
             ƛ x′ ⇒ (abs x (conc t̂′ x′) [ s ])
  let x↔ = swap x (t̂ .atom)
  in case t̂ .term of λ where
    (` v) → if x↔ v == x then s else (x↔ ` v)
    (L · M) → (abs x (x↔ L) [ s ]) · (abs x (x↔ M) [ s ])
    (ƛ t̂′) → let x′ = freshAtom (x ∷ supp t̂ ++ supp s ++ supp (x↔ t̂′)) in
             ƛ x′ ⇒ (abs x (conc (x↔ t̂′) x′) [ s ])
-}

-- conc-subst :
--   conc t̂ 𝕒
--   ≡ swap 𝕒 (t̂ .atom) (t̂ .term)
--   ≡⟨ ? ⟩
--   ≡ swap 𝕒 (x↔y t̂ .atom) (x↔y t̂ .term)
--   conc (x↔y t̂) 𝕒

postulate
  swap-shape⁺⁺ :
    let
      t  = conc t̂ z
      t′ = conc (swap x y t̂) z′
    in
      case t of λ where
        (L · M) → t′ ≡ swap x y L · swap x y M
        _ → ⊤

module _ {x y : Atom} {s : Term} where
  swap-subst : ∀ t̂ →
    ────────────────────────────────────────────────
    swap x y (t̂ [ s ]) ≈ (swap x y t̂) [ swap x y s ]
  swap-subst t̂@(abs a t)
    -- with 𝕩 ← minFresh (supp t̂ ++ supp s) .proj₁
    with conc t̂ (freshAtom (supp t̂ ++ supp s)) -- 𝕩
       | conc (swap x y t̂) (freshAtom (supp (swap x y t̂) ++ supp s))
       -- | swap-shape {x}{y} (t̂ .term)
       -- | swap-shape⁺⁺ {t̂}{freshAtom (supp t̂ ++ supp s)}{x}{y}
       --                {freshAtom (supp (swap x y t̂) ++ supp s)}
  ... | L · M | _ · _ -- .(swap x y L · swap x y M) | refl
    -- (L · M) → (abs x L [ s ]) · (abs x M [ s ])
    =
    let 𝕩  = freshAtom (supp t̂ ++ supp s)
        𝕩′ = freshAtom (𝕩 ∷ supp (swap x y t̂) ++ supp s)
    in begin
    --   swap x y (t̂ [ s ])
    -- ≡⟨⟩
      swap x y ((abs 𝕩 L [ s ]) · (abs 𝕩 M [ s ]))
    ≡⟨⟩
      swap x y (abs 𝕩 L [ s ]) · swap x y (abs 𝕩 M [ s ])
    ≈⟨ {!!} ⟩
      -- (swap x y (abs 𝕩′ L) [ swap x y s ]) · (swap x y (abs 𝕩′ M) [ swap x y s ])
    -- ≈⟨ {!!} ⟩
      -- (swap x y (L · M)) [ swap x y s ]
    -- ≡⟨⟩
     (swap x y t̂) [ swap x y s ]
    ∎ where open ≈-Reasoning
    -- rewrite swap-subst (abs 𝕩 L) | swap-subst (abs 𝕩 M) = {!!}
  ... | ƛ t̂′ | ƛ _ -- | _
    -- (ƛ t̂′) → let x′ = freshAtom (x ∷ supp t̂ ++ supp s ++ supp t̂′) in
    --          ƛ x′ ⇒ abs x (conc t̂′ x′) [ s ]
    =
    let 𝕩  = freshAtom (supp t̂ ++ supp s)
        𝕩′ = freshAtom (𝕩 ∷ supp t̂ ++ supp s ++ supp t̂′)
    in begin
    --   swap x y (t̂ [ s ])
    -- ≡⟨⟩
      swap x y (ƛ 𝕩′ ⇒ abs 𝕩 (conc t̂′ 𝕩′) [ s ])
      -- swap x y (ƛ 𝕩′ ⇒ abs 𝕩 (conc t̂′ 𝕩′) [ s ])
    ≈⟨ {!!} ⟩
      (swap x y t̂) [ swap x y s ]
    ∎ where open ≈-Reasoning
  ... | ` v | ` _ -- | _
    -- (` v) → if v == x then s else (` v)
    with v ≟ freshAtom (supp t̂ ++ supp s)
  ... | yes refl
    = let 𝕩 = freshAtom (supp t̂ ++ supp s) in
    begin
      swap x y s
    ≈⟨ {!!} ⟩
      (swap x y t̂) [ swap x y s ]
    ∎ where open ≈-Reasoning
  ... | no v≢x
    =
    let 𝕩 = freshAtom (supp t̂ ++ supp s)
    in begin
      swap x y (` v)
    ≈⟨ {!!} ⟩
      (swap x y t̂) [ swap x y s ]
    ∎ where open ≈-Reasoning
