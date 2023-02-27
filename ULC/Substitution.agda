-- {-# OPTIONS --allow-unsolved-metas #-}
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

-- infix 6 _[_/_]↑
-- _[_/_]↑ : Abs Term → Atom → Term → Abs Term
-- (abs 𝕒 t) [ x / N ]↑ = unƛ $ (ƛ 𝕒 ⇒ t) [ x / N ]

postulate swap-subst : Equivariant _[_/_]

{- ** postulate for now...

subs : List (Atom × Term) → Op₁ Term
subs = λ where
  [] t → t
  ((𝕒 , s) ∷ σ) t → subs σ (t [ 𝕒 / s ])

sub-ξ : (L · M) [ x / N ] ≡ (L [ x / N ]) · (M [ x / N ])
sub-ξ = refl

sub-ƛ : (ƛ x ⇒ N) [ y / M ] ≡
  (let x′ = freshAtom (y ∷ x ∷ supp N ++ supp M)
   in ƛ x′ ⇒ swap x′ x N [ y / M ])
sub-ƛ = refl

sub-` : (` x) [ x / N ] ≡ N
sub-` {x} rewrite ≟-refl x = refl

sub-`-reject : x ≢ y → (` x) [ y / N ] ≡ ` x
sub-`-reject {x}{y} x≢y rewrite dec-no (x ≟ y) x≢y .proj₂ = refl

-- sub-noop : x ∉ supp t → t [ x / M ] ≈ t
-- sub-noop x∉ = {!!}

swap-var-helper : ∀ x y v z s
  → swap x y (if v == z then s else (` v))
  ≈ swap x y (` v) [ swap x y z / swap x y s ]
swap-var-helper x y v z s
  = case v ≟ z of λ where
      (yes v≡z) → ∙v≡z v≡z
      (no  v≢z) → ∙v≢z v≢z
  where
  ∙v≡z : v ≡ z
        → swap x y (if v == z then s else (` v))
        ≈ swap x y (` v) [ swap x y z / swap x y s ]
  ∙v≡z v≡z rewrite dec-yes (v ≟ z) v≡z .proj₂ | v≡z
    = ≈-reflexive $ sym $ sub-`

  ∙v≢z : v ≢ z
        → swap x y (if v == z then s else (` v))
        ≈ swap x y (` v) [ swap x y z / swap x y s ]
  ∙v≢z v≢z rewrite dec-no (v ≟ z) v≢z .proj₂
    = ≈-reflexive
    $ sym
    $ sub-`-reject
    $ swap-≢ v≢z

private
  pattern 𝟘 = here refl; pattern 𝟙 = there 𝟘
  pattern 𝟚 = there 𝟙; pattern 𝟛 = there 𝟚
open ≈-Reasoning

cong-if : ∀ {b} →
  ∙ L ≈ L′
  ∙ M ≈ M′
    ──────────────────────
    (if b then L  else M)
  ≈ (if b then L′ else M′)
cong-if {b = true} = const
cong-if {b = false} _ = id

cong-substˡ : x ≈ y → t [ x / M ] ≈ t [ y / M ]
cong-substˡ refl = ≈-refl

mutual
  {-# TERMINATING #-}
  swap-subst : ∀ {x y z : Atom} {s : Term} t →
    ─────────────────────────────────────────────────────────────────
    swap x y (t [ z / s ]) ≈ swap x y t [ swap x y z / swap x y s ]
  swap-subst {x}{y}{z}{s} t with t
  ... | ` v
    = begin
      swap x y ((` v) [ z / s ])
    ≡⟨⟩
      swap x y (if v == z then s else (` v))
    ≈⟨ swap-var-helper x y v z s ⟩
      ` (if v == x then y else if v == y then x else v) [ swap x y z / swap x y s ]
    ≡⟨⟩
      swap x y (` v) [ swap x y z / swap x y s ]
    ∎
  ... | L · M
    = begin
      swap x y ((L · M) [ z / s ])
    ≡⟨⟩
      swap x y ((L [ z / s ]) · (M [ z / s ]))
    ≡⟨⟩
      swap x y (L [ z / s ]) · swap x y (M [ z / s ])
    ≈⟨ ξ≡ (swap-subst L) (swap-subst M) ⟩
        (swap x y L [ swap x y z / swap x y s ])
      · (swap x y M [ swap x y z / swap x y s ])
    ≡⟨⟩
      (swap x y L · swap x y M) [ swap x y z / swap x y s ]
    ≡⟨⟩
      swap x y (L · M) [ swap x y z / swap x y s ]
    ∎
  ... | ƛ t̂@(abs 𝕩 t)
         --   𝕩′ ∉ z ∷ supp t̂ ++ supp s
         -- ⇒⟨ equivariance of _∉_ ⟩
         --   swap x y 𝕩′ ∉ swap x y (z ∷ supp t̂ ++ supp s)
         -- ⇒⟨ equivariance on 𝕩′ ⟩
         --   𝕩′ ∉ -//-
         --   ─────────────────────────────────────────────
         --   ✓ swap x y 𝕩′ ∉ swap x y (z ∷ supp t̂ ++ supp s)
         --     𝕩′ ∉ swap x y (z ∷ supp t̂ ++ supp s)
         --   ✖ 𝕩′ ∉ swap x y (z ∷ supp t̂ ++ supp s)
    = {!!}
  {-
    let 𝕩′ , x∉ = minFresh (z ∷ supp t̂ ++ supp s)
        𝕪′ , y∉ = minFresh (swap x y z ∷ supp (swap x y t̂) ++ supp (swap x y s))

        cur-supp : Atoms
        cur-supp = swap x y z ∷ supp (swap x y t̂) ++ supp (swap x y s)

        x∉′ : swap x y 𝕩′ ∉ cur-supp
        x∉′ = λ where
          (here eq) → swap-≢ (x∉ ∘ here) eq
          (there x∈) → case ∈-++⁻ (supp $ swap x y t̂) x∈ of λ where
            (inj₁ x∈) → -- x∈ : swap x y 𝕩′ ∈ supp (swap x y t̂)
                        -- ⇒? 𝕩′ ∈ supp t̂
              {!!}
            (inj₂ x∈) → -- x∈ : swap x y 𝕩′ ∈ supp (swap x y s)
                        -- ⇒? 𝕩′ ∈ supp s
              {!!}

        w∉′ : w ∉ swap x y 𝕩′ ∷ cur-supp
        w∉′ = {!!}

        y∉′ : 𝕪′ ∉ cur-supp
        y∉′ = y∉

        w∉″ : w ∉ 𝕪′ ∷ cur-supp
        w∉″ = {!!}
    in begin
      swap x y ((ƛ t̂) [ z / s ])
    ≡⟨⟩
      swap x y (ƛ 𝕩′ ⇒ conc t̂ 𝕩′ [ z / s ])
    ≡⟨⟩
      ƛ swap x y 𝕩′ ⇒ swap x y (conc t̂ 𝕩′ [ z / s ])
    ≡⟨⟩
      (ƛ (abs (swap x y 𝕩′) $ swap x y (conc t̂ 𝕩′ [ z / s ])))
    ≈⟨ ζ≡ ((𝕩′ ∷ 𝕪′ ∷ x ∷ y ∷ z ∷ supp t̂ ++ supp s) , λ w w∉ →
      -- this is precisely the Abs-isomorphism proof for _×_!
      begin
        conc (abs (swap x y 𝕩′) $
          swap x y (conc t̂ 𝕩′ [ z / s ])) w
      ≈⟨ cong-conc∘abs $ swap-subst (conc t̂ 𝕩′) ⟩
        conc (abs (swap x y 𝕩′) $
          swap x y (conc t̂ 𝕩′) [ swap x y z / swap x y s ]) w
      ≈⟨ (cong-conc∘abs $ cong-subst $ swap-conc t̂) ⟩
        conc (abs (swap x y 𝕩′) $
          conc (swap x y t̂) (swap x y 𝕩′) [ swap x y z / swap x y s ]) w
      ≈⟨ conc-fresh {t̂ = swap x y t̂} x∉′ w∉′ ⟩
        conc (swap x y t̂) w [ swap x y z / swap x y s ]
      ≈˘⟨ conc-fresh {t̂ = swap x y t̂} y∉′ w∉″ ⟩
        conc (abs 𝕪′ (conc (swap x y t̂) 𝕪′ [ swap x y z / swap x y s ])) w
      ∎)
    ⟩
      (ƛ (abs 𝕪′ (conc (swap x y t̂) 𝕪′ [ swap x y z / swap x y s ])))
    ≡⟨⟩
      ƛ 𝕪′ ⇒ conc (swap x y t̂) 𝕪′ [ swap x y z / swap x y s ]
    ≡⟨⟩
      (ƛ swap x y 𝕩 ⇒ swap x y t) [ swap x y z / swap x y s ]
    ≡⟨⟩
      swap x y (ƛ t̂) [ swap x y z / swap x y s ]
    ∎
  -}

  -- {-# TERMINATING #-}
  postulate cong-subst : t ≈ t′ → t [ x / M ] ≈ t′ [ x / M ]
{-
  cong-subst ν≡ = ≡α-refl _
  cong-subst (ξ≡ eqˡ eqʳ) = ξ≡ (cong-subst eqˡ) (cong-subst eqʳ)
  cong-subst {ƛ t̂}{ƛ t̂′}{x}{M} (ζ≡ (xs , eq)) =
    let 𝕩 , x∉ = minFresh (x ∷ supp t̂ ++ supp M)
        𝕪 , y∉ = minFresh (x ∷ supp t̂′ ++ supp M)

        ys = 𝕩 ∷ 𝕪 ∷ x ∷ supp t̂ ++ supp t̂′ ++ supp M ++ xs
        ysˡ = 𝕩 ∷ x ∷ supp t̂ ++ supp M
        ysʳ = 𝕪 ∷ x ∷ supp t̂′ ++ supp M
        ys⊆ˡ : ysˡ ⊆ ys
        ys⊆ˡ = λ where
          (here p) → here p
          (there (here p)) → there $′ there $′ here p
          (there (there x∈)) → case ∈-++⁻ (supp t̂) x∈ of λ where
            (inj₁ x∈) → there $′ there $′ there $′ ∈-++⁺ˡ x∈
            (inj₂ x∈) → there $′ there $′ there $′
                        ∈-++⁺ʳ (supp t̂) $ ∈-++⁺ʳ (supp t̂′) $ ∈-++⁺ˡ x∈
        ys⊆ʳ : ysʳ ⊆ ys
        ys⊆ʳ = λ where
          (here p) → there $′ here p
          (there (here p)) → there $′ there $′ here p
          (there (there x∈)) → case ∈-++⁻ (supp t̂′) x∈ of λ where
            (inj₁ x∈) → there $′ there $′ there $′
                        ∈-++⁺ʳ (supp t̂) $ ∈-++⁺ˡ x∈
            (inj₂ x∈) → there $′ there $′ there $′
                        ∈-++⁺ʳ (supp t̂) $ ∈-++⁺ʳ (supp t̂′) $ ∈-++⁺ˡ x∈

    in ζ≡ (ys , λ z z∉ →
    begin
      conc (abs 𝕩 $ conc t̂ 𝕩 [ x / M ]) z
    ≈⟨ conc-fresh {t̂ = t̂} x∉ (z∉ ∘ ys⊆ˡ) ⟩
      conc t̂ z [ x / M ]
    ≈⟨ cong-subst
     $ eq z
     $ z∉ ∘ there ∘′ there ∘′ there ∘′
       ∈-++⁺ʳ (supp t̂) ∘ ∈-++⁺ʳ (supp t̂′) ∘ ∈-++⁺ʳ (supp M)
     ⟩
      conc t̂′ z [ x / M ]
    ≈˘⟨ conc-fresh {t̂ = t̂′} y∉ (z∉ ∘ ys⊆ʳ) ⟩
      conc (abs 𝕪 $ conc t̂′ 𝕪 [ x / M ]) z
    ∎)
-}
  postulate
    conc-fresh :
    --   let 𝕩 = freshAtom (x ∷ supp t̂ ++ supp M) in
      ∙ 𝕩 ∉ x ∷ supp t̂ ++ supp M
      ∙ z ∉ (𝕩 ∷ x ∷ supp t̂ ++ supp M)
        ─────────────────────────────────
        conc (abs 𝕩 $ conc t̂ 𝕩 [ x / M ]) z
      ≈ conc t̂ z [ x / M ]
{-
  conc-fresh {𝕩}{x}{t̂}{M}{z} x∉ z∉ =
    begin
      conc (abs 𝕩 $ conc t̂ 𝕩 [ x / M ]) z
    ≡⟨⟩
      ⦅ z ↔ 𝕩 ⦆ (conc t̂ 𝕩 [ x / M ])
    ≈⟨ swap-subst (conc t̂ 𝕩) ⟩
      ⦅ z ↔ 𝕩 ⦆ conc t̂ 𝕩 [ ⦅ z ↔ 𝕩 ⦆ x / ⦅ z ↔ 𝕩 ⦆ M ]
    ≈⟨ cong-substˡ {t = ⦅ z ↔ 𝕩 ⦆ conc t̂ 𝕩} {M = ⦅ z ↔ 𝕩 ⦆ M} eq-x ⟩
      ⦅ z ↔ 𝕩 ⦆ conc t̂ 𝕩 [ x / ⦅ z ↔ 𝕩 ⦆ M ]
    ≈⟨ cong-substʳ {t = ⦅ z ↔ 𝕩 ⦆ conc t̂ 𝕩} {x = x} eq-M ⟩
      ⦅ z ↔ 𝕩 ⦆ conc t̂ 𝕩 [ x / M ]
    ≈⟨ cong-subst $ swap-conc t̂ ⟩
      conc (⦅ z ↔ 𝕩 ⦆ t̂) (⦅ z ↔ 𝕩 ⦆ 𝕩) [ x / M ]
    ≡⟨ cong (λ ◆ → conc (⦅ z ↔ 𝕩 ⦆ t̂) ◆ [ x / M ]) $ swapʳ z 𝕩 ⟩
      conc (⦅ z ↔ 𝕩 ⦆ t̂) z [ x / M ]
    ≈⟨ cong-subst $ cong-conc eq-t̂ z∉′ ⟩
      conc t̂ z [ x / M ]
    ∎
    where
      z∉t̂ : z ∉ supp t̂
      z∉t̂ = z∉ ∘ there ∘′ there ∘′ ∈-++⁺ˡ

      x∉t̂ : 𝕩 ∉ supp t̂
      x∉t̂ = x∉ ∘ there ∘ ∈-++⁺ˡ

      eq-x : ⦅ z ↔ 𝕩 ⦆ x ≈ x
      eq-x = swap-fresh x (λ where 𝟘 → z∉ 𝟙) (λ where 𝟘 → x∉ 𝟘)

      eq-t̂ : ⦅ z ↔ 𝕩 ⦆ t̂ ≈ t̂
      eq-t̂ = swap-fresh t̂ z∉t̂ x∉t̂

      eq-M : ⦅ z ↔ 𝕩 ⦆ M ≈ M
      eq-M = swap-fresh M (z∉ ∘ there ∘′ there ∘′ ∈-++⁺ʳ (supp t̂))
                          (x∉ ∘ there ∘′ ∈-++⁺ʳ (supp t̂))

      z∉′ : z ∉ eq-t̂ .proj₁
      z∉′ = z∉ ∘ there ∘′ there ∘′ ∈-++⁺ˡ ∘ supp-abs⊆ t̂ x∉t̂ z∉t̂

  {-# TERMINATING #-}
  cong-substʳ : M ≈ M′ → t [ x / M ] ≈ t [ x / M′ ]
  cong-substʳ {t = ` _}{x} eq = cong-if {b = _ == x} eq ≈-refl
  cong-substʳ {t = L · M} eq = ξ≡ (cong-substʳ {t = L} eq) (cong-substʳ {t = M} eq)
  cong-substʳ {M}{M′}{ƛ t̂}{x} eq =
    let 𝕩 , x∉ = minFresh (x ∷ supp t̂ ++ supp M)
        𝕪 , y∉ = minFresh (x ∷ supp t̂ ++ supp M′)
        xs = 𝕩 ∷ 𝕪 ∷ x ∷ supp t̂ ++ supp M ++ supp M′
        xsˡ = 𝕩 ∷ x ∷ supp t̂ ++ supp M
        xsʳ = 𝕪 ∷ x ∷ supp t̂ ++ supp M′
        xs⊆ˡ : xsˡ ⊆ xs
        xs⊆ˡ = λ where
          (here p) → here p
          (there (here p)) → there $′ there $′ here p
          (there (there x∈)) → case ∈-++⁻ (supp t̂) x∈ of λ where
            (inj₁ x∈) → there $′ there $′ there $′ ∈-++⁺ˡ x∈
            (inj₂ x∈) → there $′ there $′ there $′ ∈-++⁺ʳ (supp t̂) $ ∈-++⁺ˡ x∈
        xs⊆ʳ : xsʳ ⊆ xs
        xs⊆ʳ = λ where
          (here p) → there $′ here p
          (there (here p)) → there $′ there $′ here p
          (there (there x∈)) → case ∈-++⁻ (supp t̂) x∈ of λ where
            (inj₁ x∈) → there $′ there $′ there $′ ∈-++⁺ˡ x∈
            (inj₂ x∈) → there $′ there $′ there $′ ∈-++⁺ʳ (supp t̂) $ ∈-++⁺ʳ (supp M) x∈
    in
    ζ≡ (xs , λ z z∉ →
      begin
        conc (abs 𝕩 $ conc t̂ 𝕩 [ x / M ]) z
      ≈⟨ conc-fresh {t̂ = t̂} {M = M} x∉ (z∉ ∘ xs⊆ˡ) ⟩
        conc t̂ z [ x / M ]
      ≈⟨ cong-substʳ {t = conc t̂ z} eq ⟩
        conc t̂ z [ x / M′ ]
      ≈˘⟨ conc-fresh {t̂ = t̂} {M = M′} y∉ (z∉ ∘ xs⊆ʳ) ⟩
        conc (abs 𝕪 $ conc t̂ 𝕪 [ x / M′ ]) z
      ∎)
-}

-}
