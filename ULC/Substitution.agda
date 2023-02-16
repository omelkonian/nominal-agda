-- {-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --auto-inline #-}
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

freshAtom : Atoms → Atom
freshAtom = proj₁ ∘ minFresh

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
    =
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

  {-# TERMINATING #-}
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

{-
module _ {x y z : Atom} {s : Term} where

  module _ {w 𝕩′ 𝕪′} (w∉ : w L.Mem.∉ (𝕩′ ∷ 𝕪′ ∷ x ∷ y ∷ z ∷ supp t̂ ++ supp s)) where
    H₁ : conc (abs (swap x y 𝕩′) $ swap x y (conc t̂ 𝕩′ [ z / s ])) w
      ≈ swap x y (conc t̂ w [ z / s ])
    H₁ =
      begin
        conc (abs (swap x y 𝕩′) $ swap x y (conc t̂ 𝕩′ [ z / s ])) w
      ≡⟨⟩
        conc (swap x y $ abs 𝕩′ (conc t̂ 𝕩′ [ z / s ])) w
      ≈⟨ {!!} ⟩
        swap x y (conc t̂ w [ z / s ])
      ∎

    H₂ : swap x y (conc t̂ w) [ swap x y z / swap x y s ]
      ≈ conc (abs 𝕪′ (conc (swap x y t̂) 𝕪′ [ swap x y z / swap x y s ])) w
    H₂ =
      begin
        swap x y (conc t̂ w) [ swap x y z / swap x y s ]
      ≈⟨ cong-subst $ swap-conc t̂ ⟩
        conc (swap x y t̂) (swap x y w) [ swap x y z / swap x y s ]
      ≡⟨ cong (λ ◆ → (conc (swap x y t̂) ◆ [ swap x y z / swap x y s ]))
            $ swap-noop x y w (λ where 𝟘 → w∉ 𝟚; 𝟙 → w∉ 𝟛) ⟩
        conc (swap x y t̂) w [ swap x y z / swap x y s ]
      ≈⟨ {!!} ⟩
        conc (abs 𝕪′ (conc (swap x y t̂) 𝕪′ [ swap x y z / swap x y s ])) w
      ∎

  {-# TERMINATING #-}
  swap-subst : ∀ t →
    ─────────────────────────────────────────────────────────────────
    swap x y (t [ z / s ]) ≈ swap x y t [ swap x y z / swap x y s ]
  swap-subst (` v)
    = begin
      swap x y ((` v) [ z / s ])
    ≡⟨⟩
      swap x y (if v == z then s else (` v))
    ≈⟨ swap-var-helper x y v z s ⟩
      ` (if v == x then y else if v == y then x else v) [ swap x y z / swap x y s ]
    ≡⟨⟩
      swap x y (` v) [ swap x y z / swap x y s ]
    ∎
  swap-subst (L · M)
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
  swap-subst (ƛ t̂@(abs 𝕩 t))
    =
    let 𝕩′ = freshAtom (z ∷ supp t̂ ++ supp s)
        𝕪′ = freshAtom (swap x y z ∷ supp (swap x y t̂) ++ supp (swap x y s))
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
         conc (abs (swap x y 𝕩′) $ swap x y (conc t̂ 𝕩′ [ z / s ])) w
       ≈⟨ H₁ {t̂ = t̂} w∉ ⟩
         swap x y (conc t̂ w [ z / s ])
       ≈⟨ swap-subst (conc t̂ w) ⟩ -- TERMINATING!
         (swap x y (conc t̂ w) [ swap x y z / swap x y s ])
       ≈⟨ H₂ {t̂ = t̂} w∉ ⟩
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

-- {-
-- -- specialized version of `mapAbs` for Term
-- mapAbs-Term : (x' : Abs Term) → (∀ (t : Term) → t ≺ᵐ x' → Term) → Abs Term
-- mapAbs-Term x' f =
--   let a , _ = fresh (supp x' ++ supp?? f)
--   in abs a (f (conc x' a) (conc≺ x' a))

-- -- ⋯ (ƛ f) → ƛ mapAbs _[ 𝕒 / s ] f

-- -- capture-avoiding application
-- conc† : Abs Term → Atom → Term
-- conc† f@(abs x t) y =
--   let z , _ = fresh (y ∷ supp f)
--   in conc (⦅ x ↔ z ⦆ f) y
-- -}

-- -- -- {-# TERMINATING #-}
-- -- -- cong-subst : t̂ ≈ t̂′ → t̂ [ M ] ≈ t̂′ [ M ]
-- -- -- cong-subst {t̂@(abs x t)}{t̂′} (xs , p)
-- -- --   with p x {!!} | conc t̂ x | conc t̂′ x
-- -- -- ... | eq | k | l
-- -- --   = {!!}

-- -- -- subst-swap-no : z ≢ x → z ≢ y → (` y) [ swap x y z / N ] ≈ ` y
-- -- -- subst-swap-no {z}{x}{y}{N} z≢x z≢y
-- -- --   rewrite dec-no (z ≟ x) z≢x .proj₂
-- -- --   rewrite dec-no (z ≟ y) z≢y .proj₂
-- -- --   -- y [ z / N ] ≈ y
-- -- --   rewrite dec-no (y ≟ z) (≢-sym z≢y) .proj₂
-- -- --   -- y ≈ y
-- -- --   = ≈-refl

-- -- -- subst-noop : w ∉ (Atoms ∋ x ∷ y ∷ z ∷ [])
-- -- --            → (` w) [ swap x y z / N ] ≈ (` w)
-- -- -- subst-noop {w}{x}{y}{z} w∉
-- -- --   with z ≟ x
-- -- -- ... | yes refl
-- -- --   rewrite dec-no (w ≟ y) (λ where refl → w∉ 𝟙) .proj₂
-- -- --   = ≈-refl
-- -- -- ... | no _
-- -- --   with z ≟ y
-- -- -- ... | yes refl
-- -- --   rewrite dec-no (w ≟ x) (λ where refl → w∉ 𝟘) .proj₂
-- -- --   = ≈-refl
-- -- -- ... | no _
-- -- --   rewrite dec-no (w ≟ z) (λ where refl → w∉ 𝟚) .proj₂
-- -- --   = ≈-refl

-- -- -- -- ≢-cong-swap : z ≢ z′ → swap x y z ≢ swap x y z′
-- -- -- -- counter-example:         x ≢ z
-- -- -- --                 swap x z x ≡ swap x y z

-- -- -- subst-with-swap : ∀ x y z N → swap x y (` z) [ swap x y z / N ] ≡ N
-- -- -- subst-with-swap x y z N
-- -- --   with z ≟ x
-- -- -- ... | yes refl
-- -- --   -- swap x y (` x) [ swap x y z / N ] ≡ N
-- -- --   rewrite swapˡ x y
-- -- --   -- y [ y / N ] ≡ N
-- -- --   rewrite ≟-refl y
-- -- --   -- N ≡ N
-- -- --   = refl
-- -- -- ... | no  z≢x
-- -- --   -- swap x y (` z) [ swap x y z / N ] ≡ N
-- -- --   with z ≟ y
-- -- -- ... | yes refl
-- -- --   -- swap x y (` y) [ swap x y y / N ] ≡ N
-- -- --   rewrite swapʳ x y
-- -- --   -- x [ x / N ] ≡ N
-- -- --   rewrite ≟-refl x
-- -- --   -- N ≡ N
-- -- --   = refl
-- -- -- ... | no z≢y
-- -- --   -- ` z [ z / N ] ≡ N
-- -- --   rewrite ≟-refl z
-- -- --   -- N ≡ N
-- -- --   = refl

-- -- -- mutual
-- -- --   conc-subst : conc t̂ x [ y / M ] ≈ conc (t̂ [ y / M ]↑) x
-- -- --   conc-subst {t̂@(abs 𝕩 t)}{x}{y}{M} =
-- -- --     begin
-- -- --       conc t̂ x [ y / M ]
-- -- --     ≡⟨⟩
-- -- --     --   swap x 𝕩 t [ y / M ]
-- -- --     -- ≈⟨ {!!} ⟩
-- -- --       conc t̂ x [ y / M ]
-- -- --     ≈⟨ {!!} ⟩
-- -- --       conc (swap x w_ t̂) x [ swap x w_ y / swap x w_ M ]
-- -- --     ≡˘⟨ cong (λ ◆ → conc (swap x w_ t̂) ◆ [ swap x w_ y / swap x w_ M ])
-- -- --           $ swapʳ x w_ ⟩
-- -- --       conc (swap x w_ t̂) (swap x w_ w_) [ swap x w_ y / swap x w_ M ]
-- -- --     ≈˘⟨ {!!} ⟩
-- -- --       swap x w_ (conc t̂ w_) [ swap x w_ y / swap x w_ M ]
-- -- --     ≈˘⟨ {!!} ⟩
-- -- --       swap x w_ (conc t̂ w_ [ y / M ])
-- -- --     ≡⟨⟩
-- -- --       conc (abs w_ $ conc t̂ w_ [ y / M ]) x
-- -- --     ≡⟨⟩
-- -- --       conc (t̂ [ y / M ]↑) x
-- -- --     ∎ where w_ = freshAtom (y ∷ supp t̂ ++ supp M)

-- -- --   {-# TERMINATING #-}
-- -- --   cong-subst : t ≈ t′ → t [ z / M ] ≈ t′ [ z / M ]
-- -- --   cong-subst ν≡ = ≈-refl
-- -- --   cong-subst (ξ≡ p q) = ξ≡ (cong-subst p) (cong-subst q)
-- -- --   cong-subst {ƛ t̂@(abs x t)}{ƛ t̂′@(abs x′ t′)}{z}{M} (ζ≡ (xs , p)) = ζ≡ (xs , QED)
-- -- --     where
-- -- --       QED : ∀ 𝕩 → 𝕩 L.Mem.∉ xs
-- -- --           → conc (t̂ [ z / M ]↑) 𝕩 ≈ conc (t̂′ [ z / M ]↑) 𝕩
-- -- --       QED 𝕩 𝕩∉ = qed
-- -- --         where
-- -- --           IH : conc t̂ 𝕩 ≈ conc t̂′ 𝕩
-- -- --           IH = p 𝕩 𝕩∉

-- -- --           IH′ : conc t̂ 𝕩 [ z / M ] ≈ conc t̂′ 𝕩 [ z / M ]
-- -- --           IH′ = cong-subst IH

-- -- --           qed : conc (t̂ [ z / M ]↑) 𝕩 ≈ conc (t̂′ [ z / M ]↑) 𝕩
-- -- --           qed =
-- -- --             begin
-- -- --               conc (t̂ [ z / M ]↑) 𝕩
-- -- --             ≈˘⟨ conc-subst {t̂ = t̂} ⟩
-- -- --               conc t̂ 𝕩 [ z / M ]
-- -- --             ≈⟨ IH′ ⟩
-- -- --               conc t̂′ 𝕩 [ z / M ]
-- -- --             ≈⟨ conc-subst {t̂ = t̂′} ⟩
-- -- --               conc (t̂′ [ z / M ]↑) 𝕩
-- -- --             ∎

-- -- --   swap-subst-FAIL :
-- -- --     ─────────────────────────────────────────────────────────────────
-- -- --     swap x y (N [ z / M ]) ≈ (swap x y N) [ swap x y z / swap x y M ]
-- -- --     -- swap x y (N [ z / 0 ]) ≈ (swap x y N) [ swap x y z / 0 ]
-- -- --     -- swap x y (N [ x / 0 ]) ≈ (swap x y N) [ swap x y x / 0 ]
-- -- --     -- swap x y (N [ x / 0 ]) ≈ (swap x y N) [ y / 0 ]
-- -- --     -- swap x y ((x, y) [ x / 0 ]) ≈ (swap x y (x,y)) [ y / 0 ]
-- -- --     -- swap x y (0, y) ≈ (y,x) [ y / 0 ]
-- -- --     -- (0, x) ≈ (0, x)
-- -- --   swap-subst-FAIL {x}{y}{` w}{z}{M}
-- -- --     with x ≟ y
-- -- --   swap-subst-FAIL {x}{y}{N@(` w)}{z}{M} | yes refl
-- -- --   -- swap x x (N [ z / M ]) ≈ (swap x x N) [ swap x x z / swap x x M ]
-- -- --     = begin
-- -- --       swap x x (N [ z / M ])
-- -- --     ≈⟨ swap-id ⟩
-- -- --       N [ z / M ]
-- -- --     ≈˘⟨ cong-subst-/ʳ swap-id ⟩
-- -- --       N [ z / swap x x M ]
-- -- --     ≈˘⟨ cong-subst-/ˡ swap-id ⟩
-- -- --       N [ swap x x z / swap x x M ]
-- -- --     ≈˘⟨ cong-substˡ swap-id ⟩
-- -- --       (swap x x N) [ swap x x z / swap x x M ]
-- -- --     ∎ where
-- -- --       postulate
-- -- --         cong-subst-/ˡ : ∀ {x x′ M} → x ≈ x′ → t [ x / M ] ≈ t [ x′ / M ]
-- -- --         cong-subst-/ʳ : ∀ {x M M′} → M ≈ M′ → t [ x / M ] ≈ t [ x / M′ ]
-- -- --         cong-substˡ : ∀ {x M} → t ≈ t′ → t [ x / M ] ≈ t′ [ x / M ]
-- -- --     -- ** NEED SOME HELPER LEMMAS FOR swap-id within different parts of substitution
-- -- --     -- ** otherwise, additionally require x ≢ y
-- -- --   swap-subst-FAIL {x}{y}{` w}{z}{M} | no x≢y
-- -- --   -- swap x y (` w  [ z / M ]) ≡ (swap x y (` w)) [ swap x y z / swap x y M ]
-- -- --     with w ≟ z
-- -- --   swap-subst-FAIL {x}{y}{` w}{z}{M} | no x≢y | yes refl
-- -- --   -- swap x y (` z  [ z / M ]) ≡ (swap x y (` z)) [ swap x y z / swap x y M ]
-- -- --     rewrite ≟-refl z
-- -- --   -- swap x y M ≈ (swap x y (` z)) [ swap x y z / swap x y M ]
-- -- --     rewrite subst-with-swap x y z (swap x y M)
-- -- --   -- swap x y M ≈ swap x y M
-- -- --     = ≈-refl
-- -- --   swap-subst-FAIL {x}{y}{` w}{z}{M} | no x≢y | no w≢z
-- -- --   -- swap x y (` w) ≡ (swap x y (` w)) [ swap x y z / swap x y M ]
-- -- --     with w ≟ x
-- -- --   swap-subst-FAIL {x}{y}{` w}{z}{M} | no x≢y | no w≢z | yes refl
-- -- --   -- swap x y (` x) ≡ (swap x y (` x)) [ swap x y z / swap x y M ]
-- -- --     rewrite swapˡ x y
-- -- --   -- y ≡ y [ swap x y z / swap x y M ]
-- -- --     with z ≟ x
-- -- --   ... | yes refl
-- -- --   -- y ≡ y [ y / swap x y M ]
-- -- --     rewrite ≟-refl y
-- -- --   -- y ≡ swap x y M
-- -- --     = NON-DERIVABLE -- hence require z ≢ x
-- -- --     where postulate NON-DERIVABLE : ∀ {A : Type} → A
-- -- --   ... | no z≢x
-- -- --   -- y ≡ y [ swap x y z / swap x y M ]
-- -- --     with z ≟ y
-- -- --   ... | no z≢y
-- -- --   -- y ≡ y [ z / swap x y M ]
-- -- --     rewrite dec-no (y ≟ z) (≢-sym z≢y) .proj₂
-- -- --   -- y ≡ y
-- -- --     = ≈-refl
-- -- --   ... | yes refl
-- -- --   -- y ≡ y [ x / swap x y M ]
-- -- --     with y ≟ x
-- -- --   ... | no y≢x
-- -- --   -- y ≡ y
-- -- --     = ≈-refl
-- -- --   ... | yes refl
-- -- --   -- y ≡ swap x y M
-- -- --     = NON-DERIVABLE -- hence require y ≢ x (OPTIONAL)
-- -- --     where postulate NON-DERIVABLE : ∀ {A : Type} → A
-- -- --   swap-subst-FAIL {x}{y}{` w}{z}{M} | no x≢y | no w≢z | no w≢x
-- -- --   -- swap x y (` w) ≡ (swap x y (` w)) [ swap x y z / swap x y M ]
-- -- --     with w ≟ y
-- -- --   ... | no w≢y
-- -- --   -- ` w ≡ ` w [ swap x y z / swap x y M ]
-- -- --     = TODO -- holds because w ∉ {x, y, z}
-- -- --     where postulate TODO : ` w ≈ (` w) [ swap x y z / swap x y M ]
-- -- --   ... | yes refl
-- -- --   -- swap x y (` y) ≡ (swap x y (` y)) [ swap x y z / swap x y M ]
-- -- --     rewrite swapʳ x y
-- -- --   -- x ≡ x [ swap x y z / swap x y M ]
-- -- --     with z ≟ x
-- -- --   ... | yes refl
-- -- --   -- x ≡ x [ y / swap x y M ]
-- -- --     rewrite dec-no (x ≟ y) x≢y .proj₂
-- -- --   -- x ≡ x
-- -- --     = ≈-refl
-- -- --   ... | no z≢x
-- -- --   -- x ≡ x [ swap x y z / swap x y M ]
-- -- --     with z ≟ y
-- -- --   ... | no z≢y
-- -- --   -- x ≡ x [ z / swap x y M ]
-- -- --     rewrite dec-no (x ≟ z) (≢-sym z≢x) .proj₂
-- -- --   -- x ≡ x
-- -- --     = ≈-refl
-- -- --   ... | yes refl
-- -- --   -- x ≡ x [ x / swap x y M ]
-- -- --     rewrite ≟-refl x
-- -- --   -- x ≡ swap x y M
-- -- --     = NON-DERIVABLE -- hence require z ≢ y
-- -- --     where postulate NON-DERIVABLE : ∀ {A : Type} → A
-- -- --   swap-subst-FAIL {N = _} = TODO
-- -- --     where postulate TODO : ∀ {A : Type} → A

-- -- --   swap-subst :
-- -- --     z ∉ (Atoms ∋ x ∷ y ∷ [])
-- -- --     ────────────────────────────────────────────────────────
-- -- --     swap x y (N [ z / M ]) ≈ (swap x y N) [ z / swap x y M ]
-- -- --   swap-subst {z}{x}{y}{` w} z∉
-- -- --   -- swap x y (` w  [ z / M ]) ≡ (swap x y (` w)) [ z / swap x y M ]
-- -- --     with w ≟ z
-- -- --   swap-subst {z}{x}{y}{` w} z∉ | yes refl
-- -- --   -- swap x y (` z  [ z / M ]) ≡ (swap x y (` z)) [ z / swap x y M ]
-- -- --     rewrite swap-noop x y z z∉
-- -- --   -- swap x y (` z  [ z / M ]) ≡ (` z) [ z / swap x y M ]
-- -- --     rewrite ≟-refl z
-- -- --   -- swap x y M ≡ swap x y M
-- -- --     = ≈-refl
-- -- --   swap-subst {z}{x}{y}{` w} z∉ | no w≢z
-- -- --   -- swap x y (` w) ≡ (swap x y (` w)) [ z / swap x y M ]

-- -- --     with w ∈? (Atoms ∋ x ∷ y ∷ [])
-- -- --   ... | yes 𝟘
-- -- --   -- swap x y (` x) ≡ (swap x y (` x)) [ z / swap x y M ]
-- -- --     rewrite swapˡ x y
-- -- --   -- y ≡ y [ z / swap x y M ]
-- -- --     rewrite dec-no (y ≟ z) (λ where refl → z∉ 𝟙) .proj₂
-- -- --   -- y ≡ y
-- -- --     = ≈-refl
-- -- --   ... | yes 𝟙
-- -- --   -- swap x y (` y) ≡ (swap x y (` y)) [ z / swap x y M ]
-- -- --     rewrite swapʳ x y
-- -- --   -- x ≡ x [ z / swap x y M ]
-- -- --     rewrite dec-no (x ≟ z) (λ where refl → z∉ 𝟘) .proj₂
-- -- --   -- x ≡ x
-- -- --     = ≈-refl
-- -- --   ... | no w∉xy
-- -- --     rewrite swap-noop x y w w∉xy
-- -- --   -- ` w ≡ ` w [ z / swap x y M ]
-- -- --     rewrite dec-no (w ≟ z) w≢z .proj₂
-- -- --   -- ` w ≡ ` w
-- -- --     = ≈-refl

-- -- --   swap-subst {N = L · R} z∉
-- -- --   -- x↔y ((L · R) [z/M]) ≈ (x↔y (L · R) [z/x↔y M]
-- -- --   -- x↔y (L[z/M] · R[z/M]) ≈ (x↔y L · x↔y R) [z/x↔y M]
-- -- --   -- x↔y (L[z/M]) · x↔y (R[z/M]) ≈ (x↔y L) [z/x↔y M] · (x↔y R) [z/x↔y M]
-- -- --     = ξ≡ (swap-subst {N = L} z∉) (swap-subst {N = R} z∉)

-- -- --   swap-subst {z}{x}{y}{ƛ t̂}{M} z∉
-- -- --     = ζ≡ (-, QED)
-- -- --   -- x↔y (ƛ t̂ [z/M]) ≈ (x↔y (ƛ t̂) [z/x↔y M]
-- -- --   -- let w , _ = minFresh (z ∷ supp t̂ ++ supp M)
-- -- --   -- x↔y (ƛ w ⇒ conc t̂ w [z/M]) ≈ (ƛ (x↔y t̂)) [z/x↔y M]
-- -- --   -- let v , _ = minFresh (z ∷ supp (x↔y t̂) ++ supp M)
-- -- --   -- x↔y (ƛ w ⇒ conc t̂ w [z/M]) ≈ (ƛ v ⇒ conc (x↔y t̂) v [z/x↔y M])
-- -- --   -- f@(ƛ x↔y w ⇒ x↔y (conc t̂ w [z/M])) ≈ g@(ƛ v ⇒ conc (x↔y t̂) v [z/x↔y M])
-- -- --     where
-- -- --       x↔y↓ = (Atom → Atom) ∋ swap x y
-- -- --       x↔y = (Term → Term) ∋ swap x y
-- -- --       x↔y↑ = (Abs Term → Abs Term) ∋ swap x y

-- -- --       _w = minFresh (z ∷ supp t̂ ++ supp M) .proj₁
-- -- --       w∉ = minFresh (z ∷ supp t̂ ++ supp M) .proj₂
-- -- --       _v = minFresh (z ∷ supp (x↔y↑ t̂) ++ supp (x↔y M)) .proj₁
-- -- --       v∉ = minFresh (z ∷ supp (x↔y↑ t̂) ++ supp (x↔y M)) .proj₂

-- -- --       f = abs (x↔y↓ _w) $ x↔y (conc t̂ _w [ z / M ])
-- -- --       g = abs _v $ conc (x↔y↑ t̂) _v [ z / x↔y M ]

-- -- --   -- f@(ƛ x↔y w ⇒ x↔y (conc t̂[z/M] w[z/M]) ≈ g@(ƛ v ⇒ conc (x↔y t̂) v [x↔y z/x↔y M])
-- -- --   -- f@(ƛ x↔y w ⇒ conc (x↔y t̂[z/M]) (x↔y w[z/M]) ≈ g@(ƛ v ⇒ conc (x↔y t̂) v [x↔y z/x↔y M])

-- -- --   -- И (λ 𝕩 → conc f 𝕩 ≈ conc g 𝕩)
-- -- --   -- ∃ ⦃x,y⦄ → ∀ 𝕩 → 𝕩 ∉ ⦃x,y⦄ → conc f 𝕩 ≈ conc g 𝕩
-- -- --       QED : ∀ 𝕩 → 𝕩 ∉ (Atoms ∋ x ∷ y ∷ z ∷ []) → conc f 𝕩 ≈ conc g 𝕩
-- -- --       QED 𝕩 𝕩∉
-- -- --   -- conc (x↔y t̂[z/M]) (𝕩[z/M]) ≈ conc (x↔y t̂) 𝕩 [x↔y z/x↔y M]
-- -- --   -- conc (x↔y t̂[z/M]) 𝕩 ≈ conc (x↔y t̂)[x↔y z/x↔y M] 𝕩
-- -- --   -- conc (x↔y t̂[z/M]) 𝕩 ≈ conc (x↔y t̂[z/M]) 𝕩
-- -- --         = begin
-- -- --           conc f 𝕩
-- -- --         ≡⟨⟩
-- -- --           conc (abs (x↔y↓ _w) $ x↔y (conc t̂ _w [ z / M ])) 𝕩
-- -- --         ≡⟨⟩
-- -- --           swap 𝕩 (x↔y↓ _w) (x↔y (conc t̂ _w [ z / M ]))
-- -- --         ≈⟨ cong-swap $ swap-subst {N = conc t̂ _w} {M = M} z∉ ⟩
-- -- --           swap 𝕩 (x↔y↓ _w) ((x↔y (conc t̂ _w)) [ z / x↔y M ])
-- -- --         ≈⟨ cong-swap
-- -- --          $ cong-subst {t = x↔y (conc t̂ _w)} {t′ = conc (x↔y↑ t̂) (x↔y↓ _w)}
-- -- --          $ swap-conc t̂
-- -- --          ⟩
-- -- --           swap 𝕩 (x↔y↓ _w) (conc (x↔y↑ t̂) (x↔y↓ _w) [ z / x↔y M ])
-- -- --         ≈⟨ {!!} ⟩
-- -- --           swap 𝕩 _v (conc (x↔y↑ t̂) _v) [ z / swap 𝕩 _v (x↔y M) ]
-- -- --         ≈˘⟨ swap-subst {N = conc (x↔y↑ t̂) _v} {M = x↔y M} z∉′ ⟩
-- -- --           swap 𝕩 _v (conc (x↔y↑ t̂) _v [ z / x↔y M ])
-- -- --         ≡⟨⟩
-- -- --           conc (abs _v $ conc (x↔y↑ t̂) _v [ z / x↔y M ]) 𝕩
-- -- --         ≡⟨⟩
-- -- --           conc g 𝕩
-- -- --         ∎ where
-- -- --           z∉′ : z ∉ (Atoms ∋ 𝕩 ∷ _v ∷ [])
-- -- --           z∉′ = λ where 𝟘 → 𝕩∉ 𝟚
-- -- --                         (there (here z≡v)) → v∉ (here $ sym z≡v)
