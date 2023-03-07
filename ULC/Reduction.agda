{-# OPTIONS --allow-unsolved-metas #-}
open import Prelude.Init hiding ([_]); open SetAsType
open L.Mem
open import Prelude.DecEq
open import Prelude.InfEnumerable
open import Prelude.InferenceRules
open import Prelude.Closures
open import Prelude.Decidable
open import Prelude.Functor
open import Prelude.Bifunctor
open import Prelude.Lists.Membership
open import Prelude.Lists.Dec

module ULC.Reduction (Atom : Type) ⦃ _ : DecEq Atom ⦄ ⦃ _ : Enumerable∞ Atom ⦄ where

open import Nominal          Atom ⦃ it ⦄
open import ULC.Base         Atom ⦃ it ⦄ hiding (z; x′)
open import ULC.Measure      Atom ⦃ it ⦄
open import ULC.Alpha        Atom ⦃ it ⦄
open import ULC.Substitution Atom ⦃ it ⦄

-- ** Reduction rules.
infix 0 _—→_
data _—→_ : Rel₀ Term where
  β :
      ──────────────────────────────
      (ƛ x ⇒ t) · t′ —→ t [ x / t′ ]
      -- (ƛ t̂) · t —→ t̂ [ t ] -- "grown-up" substitution

  ζ_ :
      t —→ t′
      ───────────────────
      ƛ x ⇒ t —→ ƛ x ⇒ t′

  ξ₁_ :
      t —→ t′
      ─────────────────
      t · t″ —→ t′ · t″

  ξ₂_ :
      t —→ t′
      ─────────────────
      t″ · t —→ t″ · t′
{-
postulate
  supp-conc : supp (conc t̂ y) ⊆ y ∷ supp (t̂ .term)
  supp-conc♯ : t̂ .atom ∉ supp (conc t̂ y)

{-# TERMINATING #-}
supp-[] : supp (t [ x / t′ ]) ⊆ supp t ++ supp t′
supp-[] {` y}{x}{t′}
  with y ≟ x
... | yes refl
  = ∈-++⁺ʳ _
... | no x≠y
  = λ where (here refl) → here refl
supp-[] {L · M}{x}{t′} x∈
  with ∈-++⁻ (supp (L [ x / t′ ])) (∈-nub⁻ x∈)
... | inj₁ x∈ = case ∈-++⁻ (supp L) $ supp-[] {t = L} x∈ of λ where
  (inj₁ x∈) → ∈-++⁺ˡ $ ∈-nub⁺ $ ∈-++⁺ˡ x∈
  (inj₂ x∈) → ∈-++⁺ʳ (nub $ supp L ++ supp M) x∈
... | inj₂ x∈ = case ∈-++⁻ (supp M) $ supp-[] {t = M} x∈ of λ where
  (inj₁ x∈) → ∈-++⁺ˡ $ ∈-nub⁺ $ ∈-++⁺ʳ (supp L) x∈
  (inj₂ x∈) → ∈-++⁺ʳ (nub $ supp L ++ supp M) x∈
supp-[] {t₀@(ƛ t̂@(abs _ t))}{x}{t′} {x′} x∈
  with y ← freshAtom (x ∷ supp t̂ ++ supp t′)
  with x∈ , x≢ ← ∈-filter⁻ (¬? ∘ (_≟ y)) {xs = supp (conc t̂ y [ x / t′ ])} x∈
  with ∈-++⁻ (supp $ conc t̂ y) $ supp-[] {t = conc t̂ y} x∈
... | inj₂ x∈ = ∈-++⁺ʳ (supp t₀) x∈
... | inj₁ x∈
  with x∉ ← supp-conc♯ {t̂ = t̂} {y = y}
  with supp-conc {t̂}{y} x∈
... | 𝟘 = ⊥-elim $ x≢ refl
... | there x∈′
  with x′ ≟ t̂ .atom
... | yes refl = ⊥-elim $ x∉ x∈
... | no x≢ = ∈-++⁺ˡ {xs = supp t₀}
            $ ∈-filter⁺ (¬? ∘ (_≟ t̂ .atom)) {xs = supp t} x∈′ x≢

∉-[] :
  ∙ y ∉ supp t
  ∙ y ∉ supp t′
    ───────────────────────
    y ∉ supp (t [ x / t′ ])
∉-[] {t = t} y∉ y∉′ = ∉-++⁺ y∉ y∉′ ∘ supp-[] {t = t}

fresh-—→ :
  N —→ N′
  ───────────────────────────
  (_∉ supp N) ⊆¹ (_∉ supp N′)
fresh-—→ (β {t = t}) x∉ =
  let x∉ , x∉′ = ∉-++⁻ $ ∉-nub⁻ x∉
  in ∉-[] {t = t} (∉-filter⁻ (¬? ∘ (_≟ _)) x∉ {!!}) x∉′
fresh-—→ (ζ p) x∉ =
  let x∉ = ∉-filter⁻ (¬? ∘ (_≟ _)) x∉ {!!}
  in ∉-filter⁺ (¬? ∘ (_≟ _)) $ fresh-—→ p x∉
fresh-—→ (ξ₁ p) x∉ =
  let x∉ , x∉″ = ∉-++⁻ $ ∉-nub⁻ x∉
      x∉′ = fresh-—→ p x∉
  in ∉-nub⁺ $ ∉-++⁺ x∉′ x∉″
fresh-—→ (ξ₂_ {t″ = t″} p) x∉ =
  let x∉″ , x∉ = ∉-++⁻ {xs = supp t″} $ ∉-nub⁻ x∉
      x∉′ = fresh-—→ p x∉
  in ∉-nub⁺ $ ∉-++⁺ x∉″ x∉′
-}
open ReflexiveTransitiveClosure _—→_

appL-cong :
  L —↠ L′
  ───────────────
  L · M —↠ L′ · M
appL-cong (L ∎) = L · _ ∎
appL-cong (L —→⟨ r ⟩ rs) = L · _ —→⟨ ξ₁ r ⟩ appL-cong rs

appR-cong :
  M —↠ M′
  ───────────────
  L · M —↠ L · M′
appR-cong (M ∎) = _ · M ∎
appR-cong (M —→⟨ r ⟩ rs) = _ · M —→⟨ ξ₂ r ⟩ appR-cong rs

abs-cong :
  N —↠ N′
  ───────────────────
  ƛ x ⇒ N —↠ ƛ x ⇒ N′
abs-cong (M ∎) = ƛ _ ⇒ M ∎
abs-cong (L —→⟨ r ⟩ rs) = ƛ _ ⇒ L —→⟨ ζ r ⟩ abs-cong rs

private
  postulate
    s z n m : Atom
    s≠z : s ≢ z

  infixr 2 _—→≡⟨_⟩_ _—→≡⟨⟩_
  _—→≡⟨_⟩_ : (t : Term) → t ≡ t′ → t′ —↠ t″ → t —↠ t″
  _ —→≡⟨ refl ⟩ p = p

  _—→≡⟨⟩_ : (t : Term) → t —↠ t′ → t —↠ t′
  _ —→≡⟨⟩ p = _ —→≡⟨ refl ⟩ p

  open import Prelude.General

  _ : (ƛ s ⇒ ` s) · ` z —↠ ` z
  _ = begin
      (ƛ s ⇒ ` s) · ` z
    —→⟨ β ⟩
      (` s) [ s / ` z ]
    —→≡⟨⟩
      (if s == s then ` z else ` s)
    —→≡⟨ if-true $ cong isYes $ ≟-refl s ⟩
      ` z
    ∎

  $z = freshAtom (s ∷ supp (ƛ z ⇒ ` s) ++ (z ∷ []))

  _ : (ƛ s ⇒ ƛ z ⇒ ` s) · ` z —↠ (ƛ $z ⇒ ` z)
  _ =
    begin
      (ƛ s ⇒ ƛ z ⇒ ` s) · ` z
    —→⟨ β ⟩
      (ƛ z ⇒ ` s) [ s / ` z ]
    —→≡⟨⟩
      (ƛ $z ⇒ conc (abs z $ ` s) $z [ s / ` z ])
    —→≡⟨⟩
      (ƛ $z ⇒ swap $z z (` s) [ s / ` z ])
    —→≡⟨ cong (λ ◆ → ƛ $z ⇒ (` ◆) [ s / ` z ]) $ swap-noop $z z s (λ where
         (here eq) → freshAtom∉ $ here $′ sym eq
         (there (here eq)) → s≠z eq) ⟩
      (ƛ $z ⇒ ` s [ s / ` z ])
    —→≡⟨ cong (λ ◆ → ƛ $z ⇒ ◆) $ if-true $ cong isYes $ ≟-refl s ⟩
      (ƛ $z ⇒ ` z)
    ∎

  zeroᶜ = ƛ s ⇒ ƛ z ⇒ ` z
  sucᶜ  = ƛ n ⇒ ƛ s ⇒ ƛ z ⇒ ` s · (` n · ` s · ` z)

  mkNumᶜ : ℕ → Term
  mkNumᶜ = λ where
    zero    → zeroᶜ
    (suc n) → sucᶜ · (mkNumᶜ n)

  twoᶜ  = ƛ s ⇒ ƛ z ⇒ ` s · (` s · ` z)
  fourᶜ = ƛ s ⇒ ƛ z ⇒ ` s · (` s · (` s · (` s · ` z)))
  plusᶜ = ƛ m ⇒ ƛ n ⇒ ƛ s ⇒ ƛ z ⇒ (` m · ` s · (` n · ` s · ` z))
  2+2ᶜ : Term
  2+2ᶜ = plusᶜ · twoᶜ · twoᶜ

{-
  _ : 2+2ᶜ —↠ fourᶜ
  _ =
    begin
      (plusᶜ · twoᶜ) · twoᶜ
    ≡⟨⟩
      ( (ƛ m ⇒ ƛ n ⇒ ƛ s ⇒ ƛ z ⇒ (` m · ` s · (` n · ` s · ` z)))
      · (ƛ s ⇒ ƛ z ⇒ ` s · (` s · ` z))
      ) · twoᶜ
    —→⟨ ξ₁ β ⟩
      let
        n′ = freshAtom (m ∷ n ∷ supp (ƛ s ⇒ ƛ z ⇒ (` m · ` s · (` n · ` s · ` z))) ++ supp (ƛ s ⇒ ƛ z ⇒ ` s · (` s · ` z)))
        s′ = freshAtom (m ∷ {!n ∷ ?!})
        z′ = freshAtom (m ∷ {!!})
      in
      ( ƛ n′ ⇒ ƛ s′ ⇒ ƛ z′ ⇒ {!!}
          -- ((ƛ s′ ⇒ ƛ z′ ⇒ ` s′ · (` s′ · ` z′)) · ` s′ · (` n′ · ` s′ · ` z′))
      ) · twoᶜ
    —→⟨ {!!} ⟩
    -- —→⟨ ξ₁ β ⟩
    --   ( (ƛ n ⇒ ƛ s ⇒ ƛ z ⇒ (` m · ` s · (` n · ` s · ` z))) [ m / twoᶜ ]
    --   ) · twoᶜ
    --   (ƛ n ⇒ ƛ s ⇒ ƛ z ⇒ twoᶜ · ` s · (` n · ` s · ` z)) · twoᶜ
    -- —→⟨ β ⟩
    --   ƛ s ⇒ ƛ z ⇒ twoᶜ · ` s · (twoᶜ · ` s · ` z)
    -- —→⟨ ζ ζ ξ₁ β ⟩
    --   ƛ s ⇒ ƛ z ⇒ (ƛ z ⇒ ` s · (` s · ` z)) · (twoᶜ · ` s · ` z)
    -- —→⟨ ζ ζ β ⟩
    --   ƛ s ⇒ ƛ z ⇒ ` s · (` s · (twoᶜ · ` s · ` z))
    -- —→⟨ ζ ζ ξ₂ ξ₂ ξ₁ β ⟩
    --   ƛ s ⇒ ƛ z ⇒ ` s · (` s · ((ƛ z ⇒ ` s · (` s · ` z)) · ` z))
    -- —→⟨ ζ ζ ξ₂ ξ₂ β ⟩
      ƛ s ⇒ ƛ z ⇒ ` s · (` s · (` s · (` s · ` z)))
    ≡⟨⟩
      fourᶜ
    ∎
-}

-- ** Specific term forms.
Neutral Normal Value : Pred₀ Term
Neutral = λ where
  (` _) → ⊤
  (L · M) → Neutral L × Normal M
  _ → ⊥
Normal M = Neutral M ⊎ (case M of λ where
  (ƛ x ⇒ N) → Normal N
  _ → ⊥)
Value = λ where
  (ƛ _ ⇒ _) → ⊤
  _ → ⊥

-- ** Progress.

pattern step_ x = inj₁ x
pattern ⟨+_ x   = inj₁ x
pattern done_ x = inj₂ x
pattern +⟩_ x   = inj₂ x
infix 0 step_ done_ ⟨+_ +⟩_

progress : (M : Term) → ∃ (M —→_) ⊎ Normal M
progress (` _) = done auto
progress (ƛ _ ⇒ N) with progress N
... | step (_ , N→) = ⟨+ -, ζ N→
... | done N∅       = +⟩ +⟩ N∅
progress (` _ · N) with progress N
... | step (_ , N→) = ⟨+ -, ξ₂ N→
... | done N∅       = +⟩ ⟨+ auto , N∅
progress ((ƛ _) · _) = ⟨+ -, β
progress (L@(_ · _) · M) with progress L
... | step (_ , L→) = ⟨+ -, ξ₁ L→
... | done (⟨+ L∅) with progress M
...   | step (_ , M→) = ⟨+ -, ξ₂ M→
...   | done M∅       = +⟩ ⟨+ (L∅ , M∅)

-- ** Evaluation.
Gas = ℕ

eval : Gas → (L : Term) → Maybe (∃ λ N → Normal N × (L —↠ N))
eval 0 L = nothing
eval (suc m) L with progress L
... | done N∅       = just $ -, N∅ , (L ∎)
... | step (M , L→) = map₂′ (map₂ (L —→⟨ L→ ⟩_)) <$> eval m M

{- Ctrl-c Ctrl-n "eval 100 2+2ᶜ" -}

-- ** Confluence

infix -1 _⇛_

data _⇛_ : Rel₀ Term where

  -- TODO: adding α-renaming is morally OK

  ν⇛ : ` x ⇛ ` x

  ζ⇛ :
      N ⇛ N′
      ──────────────────
      ƛ x ⇒ N ⇛ ƛ x ⇒ N′
  -- И a. N̂ @ a ⇛ N̂′ @ a
  -- ───────────────────
  -- ƛ N̂ ⇛ ƛ N̂′
  -- or use the dual ⅁??

  ξ⇛ :
    ∙ L ⇛ L′
    ∙ M ⇛ M′
      ───────────────
      L · M ⇛ L′ · M′

  β⇛ :
    ∙ N ⇛ N′
    ∙ M ⇛ M′
      ─────────────────────────────
      -- (ƛ x ⇒ N) · M ⇛ N′ [ x / M′ ]
      (ƛ x ⇒ N) · M ⇛ N′ [ x / M′ ]

open ReflexiveTransitiveClosure _⇛_
  renaming ( _—→⟨_⟩_ to _⇛⟨_⟩_; _∎ to _⇛∎; _—↠_ to _⇛∗_
           ; _—↠⟨_⟩_ to _⇛∗⟨_⟩_; —↠-trans to ⇛∗-trans
           )

par-refl : M ⇛ M
par-refl {` x}   = ν⇛
par-refl {ƛ N}   = ζ⇛ par-refl
par-refl {L · M} = ξ⇛ par-refl par-refl

beta-par :
  M —→ N
  ──────
  M ⇛ N
beta-par = λ where
  (ξ₁ r) → ξ⇛ (beta-par r) par-refl
  (ξ₂ r) → ξ⇛ par-refl (beta-par r)
  β      → β⇛ par-refl par-refl
  (ζ r)  → ζ⇛ (beta-par r)

beta-pars :
  M —↠ N
  ──────
  M ⇛∗ N
beta-pars = λ where
  (_ ∎) → _ ⇛∎
  (L —→⟨ b ⟩ bs) → L ⇛⟨ beta-par b ⟩ beta-pars bs

betas-pars :
  M —↠ N
  ──────
  M ⇛∗ N
betas-pars = λ where
  (_ ∎) → _ ⇛∎
  (_ —→⟨ p ⟩ bs) → _ ⇛⟨ beta-par p ⟩ betas-pars bs

par-betas :
  M ⇛ N
  ──────
  M —↠ N
par-betas (ν⇛ {x = x}) = (` x) ∎
par-betas (ζ⇛ p) = abs-cong (par-betas p)
par-betas {L · M} (ξ⇛ {L = L}{L′}{M}{M′} p₁ p₂) =
  begin L · M   —↠⟨ appL-cong (par-betas p₁) ⟩
        L′ · M  —↠⟨ appR-cong (par-betas p₂) ⟩
        L′ · M′ ∎
par-betas {(ƛ x ⇒ N) · M} (β⇛ {N′ = N′}{M′ = M′} p₁ p₂) =
  begin (ƛ x ⇒ N) · M   —↠⟨ appL-cong (abs-cong (par-betas p₁)) ⟩
        (ƛ x ⇒ N′) · M  —↠⟨ appR-cong (par-betas p₂) ⟩
        (ƛ x ⇒ N′) · M′ —→⟨ β ⟩
        N′ [ x / M′ ]   ∎

pars-betas :
  M ⇛∗ N
  ──────
  M —↠ N
pars-betas (_ ⇛∎) = _ ∎
pars-betas (_ ⇛⟨ p ⟩ ps) = —↠-trans (par-betas p) (pars-betas ps)

sub-swap :
  N ⇛ N′
  ──────────────────────────
  swap x y N ⇛ swap x y N′
sub-swap ν⇛ = ν⇛
sub-swap (ζ⇛ p) = ζ⇛ (sub-swap p)
sub-swap (ξ⇛ p q) = ξ⇛ (sub-swap p) (sub-swap q)
sub-swap {x = 𝕒}{𝕓} (β⇛ {N}{N′}{M}{M′}{x} p q) =
  {- β⇛ :
      ∙ N ⇛ N′
      ∙ M ⇛ M′
        ─────────────────────────────
        (ƛ x ⇒ N) · M ⇛ N′ [ x / M′ ]
  -}
  qed
  where
    a↔b = swap 𝕒 𝕓
    a↔b↓ = (Atom → Atom) ∋ swap 𝕒 𝕓

    -- ƛN⇛ : (ƛ x ⇒ N) ⇛ (ƛ x ⇒ N′)
    -- ƛN⇛ = ζ⇛ p

    -- N⇛ : a↔b (ƛ x ⇒ N) ⇛ a↔b (ƛ x ⇒ N′)
    -- N⇛ = sub-swap ƛN⇛

    N⇛ : a↔b N ⇛ a↔b N′
    N⇛ = sub-swap p

    M⇛ : a↔b M ⇛ a↔b M′
    M⇛ = sub-swap q

    H : a↔b (ƛ x ⇒ N) · a↔b M ⇛ a↔b N′ [ a↔b↓ x / a↔b M′ ]
    H = β⇛ N⇛ M⇛

    eq : a↔b (N′ [ x / M′ ]) ≡ a↔b N′ [ a↔b↓ x / a↔b M′ ]
    eq = swap-subst 𝕒 𝕓 {N′}{x}{M′}

    qed : a↔b (ƛ x ⇒ N) · a↔b M ⇛ a↔b (N′ [ x / M′ ])
    qed = subst (λ ◆ → a↔b (ƛ x ⇒ N) · a↔b M ⇛ ◆) (sym eq) H

postulate
  sub-swap˘ :
    swap x y N ⇛ swap x y N′
    ──────────────────────────
    N ⇛ N′

-- sub-conc : ∀ {f f′ : Abs Term} →
--   ƛ f ⇛ ƛ f′
--   ────────────────────
--   conc f x ⇛ conc f′ x
-- sub-conc (ζ⇛ p) = sub-swap p

-- {-# TERMINATING #-}
-- sub-par :
--   ∙ N ⇛ N′
--   ∙ M ⇛ M′
--     ───────────────────────────
--     N [ x / M ] ⇛ N′ [ x / M′ ]

-- sub-par {x = 𝕒} (ν⇛ {x = x}) p
--   with x ≟ 𝕒
-- ... | yes refl = p
-- ... | no  _    = ν⇛

-- sub-par (ξ⇛ L→ M→) p =
--   ξ⇛ (sub-par L→ p) (sub-par M→ p)

-- sub-par {M = M}{M′}{𝕒} (ζ⇛ {N}{N′}{x} p) q =
--   {- ζ⇛ :
--       N ⇛ N′
--       ──────────────────
--       ƛ x ⇒ N ⇛ ƛ x ⇒ N′
--   -}
--   qed
--   where
--     x′  = freshAtom (𝕒 ∷ supp (ƛ x ⇒ N) ++ supp M)
--     x′′ = freshAtom (𝕒 ∷ supp (ƛ x ⇒ N′) ++ supp M′)

--     xs = 𝕒 ∷ supp (ƛ x ⇒ N) ++ supp M

--     open ≡-Reasoning

--     eq : (ƛ x′′ ⇒ swap x′′ x N′ [ 𝕒 / M′ ]) ≡ (ƛ x′ ⇒ swap x′ x N′ [ 𝕒 / M′ ])
--     eq = extˡ (ζ≡ (xs , λ w w∉ →
--       let
--         eq₀ : swap w x′′ x ≡ swap w x′ x
--         eq₀ = {!!}

--         eq₁ : swap w x′′ N′ ≡ swap w x′ N′
--         eq₁ = {!!}
--       in
--       ≡-Reasoning.begin
--         swap w x′′ (swap x′′ x N′ [ 𝕒 / M′ ])
--       ≡⟨ swap-subst w x′′ ⟩
--         swap w x′′ (swap x′′ x N′) [ swap w x′′ 𝕒 / swap w x′′ M′ ]
--       ≡⟨ {!!} ⟩
--         swap w x′′ (swap x′′ x N′) [ 𝕒 / swap w x′′ M′ ]
--       ≡⟨ {!!} ⟩
--         swap w x′′ (swap x′′ x N′) [ 𝕒 / M′ ]
--       ≡⟨ cong _[ 𝕒 / M′ ]
--        $ ≡-Reasoning.begin
--            swap w x′′ (swap x′′ x N′)
--          ≡⟨ {!!} ⟩
--            swap (swap w x′′ x′′) (swap w x′′ x) (swap w x′′ N′)
--          ≡⟨ {!!} ⟩
--            swap w (swap w x′′ x) (swap w x′′ N′)
--          ≡⟨ cong₂ (swap w)
--             (≡-Reasoning.begin
--               swap w x′′ x
--              ≡⟨ {!!} ⟩
--               swap w x′ x
--              ≡-Reasoning.∎)
--             (≡-Reasoning.begin
--               swap w x′′ N′
--              ≡⟨ {!!} ⟩
--                swap w x′ N′
--              ≡-Reasoning.∎)
--           ⟩
--            swap w (swap w x′ x) (swap w x′ N′)
--          ≡⟨ {!!} ⟩
--            swap (swap w x′ x′) (swap w x′ x) (swap w x′ N′)
--          ≡⟨ {!!} ⟩
--            swap w x′ (swap x′ x N′)
--          ≡-Reasoning.∎
--        ⟩
--         swap w x′ (swap x′ x N′) [ 𝕒 / M′ ]
--       ≡⟨ {!!} ⟩
--         swap w x′ (swap x′ x N′) [ 𝕒 / swap w x′ M′ ]
--       ≡⟨ {!!} ⟩
--         swap w x′ (swap x′ x N′) [ swap w x′ 𝕒 / swap w x′ M′ ]
--       ≡˘⟨ swap-subst w x′ ⟩
--         swap w x′ (swap x′ x N′ [ 𝕒 / M′ ])
--       ≡-Reasoning.∎))


--     qed : (ƛ x ⇒ N) [ 𝕒 / M ] ⇛ (ƛ x ⇒ N′) [ 𝕒 / M′ ]
--     qed rewrite eq = ζ⇛ $ sub-par (sub-swap p) q


-- sub-par {M = X}{X′}{𝕒} (β⇛ {N}{N′}{M}{M′}{x} p q) pq =
--   {- β⇛ :
--       ∙ N ⇛ N′
--       ∙ M ⇛ M′
--         ─────────────────────────────
--         (ƛ x ⇒ N) · M ⇛ N′ [ x / M′ ]
--   -}
--   qed
--   where
--     x′ = freshAtom (𝕒 ∷ supp (ƛ x ⇒ N) ++ supp X)

--     _ : ((ƛ x ⇒ N) · M) [ 𝕒 / X ]
--       ≡ (ƛ x′ ⇒ swap x′ x N [ 𝕒 / X ]) · (M [ 𝕒 / X ])
--     _ = refl

--     N⇛ : swap x′ x N [ 𝕒 / X ] ⇛ swap x′ x N′ [ 𝕒 / X′ ]
--     N⇛ = sub-par (sub-swap p) pq

--     M⇛ : M [ 𝕒 / X ] ⇛ M′ [ 𝕒 / X′ ]
--     M⇛ = sub-par q pq

--     qed′ : ((ƛ x ⇒ N) · M) [ 𝕒 / X ]
--          ⇛ swap x′ x N′ [ 𝕒 / X′ ] [ x′ / M′ [ 𝕒 / X′ ] ]
--     qed′ = β⇛ N⇛ M⇛

--     eq : swap x′ x N′ [ 𝕒 / X′ ] [ x′ / M′ [ 𝕒 / X′ ] ]
--        ≡ N′ [ x / M′ ] [ 𝕒 / X′ ]
--     eq =
--       ≡-Reasoning.begin
--         swap x′ x N′ [ 𝕒 / X′ ] [ x′ / M′ [ 𝕒 / X′ ] ]
--       ≡-Reasoning.≡⟨ subst-commute {swap x′ x N′} ⟩
--         swap x′ x N′ [ x′ / M′ ] [ 𝕒 / X′ ]
--       ≡-Reasoning.≡⟨ cong (_[ 𝕒 / X′ ]) $ swap∘subst {x′}{x}{N′}{M′} ⟩
--         N′ [ x / M′ ] [ 𝕒 / X′ ]
--       ≡-Reasoning.∎

--     qed : ((ƛ x ⇒ N) · M) [ 𝕒 / X ] ⇛ N′ [ x / M′ ] [ 𝕒 / X′ ]
--     qed = subst (_ ⇛_) eq qed′

-- _⁺ : Op₁ Term
-- _⁺ = λ where
--   (` x)           → ` x
--   (ƛ x ⇒ M)       → ƛ x ⇒ (M ⁺)
--   ((ƛ x ⇒ N) · M) → N ⁺ [ x / M ⁺ ]
--   (L · M)         → (L ⁺) · (M ⁺)

-- par-⦊ :
--   M ⇛ N
--   ───────
--   N ⇛ M ⁺
-- par-⦊ ν⇛ = ν⇛
-- par-⦊ (ζ⇛ p) = ζ⇛ (par-⦊ p)
-- par-⦊ (β⇛ p p′) = sub-par (par-⦊ p) (par-⦊ p′)
-- par-⦊ (ξ⇛ {_ · _} p p′) = ξ⇛ (par-⦊ p) (par-⦊ p′)
-- par-⦊ (ξ⇛ {` _} p p′) = ξ⇛ (par-⦊ p) (par-⦊ p′)
-- par-⦊ (ξ⇛ {ƛ _} (ζ⇛ p) p′) = β⇛ (par-⦊ p) (par-⦊ p′)

-- par-⦉ = par-⦊

-- par-◇ :
--   ∙ M ⇛ N
--   ∙ M ⇛ N′
--     ──────────────────────────
--     ∃ λ L → (N ⇛ L) × (N′ ⇛ L)
-- par-◇ {M = M} p p′ = M ⁺ , par-⦉ p , par-⦊ p′

-- strip :
--   ∙ M ⇛ N
--   ∙ M ⇛∗ N′
--     ──────────────────────────
--     ∃ λ L → (N ⇛∗ L) × (N′ ⇛ L)
-- strip mn (_ ⇛∎) = -, (_ ⇛∎) , mn
-- strip mn (_ ⇛⟨ mm' ⟩ m'n') =
--   let _ , ll' , n'l' = strip (par-⦊ mm') m'n'
--   in  -, (_ ⇛⟨ par-⦊ mn ⟩ ll') , n'l'

-- par-confluence :
--   ∙ L ⇛∗ M₁
--   ∙ L ⇛∗ M₂
--     ──────────────────────────
--     ∃ λ N → (M₁ ⇛∗ N) × (M₂ ⇛∗ N)
-- par-confluence (_ ⇛∎) p = -, p , (_ ⇛∎)
-- par-confluence (_ ⇛⟨ L⇛M₁ ⟩ M₁⇛*M₁′) L⇛*M₂ =
--   let _ , M₁⇛*N , M₂⇛N    = strip L⇛M₁ L⇛*M₂
--       _ , M₁′⇛*N′ , N⇛*N′ = par-confluence M₁⇛*M₁′ M₁⇛*N
--    in -, M₁′⇛*N′ , (_ ⇛⟨ M₂⇛N ⟩ N⇛*N′)

-- confluence :
--   ∙ L —↠ M₁
--   ∙ L —↠ M₂
--     ─────────────────────────────
--     ∃ λ N → (M₁ —↠ N) × (M₂ —↠ N)
-- confluence L↠M₁ L↠M₂ =
--   let _ , M₁⇛N , M₂⇛N = par-confluence (betas-pars L↠M₁) (betas-pars L↠M₂)
--   in -, pars-betas M₁⇛N , pars-betas M₂⇛N
