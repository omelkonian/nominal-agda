open import Prelude.Init hiding ([_]); open SetAsType
open import Prelude.DecEq
open import Prelude.InfEnumerable
open import Prelude.InferenceRules
open import Prelude.Closures
open import Prelude.Decidable
open import Prelude.Functor
open import Prelude.Bifunctor
open import Prelude.Setoid


module ULC.Reduction (Atom : Type) ⦃ _ : DecEq Atom ⦄ ⦃ _ : Enumerable∞ Atom ⦄ where

open import ULC.Base         Atom ⦃ it ⦄ hiding (z)
open import ULC.Measure      Atom ⦃ it ⦄
open import ULC.Alpha        Atom ⦃ it ⦄
open import ULC.Substitution Atom ⦃ it ⦄
open import Nominal          Atom ⦃ it ⦄

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
  postulate s z n m : Atom

  zeroᶜ = ƛ s ⇒ ƛ z ⇒ ` z
  sucᶜ  = ƛ n ⇒ ƛ s ⇒ ƛ z ⇒ ` s · (` n · ` s · ` z)

  mkNumᶜ : ℕ → Term
  mkNumᶜ = λ where
    zero    → zeroᶜ
    (suc n) → sucᶜ · (mkNumᶜ n)

  twoᶜ  = ƛ s ⇒ ƛ z ⇒ ` s · (` s · ` z)
  fourᶜ = ƛ s ⇒ ƛ z ⇒ ` s · (` s · (` s · (` s · ` z)))
  plusᶜ = ƛ m ⇒ ƛ n ⇒ ƛ s ⇒ ƛ z ⇒ (` m · ` s · (` n · ` s · ` z))
  2+2ᶜ  = plusᶜ · twoᶜ · twoᶜ

{-
  _ : 2+2ᶜ —↠ fourᶜ
  _ =
    begin
      (plusᶜ · twoᶜ) · twoᶜ
    —→⟨ ξ₁ β ⟩
      (ƛ n ⇒ ƛ s ⇒ ƛ z ⇒ twoᶜ · ` s · (` n · ` s · ` z)) · twoᶜ
    —→⟨ β ⟩
      ƛ s ⇒ ƛ z ⇒ twoᶜ · ` s · (twoᶜ · ` s · ` z)
    —→⟨ ζ ζ ξ₁ β ⟩
      ƛ s ⇒ ƛ z ⇒ (ƛ z ⇒ ` s · (` s · ` z)) · (twoᶜ · ` s · ` z)
    —→⟨ ζ ζ β ⟩
      ƛ s ⇒ ƛ z ⇒ ` s · (` s · (twoᶜ · ` s · ` z))
    —→⟨ ζ ζ ξ₂ ξ₂ ξ₁ β ⟩
      ƛ s ⇒ ƛ z ⇒ ` s · (` s · ((ƛ z ⇒ ` s · (` s · ` z)) · ` z))
    —→⟨ ζ ζ ξ₂ ξ₂ β ⟩
      ƛ s ⇒ ƛ z ⇒ ` s · (` s · (` s · (` s · ` z)))
      -- fourᶜ
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

-- T0D0: maybe add hypothesis : y ♯ L
subst-commute : N [ x / L ] [ y / M [ x / L ] ] ≡ N [ y / M ] [ x / L ]
subst-commute = {!!}

-- T0D0: add hypothesis : y ♯ N̂
swap∘subst : swap y x N [ y / M ] ≡ N [ x / M ]
-- swap∘subst : swap y x N̂ [ M ] ≡ N̂ [ M ]
swap∘subst = {!!}

sub-abs :
  N ⇛ N′
  ──────────────────────
  (ƛ x ⇒ N) ⇛ (ƛ x ⇒ N′)
sub-abs = ζ⇛

sub-swap :
  N ⇛ N′
  ──────────────────────────
  swap x y N ⇛ swap x y N′
sub-swap ν⇛ = ν⇛
sub-swap (ζ⇛ p) = ζ⇛ (sub-swap p)
sub-swap (ξ⇛ p q) = ξ⇛ (sub-swap p) (sub-swap q)
sub-swap {x = 𝕒}{𝕓} (β⇛ {N}{N′}{M}{M′}{x} p q) = -- {!ξ⇛ ? (sub-swap q)!}
  -- β⇛ :
  --   ∙ N ⇛ N′
  --   ∙ M ⇛ M′
  --     ─────────────────────────────
  --     (ƛ x ⇒ N) · M ⇛ N′ [ x / M′ ]
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

    qed : a↔b (ƛ x ⇒ N) · a↔b M ⇛ a↔b (N′ [ x / M′ ])
    -- ≡ (ƛ a↔b x ⇒ a↔b N) · a↔b M
    -- ⇛⟨ β⇛ N⇛ M⇛ ⟩ a↔b N′ [ a↔b x / a↔b M′ ]
    -- ≡⟨ ? ⟩ a↔b (N′ [ x / M′ ])
    qed = {!!}

-- sub-conc : ∀ {f f′ : Abs Term} →
--   ƛ f ⇛ ƛ f′
--   ────────────────────
--   conc f x ⇛ conc f′ x
-- sub-conc (ζ⇛ p) = sub-swap p

{-# TERMINATING #-}
sub-par :
  ∙ N ⇛ N′
  ∙ M ⇛ M′
    ───────────────────────────
    N [ x / M ] ⇛ N′ [ x / M′ ]

sub-par {x = 𝕒} (ν⇛ {x = x}) p
  with x ≟ 𝕒
... | yes refl = p
... | no  _    = ν⇛

sub-par (ξ⇛ L→ M→) p =
  ξ⇛ (sub-par L→ p) (sub-par M→ p)

  -- ζ⇛ :
  --     N ⇛ N′
  --     ──────────────────
  --     ƛ x ⇒ N ⇛ ƛ x ⇒ N′
sub-par {M = M}{M′}{𝕒} (ζ⇛ {N}{N′}{x} p) q =
  {!!}
{-
  qed
  where
    x′ x′′ : Atom
    x′  = fresh (𝕒 ∷ x ∷ supp N ++ supp M) .proj₁
    x′′ = fresh (𝕒 ∷ x ∷ supp N′ ++ supp M′) .proj₁

    x≡ : x′ ≡ x′′
    x≡ = {!!}

    -- p : N ⇛ N′

    ↔p : swap x x′ N ⇛ swap x x′ N′
    ↔p = sub-swap p

    s↔p : swap x x′ N [ 𝕒 / M ] ⇛ swap x x′ N′ [ 𝕒 / M′ ]
    s↔p = sub-par ↔p q

    ƛs↔p : (ƛ x′ ⇒ swap x x′ N [ 𝕒 / M ]) ⇛ (ƛ x′ ⇒ swap x x′ N′ [ 𝕒 / M′ ])
    ƛs↔p = sub-abs s↔p

    ƛs↔p′ : (ƛ x′ ⇒ swap x x′ N [ 𝕒 / M ])
          ⇛ (ƛ x′′ ⇒ swap x x′′ N′ [ 𝕒 / M′ ])
    ƛs↔p′ = subst (λ ◆ → (ƛ x′ ⇒ swap x x′ N [ 𝕒 / M ])
                        ⇛ (ƛ ◆ ⇒ swap x ◆ N′ [ 𝕒 / M′ ]))
                   x≡ ƛs↔p

    qed : (ƛ x ⇒ N) [ 𝕒 / M ] ⇛ (ƛ x ⇒ N′) [ 𝕒 / M′ ]
    -- qed : (ƛ N̂) [ 𝕒 / M ] ⇛ (ƛ N̂′) [ 𝕒 / M′ ]
    qed = {!!} -- ƛs↔p′
-}
  -- β⇛ :
  --   ∙ N ⇛ N′
  --   ∙ M ⇛ M′
  --     ─────────────────────────────
  --     (ƛ x ⇒ N) · M ⇛ N′ [ x / M′ ]
sub-par {M = X}{X′}{𝕒} (β⇛ {N}{N′}{M}{M′}{x} p q) pq =
  {!!}
{-
  qed
  where
    x′ : Atom
    x′ = fresh (𝕒 ∷ x ∷ supp N ++ supp X) .proj₁

    _ : ((ƛ x ⇒ N) · M) [ 𝕒 / X ]
      ≡ (ƛ x′ ⇒ swap x′ x N [ 𝕒 / X ]) · (M [ 𝕒 / X ])
    _ = refl

    N⇛ : swap x′ x N [ 𝕒 / X ] ⇛ swap x′ x N′ [ 𝕒 / X′ ]
    N⇛ = sub-par (sub-swap p) pq

    M⇛ : M [ 𝕒 / X ] ⇛ M′ [ 𝕒 / X′ ]
    M⇛ = sub-par q pq

    qed′ : ((ƛ x ⇒ N) · M) [ 𝕒 / X ]
         ⇛ swap x′ x N′ [ 𝕒 / X′ ] [ x′ / M′ [ 𝕒 / X′ ] ]
    qed′ = β⇛ N⇛ M⇛

    eq : swap x′ x N′ [ 𝕒 / X′ ] [ x′ / M′ [ 𝕒 / X′ ] ]
       ≡ N′ [ x / M′ ] [ 𝕒 / X′ ]
    eq =
      begin≡
        swap x′ x N′ [ 𝕒 / X′ ] [ x′ / M′ [ 𝕒 / X′ ] ]
      ≡⟨ subst-commute {swap x′ x N′} ⟩
        swap x′ x N′ [ x′ / M′ ] [ 𝕒 / X′ ]
      ≡⟨ cong (_[ 𝕒 / X′ ]) $ swap∘subst {x′}{x}{N′}{M′} ⟩
        N′ [ x / M′ ] [ 𝕒 / X′ ]
      ∎≡ where open ≡-Reasoning renaming (begin_ to begin≡_; _∎ to _∎≡)

    qed : ((ƛ x ⇒ N) · M) [ 𝕒 / X ] ⇛ N′ [ x / M′ ] [ 𝕒 / X′ ]
    qed = subst (_ ⇛_) eq qed′
-}

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

-- {- Version working with an abstract `Atom` type and rewriting with decidable equalitx′.
--   open import Relation.Nullarx′.Decidable using (isYes≗does)
--   private
--     postulate
--       𝕒 𝕓 𝕔 : Atom
--       b≢a : 𝕓 ≢ 𝕒

--     rw₁ : isYes (𝕒 ≟ 𝕒) ≡ true
--     rw₁ rewrite ≟-refl 𝕒 = refl
--     {-` REWRITE rw₁ `-}
--     rw₂ : isYes (𝕓 ≟ 𝕓) ≡ true
--     rw₂ rewrite ≟-refl 𝕓 = refl
--     {-` REWRITE rw₂ `-}
--     rw₃ : isYes (𝕓 ≟ 𝕒) ≡ false
--     rw₃ rewrite isYes≗does (𝕓 ≟ 𝕒) | dec-false (𝕓 ≟ 𝕒) b≢a = refl
--     {-` REWRITE rw₃ `-}
--     rw₄ : isYes (𝕒 ≟ 𝕓) ≡ false
--     rw₄ rewrite isYes≗does (𝕒 ≟ 𝕓) | dec-false (𝕒 ≟ 𝕓) (b≢a ∘ sym) = refl
--     {-` REWRITE rw₄ `-}

--     -- ** example swapping in a λ-term
--     _ : swap 𝕒 𝕓 (` 𝕒 · ` 𝕓) ≡ ` 𝕓 · ` 𝕒
--     _ = refl

--     _ = swap 𝕒 𝕓 (` 𝕒 · ` 𝕓) ≡ ` 𝕓 · ` 𝕒
--       ∋ refl

--     `id = ƛ abs 𝕒 (` 𝕒)

--     _ = swap 𝕒 𝕓 `id ≡ ƛ (abs 𝕓 (` 𝕓))
--       ∋ refl

--     -- this is the expected behaviour, doesn't matter denotationallx′
--     -- onlx′ need a smarter `swap` for efficiencx′ (e.g. using support indices)
--     -- e.g. in `swap a b (\{⋯a⋯b⋯}. x₁ * a * ⋯ xᵢ ⋯ * (b + ⋯))`
--     --      do not go inside the term as an optimix′ation
--     -- FUTURE: name restriction (e.g. used in iEUTxO instead of abstraction)
--     _ = swap 𝕒 𝕓 ((ƛ abs 𝕒 (` 𝕒)) · ` 𝕒)
--                 ≡ (ƛ abs 𝕓 (` 𝕓)) · ` 𝕓
--       ∋ refl

--     _ : (ƛ abs 𝕓 (` 𝕓 · ` 𝕒)) · (ƛ abs 𝕒 (` 𝕒 · ` 𝕓)) —↠ ` 𝕒 · ` 𝕓
--     _ = begin (ƛ abs 𝕓 (` 𝕓 · ` 𝕒)) · (ƛ abs 𝕒 (` 𝕒 · ` 𝕓)) —→⟨ β ⟩
--               (ƛ abs 𝕒 (` 𝕒 · ` 𝕓)) · ` 𝕒                   —→⟨ β ⟩
--               ` 𝕒 · ` 𝕓                                     ∎
-- -}
