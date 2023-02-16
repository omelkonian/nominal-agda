{-
Here we derive the canonical swapping for every inductive datatype,
i.e. the swapping the equivariantly distributes amongst constructors,
a.k.a. constructors are equivariant.
-}

{-# OPTIONS -v nominal:100 #-}
open import Prelude.Init
open import Prelude.DecEq
open import Prelude.Monad
open import Prelude.Semigroup
open import Prelude.Show
open import Prelude.ToN
open import Prelude.Lists
open import Prelude.Functor
open import Prelude.Bifunctor
open import Prelude.Applicative

open Meta
open import Prelude.Generics
open import Prelude.Tactics.Extra using (getPatTele)
open Debug ("nominal" , 100)

module Nominal.Swap.Derive (Atom : Set) ⦃ _ : DecEq Atom ⦄ where

open import Nominal.Swap.Base Atom

{-# TERMINATING #-}
derive↔ : Definition → TC Term
derive↔ d with d
... | record-type rn fs = do
  print $ "RECORD {name = " ◇ show rn ◇ "; fs = " ◇ show fs ◇ "}"
  return `λ⟦ "𝕒" ∣ "𝕓" ∣ "r" ⇒ pat-lam (map (mkClause ∘ unArg) fs) [] ⟧
  where
    ♯a = ♯ 2; ♯b = ♯ 1; ♯r = ♯ 0

    mkClause : Name → Clause
    mkClause fn = clause [] [ vArg $ proj fn ] (quote swap ∙⟦ ♯a ∣ ♯b ∣ fn ∙⟦ ♯r ⟧ ⟧)
... | data-type ps cs = do
  print $ "DATATYPE {pars = " ◇ show ps ◇ "; cs = " ◇ show cs ◇ "}"
  -- cs′ ← mapM mkClause $ drop 1 cs
  cs′ ← mapM mkClause cs
  return `λ⟦ "𝕒" ∣ "𝕓" ⇒ pat-lam cs′ [] ⟧
  where
    mkClause : Name → TC Clause
    mkClause cn = do
      tel ← getPatTele cn
      print $ "Making pattern clause for constructor: " ◇ show cn ◇ " " ◇ show tel
      let N = length tel; ♯𝕒 = ♯ (N + 1); ♯𝕓 = ♯ N
      print $ "  ♯𝕒: " ◇ show ♯𝕒
      print $ "  ♯𝕓: " ◇ show ♯𝕓
      -- let tel′ = map (map₂ $ fmap $ mapVars $ suc ∘ suc ∘ suc) tel
      let tel′ = map (map₂ $ fmap $ const unknown) tel
      print $ "  tel′: " ◇ show tel′
      let
        tys : Args Type
        tys = map proj₂ tel′

        itys = enumerate tys

        cArgsᵖ : Args Pattern
        cArgsᵖ = map (λ (i , at) → fmap (const $ var $ toℕ i) at) (L.reverse itys)

        cArgs : Args Term
        cArgs = map (λ (i , at) → fmap (const $ quote swap ∙⟦ ♯𝕒 ∣ ♯𝕓 ∣ ♯ (toℕ i) ⟧) at) (L.reverse itys)

      return $ clause tel′ [ vArg $ con cn cArgsᵖ ] (con cn cArgs)
... | function cs = do
  print $ "FUNCTION {cs = " ◇ show cs ◇ "}"
  clause tel ps t ∷ [] ← return cs
    where _ → error "[not supported] multi-clause function"
  print $ "  tel: " ◇ show tel
  ctx ← getContext
  print $ "  ctx: " ◇ show ctx
  inContext (L.reverse tel) $ do
    t′@(def n as) ← normalise t
      where _ → error "[not supported] rhs does not refer to another definition"
    print $ "  t′: " ◇ show t′
    d ← getDefinition n
    print $ "  d: " ◇ show d
    derive↔ d
... | data-cons _ = error "[not supported] data constructors"
... | axiom       = error "[not supported] axioms or mutual definitions"
... | prim-fun    = error "[not supported] primitive functions"

private variable A : Set ℓ

addHypotheses : Type → Type
addHypotheses = λ where
  (Π[ s ∶ a ] ty) →
    let ty′ = addHypotheses ty
        ty″ = iΠ[ "_" ∶ quote Swap ∙⟦ ♯ 0 ⟧ ] mapVars suc ty′
    in
    Π[ s ∶ a ]
      (case unArg a of λ where
        (agda-sort (lit _)) → ty″
        (agda-sort (set _)) → ty″
        _ → ty′)
  ty → ty

externalizeSwap : Type → Type
externalizeSwap = go 0
  where
    go : ℕ → Type → Type
    go n = λ where
      (def (quote Swap) as) →
        def (quote Swap) (vArg (♯ (suc n)) ∷ iArg (♯ n) ∷ as)
      (Π[ s ∶ arg i a ] ty) →
        Π[ s ∶ arg i (go n a) ] go (suc n) ty
      t → t

addHypotheses′ : (Type → Type) → Type → Type
addHypotheses′ Swap∙ = λ where
  (Π[ s ∶ a ] ty) →
    let ty′ = addHypotheses′ Swap∙ ty
        ty″ = iΠ[ "_" ∶ Swap∙ (♯ 0) ] mapVars suc ty′
    in
    Π[ s ∶ a ]
      (case unArg a of λ where
        (agda-sort (lit _)) → ty″
        (agda-sort (set _)) → ty″
        _ → ty′)
  ty → ty

instance
  Derivable-Swap : DERIVABLE Swap 1
  Derivable-Swap .derive args = do
    print "********************************************************"
    (record-type `swap _) ← getDefinition (quote Swap)
      where _ → _IMPOSSIBLE_
    ((n , f) ∷ []) ← return args
      where _ → error "not supported: mutual types"
    print $ "Deriving " ◇ parens (show f ◇ " : Swap " ◇ show n)
    T ← getType n
    ctx ← getContext
    -- ctx@(_ ∷ _ ∷ []) ← getContext
    --   where _ → error "Context ≠ {Atom : Set} ⦃ _ : DecEq Atom ⦄"
    print $ "  Context: " ◇ show ctx
    print $ "  Type: " ◇ show T
    d ← getDefinition n
    print $ "  Definition: " ◇ show d
    print $ "  argTys: " ◇ show (argTys T)

    print $ "  Parameters: " ◇ show (parameters d)
    let tel = tyTele T
    print $ "  Indices: " ◇ show (unzip tel .proj₂)
    let n′ = apply⋯ tel n
    print $ "  n′: " ◇ show n′
    let T′ = addHypotheses
           $ ∀indices⋯ tel
           $ quote Swap ∙⟦ n′ ⟧
    print $ "  T′: " ◇ show T′
    let T″ = externalizeSwap T′
    print $ "  T″: " ◇ show T″
    T ←   (declareDef (iArg f) T′ >> return T′)
      <|> (declareDef (iArg f) T″ >> return T″)

    let mctx = argTys T
        mtel = map ("_" ,_) mctx
        pc   = map (λ where (i , a) → fmap (const (` (length mctx ∸ suc (toℕ i)))) a) (enumerate mctx)
    print $ "  mctx: " ◇ show mctx
    print $ "  mtel: " ◇ show mtel
    print $ "  pc: " ◇ show pc

    t ← derive↔ d
    print $ "t: " ◇ show t
    defineFun f [ clause mtel pc (`swap ◆⟦ t ⟧) ]

-- ** deriving examples
unquoteDecl ⊎↔ = DERIVE Swap [ quote _⊎_ , ⊎↔ ]
-- unquoteDecl Σ↔ = DERIVE Swap [ quote Σ , Σ↔ ]
unquoteDecl ×↔ = DERIVE Swap [ quote _×_ , ×↔ ]
{-# TERMINATING #-}
unquoteDecl List↔ = DERIVE Swap [ quote List , List↔ ]

private
  -- ** record types
  record R⁰ : Set where
  instance
    R∅ : Swap R⁰
    R∅ = mkNameless R⁰

  record R¹ : Set where
    field x : ℕ
  unquoteDecl r¹ = DERIVE Swap [ quote R¹ , r¹ ]

  record R¹′ : Set where
    field
      x : ℕ
      y : ℕ
      r : R¹
  unquoteDecl r¹′ = DERIVE Swap [ quote R¹′ , r¹′ ]

  record R² : Set where
    field
      x : ℕ × ℤ
      y : ⊤ ⊎ Bool
  unquoteDecl r² = DERIVE Swap [ quote R² , r² ]

  record P (A : Set) : Set where
    field x : A
  unquoteDecl p = DERIVE Swap [ quote P , p ]

  -- ** inductive datatypes

  data X⁰ : Set where
  instance
    X⁰∅ : Swap X⁰
    X⁰∅ = mkNameless X⁰

  data X¹ : Set where
    x : X¹
  unquoteDecl x¹ = DERIVE Swap [ quote X¹ , x¹ ]

  data X¹′ : Set where
    x : ℕ → X¹′
  unquoteDecl x¹′ = DERIVE Swap [ quote X¹′ , x¹′ ]

  data X² : Set where
    x y : X²
  unquoteDecl x² = DERIVE Swap [ quote X² , x² ]

  data X²′ : Set where
    x y : ℕ → Bool → X²′
  unquoteDecl x²′ = DERIVE Swap [ quote X²′ , x²′ ]

  data PAIR (A B : Set) : Set where
    ⦅_,_⦆ : A → B → PAIR A B
  unquoteDecl PAIR↔ = DERIVE Swap [ quote PAIR , PAIR↔ ]

  data HPAIR {a b : Level} (A : Set a) (B : Set b) : Set (a ⊔ₗ b) where
    ⦅_,_⦆ : A → B → HPAIR A B
  unquoteDecl HPAIR↔ = DERIVE Swap [ quote HPAIR , HPAIR↔ ]

  infixr 4 _∺_
  data LIST (A : Set) : Set where
    ∅ : LIST A
    _∺_ : A → LIST A → LIST A
  -- instance
  --   List↔ : ⦃ Swap A ⦄ → Swap (LIST A)
  --   List↔ {A} ⦃ A↔ ⦄ .swap = λ 𝕒 → λ 𝕓 → λ where
  --     ∅ → ∅
  --     (a ∺ as) → swap 𝕒 𝕓 a ∺ swap 𝕒 𝕓 as
  {-# TERMINATING #-}
  unquoteDecl LIST↔ = DERIVE Swap [ quote LIST , LIST↔ ]

  postulate 𝕒 𝕓 : Atom

  _ : swap 𝕒 𝕓 (1 ∺ 2 ∺ 3 ∺ ∅) ≡ (1 ∺ 2 ∺ 3 ∺ ∅)
  _ = refl

  data XX : Set where
    c₂ : List X² → XX
    c₁ : X¹ → X² → XX
  unquoteDecl xx = DERIVE Swap [ quote XX , xx ]
