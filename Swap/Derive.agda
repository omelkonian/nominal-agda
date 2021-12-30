{-# OPTIONS -v nominal:100 #-}
open import Prelude.Init hiding (swap)
open import Prelude.DecEq
open import Prelude.Monad
open import Prelude.Semigroup
open import Prelude.Show
open import Prelude.ToN
open import Prelude.Lists
open import Prelude.Functor
open import Prelude.Bifunctor

open Meta
open import Prelude.Generics
open Debug ("nominal" , 100)

module Swap.Derive (Atom : Set) ⦃ _ : DecEq Atom ⦄ where

open import Swap.Base Atom ⦃ it ⦄

getPatTele : Name → TC PatTelescope
getPatTele cn = do
  print $ "Getting pattern telescope for constructor: " ◇ show cn
  ty ← getType cn
  print $ "  ty: " ◇ show ty
  data-cons n ← getDefinition cn
    where _ → _IMPOSSIBLE_
  print $ "  n: " ◇ show n
  data-type ps _ ← getDefinition n
    where _ → _IMPOSSIBLE_
  print $ "  ps: " ◇ show ps
  let tys = drop ps (argTys ty)
  print $ "  argTys: " ◇ show tys
  let tel = map ("_" ,_) tys
  print $ "  tel: " ◇ show tel
  return tel

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
  inContext (L.reverse (map proj₂ tel) ++ ctx) $ do
    t′@(def n as) ← normalise t
      where _ → error "[not supported] rhs does not refer to another definition"
    print $ "  t′: " ◇ show t′
    d ← getDefinition n
    print $ "  d: " ◇ show d
    derive↔ d
... | data-cons _ = error "[not supported] data constructors"
... | axiom       = error "[not supported] axioms"
... | prim-fun    = error "[not supported] primitive functions"


dropFront : ⦃ DecEq A ⦄ → List A → List A → List A
dropFront xs ys =
  let ysˡ , ysʳ = L.splitAt (length xs) ys
  in if ysˡ == xs then ysʳ
    else ys

∀instances⋯ : (Type → Type) → List Type → (Type → Type)
∀instances⋯ _ []       ty = ty
∀instances⋯ F (i ∷ is) ty = iΠ[ "_" ∶ F i ] (∀instances⋯ F is ty)

pattern agda-lit n = agda-sort (lit n)
pattern agda-set n = agda-sort (set n)

addHypotheses : Type → TC Type
addHypotheses = λ where
  (Π[ s ∶ a ] ty) → do
    ty′ ← addHypotheses ty
    print $ show ty
    print " ∼↝ "
    print $ show ty′
    case unArg a of λ where
      (agda-sort (lit _)) → do
        print $ show ty′
        print " ∼∼↝ "
        print $ show (mapVars suc ty′)
        return $ Π[ s ∶ a ] iΠ[ "_" ∶ quote Swap ∙⟦ ♯ 0 ⟧ ] mapVars suc ty′
      (agda-sort (set _)) → do
        print $ show ty′
        print " ∼∼↝ "
        print $ show (mapVars suc ty′)
        return $ Π[ s ∶ a ] iΠ[ "_" ∶ quote Swap ∙⟦ ♯ 0 ⟧ ] mapVars suc ty′
      _ → do print "non-set"
             return $ Π[ s ∶ a ] ty′
  t → return t

instance
  Derivable↔ : Derivable Swap
  Derivable↔ .DERIVE' args = do
    print "********************************************************"
    (record-type `swap _) ← getDefinition (quote Swap)
      where _ → _IMPOSSIBLE_
    ((n , f) ∷ []) ← return args
      where _ → error "not supported: mutual types"
    print $ "Deriving " ◇ parens (show f ◇ " : Swap " ◇ show n)
    T ← getType n
    ctx ← getContext
    print $ "  Context: " ◇ show ctx
    print $ "  Type: " ◇ show T
    d ← getDefinition n
    print $ "  Definition: " ◇ show d
    print $ "  argTys: " ◇ show (argTys T)
    let toDrop = length ctx
    print $ "  toDrop: " ◇ show toDrop

    print $ "  Parameters: " ◇ show (parameters d)
    let is = dropFront (L.reverse ctx) (argTys T)
    -- let is = drop toDrop (argTys T)
    print $ "  Indices: " ◇ show is
    let n′ = apply⋯ is n
    print $ "  n′: " ◇ show n′
    T′ ← addHypotheses
           $ ∀indices⋯ is
           $ quote Swap ∙⟦ n′ ⟧
    print $ "  T′: " ◇ show T′
    declareDef (iArg f) T′

    let mctx = argTys T′
        mtel = map ("_" ,_) mctx
        pc   = map (λ where (i , a) → fmap (const (` (length mctx ∸ suc (toℕ i)))) a) (enumerate mctx)
    print $ "  mctx: " ◇ show mctx
    print $ "  mtel: " ◇ show mtel
    print $ "  pc: " ◇ show pc

    t ← derive↔ d
    -- t ← inContext (L.reverse mctx ++ ctx) $ do
    --   ctx ← getContext
    --   print $ "  Context′: " ◇ show ctx
    --   derive↔ (n , f) d
    print $ "t: " ◇ show t
    defineFun f [ clause mtel pc (`swap ◆⟦ t ⟧) ]

-- instance
--   Σ↔ : ∀ {a b : Level} {A : Set a} {B : A → Set b}
--     → ⦃ Swap A ⦄
--     → ⦃ ∀ {a : A} → Swap (B a) ⦄
--     → Swap (Σ A B)
--   Σ↔ ⦃ sw₁ ⦄ ⦃ sw₂ ⦄ .swap 𝕒 𝕓 (a , Ba) = swap 𝕒 𝕓 a , {!swap ⦃ sw₂ {a = swap 𝕒 𝕓 a} ⦄ 𝕒 𝕓 Ba!}
-- unquoteDecl Σ↔ = DERIVE Swap [ quote Σ , Σ↔ ]

-- instance
--   ×↔ : ∀ {a b : Level} {A : Set a} {B : Set b}
--     → ⦃ Swap A ⦄
--     → ⦃ Swap B ⦄
--     → Swap (A × B)
--   ×↔ .swap = λ 𝕒 𝕓 → λ where
--     (a , b) → swap 𝕒 𝕓 a , swap 𝕒 𝕓 b
unquoteDecl ×↔ = DERIVE Swap [ quote _×_ , ×↔ ]

data PAIR (A B : Set) : Set where
  ⦅_,_⦆ : A → B → PAIR A B
unquoteDecl PAIR↔ = DERIVE Swap [ quote PAIR , PAIR↔ ]

data HPAIR {a b : Level} (A : Set a) (B : Set b) : Set (a ⊔ₗ b) where
  ⦅_,_⦆ : A → B → HPAIR A B
unquoteDecl HPAIR↔ = DERIVE Swap [ quote HPAIR , HPAIR↔ ]

data LIST (A : Set) : Set where
  ∅ : LIST A
  _∺_ : A → LIST A → LIST A

-- {-# TERMINATING #-}
-- unquoteDecl List↔ = DERIVE Swap [ quote LIST , List↔ ]

instance
  List↔ : ⦃ Swap A ⦄ → Swap (LIST A)
  List↔ {A} ⦃ A↔ ⦄ .swap = λ 𝕒 → λ 𝕓 → λ where
    ∅ → ∅
    (a ∺ as) → swap 𝕒 𝕓 a ∺ swap 𝕒 𝕓 as

data λTerm : Set where
  _-APP-_ : λTerm → λTerm → λTerm
  VAR : Atom → λTerm
  -- LAM : Atom × λTerm → λTerm
  -- LAM : Bind?? → Term

-- λ x . x
-- ~
-- LAM (𝕩 , var 𝕩)

{-# TERMINATING #-}
unquoteDecl λTerm↔ = DERIVE Swap [ quote λTerm , λTerm↔ ]

-- ** deriving examples

-- private

  -- testSwapRefl : (A : Set) ⦃ _ : Swap A ⦄ → Set
  -- testSwapRefl X ⦃ r ⦄ = ∀ {x : X} → swap ⦃ r ⦄ 𝕒 𝕓 x ≡ x

  -- ** record types

  -- record R⁰ : Set where
  -- instance R∅ = Nameless R⁰ ∋ it

  -- _ : testSwapRefl R⁰
  -- _ = refl

--   instance ℕ↔ = Swap ℕ ∋ λ where .swap → swapId
--   instance 𝔹↔ = Swap Bool ∋ λ where .swap → swapId

--   record R¹ : Set where
--     field x : ℕ
--   unquoteDecl r¹ = DERIVE Swap [ quote R¹ , r¹ ]
--   _ = testSwapRefl R¹ ∋ refl

--   record R¹′ : Set where
--     field
--       x : ℕ
--       y : ℕ
--       r : R¹
--   unquoteDecl r¹′ = DERIVE Swap [ quote R¹′ , r¹′ ]
--   _ = testSwapRefl R¹′ ∋ refl

--   -- record R² : Set where
--   --   field
--   --     x : ℕ × ℤ
--   --     y : ⊤ ⊎ Bool
--   -- unquoteDecl r² = DERIVE Swap [ quote R² , r² ]
--   -- _ = testSwapRefl R² ∋ refl

--   -- ** inductive datatypes

--   -- data X⁰ : Set where
--   -- unquoteDecl x⁰ = DERIVE Swap [ quote X⁰ , x⁰ ]
--   -- _ = testSwapRefl X⁰ ∋ refl

--   data X¹ : Set where
--     x : X¹
--   unquoteDecl x¹ = DERIVE Swap [ quote X¹ , x¹ ]

--   data X¹′ : Set where
--     x : ℕ → X¹′
--   unquoteDecl x¹′ = DERIVE Swap [ quote X¹′ , x¹′ ]

--   data X² : Set where
--     x y : X²
--   unquoteDecl x² = DERIVE Swap [ quote X² , x² ]

--   data X²′ : Set where
--     x y : ℕ → Bool → X²′
--   unquoteDecl x²′ = DERIVE Swap [ quote X²′ , x²′ ]

--   _ : swap 𝕒 𝕓 (1 ∷ 2 ∷ 3 ∷ []) ≡ (1 ∷ 2 ∷ 3 ∷ [])
--   _ = refl

--   data XX : Set where
--     c₂ : List X² → XX
--     c₁ : X¹ → X² → XX
--   unquoteDecl xx = DERIVE Swap [ quote XX , xx ]
