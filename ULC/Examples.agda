module ULC.Examples where

open import Prelude.Init
open L.Mem
open import Prelude.DecEq
open import Prelude.Nary
open import Prelude.Decidable
open import Prelude.Setoid
open import Prelude.General

-- ** instantiate atoms to be the natural numbers
data Atom : Set where
  $_ : ℕ → Atom
unquoteDecl DecEq-Atom = DERIVE DecEq [ quote Atom , DecEq-Atom ]
open import Nominal Atom ⦃ it ⦄
open import ULC     Atom ⦃ it ⦄

s = $ 0; z = $ 1; m = $ 2; n = $ 3
a = $ 10; b = $ 11; c = $ 12; d = $ 13; e = $ 14

-- ** α-equivalence

_ = (` a) ≡α (` a) ∋ ν≡

_ : (ƛ a ⇒ ` a) ≡α (ƛ b ⇒ ` b)
_ = ζ≡ (-, qed)
  where qed : ∀ y → y L.Mem.∉ [] → swap y a (` a) ≡α swap y b (` b)
        qed y _ rewrite swapʳ y a | swapʳ y b = ν≡

h : (ƛ a ⇒ ` c · ` a) ≡α (ƛ b ⇒ ` c · ` b)
h = ζ≡ (-, qed)
  where qed : ∀ y → y L.Mem.∉ [ c ] → swap y a (` c · ` a) ≡α swap y b (` c · ` b)
        qed y y∉ rewrite swapʳ y a | swapʳ y b
               | swap-noop y a c (λ where (here refl) → y∉ auto; (there (here ())))
               | swap-noop y b c (λ where (here refl) → y∉ auto; (there (here ())))
               = ξ≡ ν≡ ν≡

_ : (ƛ a ⇒ ` c) ≡α (ƛ b ⇒ ` c)
_ = ζ≡ (-, qed)
  where
    qed : ∀ y → y L.Mem.∉ [ c ] → swap y a (` c) ≡α swap y b (` c)
    qed y y∉
     rewrite swap-noop y a c (λ where (here refl) → y∉ auto; (there (here ())))
           | swap-noop y b c (λ where (here refl) → y∉ auto; (there (here ())))
           = ν≡

{-
  ¬equiv : ¬ (∀ t t′ 𝕒 𝕓 → t ≡α t′ → swap 𝕒 𝕓 t ≡α swap 𝕒 𝕓 t′)
  ¬equiv p = {!absurd!}
    where
        _t  = ƛ a ⇒ ` c
        _t′ = ƛ b ⇒ ` c

        eq : _t ≡α _t′
        eq = ζ≡ (-, qed)
          where
          qed : ∀ y → y L.Mem.∉ [ c ] → swap y a (` c) ≡α swap y b (` c)
          qed y y∉
            rewrite swap-noop y a c (λ where (here refl) → y∉ auto; (there (here ())))
                    | swap-noop y b c (λ where (here refl) → y∉ auto; (there (here ())))
                    = ν≡

        absurd : swap a c _t ≡α swap a c _t′
        absurd = p _t _t′ a c eq
-}

-- _ : (ƛ c ⇒ ƛ a ⇒ ` c · ` a) ≡α (ƛ c ⇒ ƛ b ⇒ ` c · ` b)
-- _ = ζ≡ (-, qed)
--   where
--     qed : ∀ y → y L.Mem.∉ [ a ]
--         → swap y c (ƛ a ⇒ ` c · ` a) ≡α swap y c (ƛ b ⇒ ` c · ` b)
--     qed y _ rewrite swapʳ y a | swapʳ y b = {!h!}

-- _ : (ƛ c ⇒ ƛ a ⇒ ` c · ` a) ≡α (ƛ d ⇒ ƛ b ⇒ ` d · ` b)
-- _ : (ƛ c ⇒ ƛ a ⇒ ` c · ` a) ≢α (ƛ d ⇒ ƛ b ⇒ ` c · ` b)

-- ** finite support

ex : Term
ex = ƛ a ⇒ ` a · ` a

suppEx = Atoms ∋ []
suppEx⁺ = Atoms ∋ [ a ]

finEx : FinSupp ex
finEx = -, go
  where
    go : ∀ 𝕒 𝕓 → 𝕒 ∉ suppEx⁺ → 𝕓 ∉ suppEx⁺ → swap 𝕓 𝕒 ex ≡α ex
    go 𝕒 𝕓 𝕒∉ 𝕓∉
      rewrite swap-noop 𝕓 𝕒 a (λ where ♯0 → 𝕓∉ auto; ♯1 → 𝕒∉ auto)
            = ≡α-refl _

_ = supp ex finEx ≡ suppEx⁺
  ∋ refl

finEx′ : FinSupp ex
finEx′ = fin ex

-- _ = supp ex finEx′ ≡ suppEx
--   ∋ refl

-- ** substitution

-- _ = (` a) [ a ↝ ` b ] ≡ ` b
--   ∋ refl

-- _ = (` a) [ a ↝ ` b · ` b ] ≡ ` b · ` b
--   ∋ refl

-- _ = (` a · ` a) [ a ↝ ` b ] ≡ ` b · ` b
--   ∋ refl

-- _ = (` a · ` a) [ a ↝ ` b · ` b ]
--   ≡ (` b · ` b) · (` b · ` b)
--   ∋ refl

-- -- _ = (` a · (ƛ a ⇒ ` a)) [ a ↝ ` b ]
-- --   ≡ ` b · (ƛ a ⇒ ` a)
-- --   ∋ {!!}

-- -- _ = (` a · (ƛ c ⇒ ` c · ` a)) [ a ↝ ` b ]
-- --   ≡ (` b · (ƛ c ⇒ ` c · ` b))
-- --   ∋ {!!}
