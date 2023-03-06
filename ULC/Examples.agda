module ULC.Examples where

open import Prelude.Init; open SetAsType
open L.Mem
open import Prelude.DecEq
open import Prelude.Nary
open import Prelude.Decidable
open import Prelude.Setoid
open import Prelude.General
open import Prelude.InfEnumerable
open import Prelude.Semigroup

-- ** instantiate atoms to be the natural numbers
record Atom : Type where
  constructor $_
  field un$ : ℕ
open Atom public
unquoteDecl DecEq-Atom = DERIVE DecEq [ quote Atom , DecEq-Atom ]
instance
  Enum-Atom : Enumerable∞ Atom
  Enum-Atom .enum = Fun.mk↔ {f = un$} {$_} ((λ _ → refl) , (λ _ → refl))
open import Nominal Atom
open import ULC     Atom
  as ULC
  hiding (z)

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

  _ : (ƛ c ⇒ ƛ a ⇒ ` c · ` a) ≡α (ƛ c ⇒ ƛ b ⇒ ` c · ` b)
  _ = ζ≡ (-, qed)
    where
      qed : ∀ y → y L.Mem.∉ [ a ]
          → swap y c (ƛ a ⇒ ` c · ` a) ≡α swap y c (ƛ b ⇒ ` c · ` b)
      qed y _ rewrite swapʳ y a | swapʳ y b = {!h!}

  _ : (ƛ c ⇒ ƛ a ⇒ ` c · ` a) ≡α (ƛ d ⇒ ƛ b ⇒ ` d · ` b)
  _ : (ƛ c ⇒ ƛ a ⇒ ` c · ` a) ≢α (ƛ d ⇒ ƛ b ⇒ ` c · ` b)
-}

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
      rewrite swap-noop 𝕓 𝕒 a (λ where 𝟘 → 𝕓∉ auto; 𝟙 → 𝕒∉ auto)
            = ≡α-refl _

_ = finEx .proj₁ ≡ suppEx⁺
  ∋ refl

_ = supp ex
  ≡ (a ∷ a ∷ a ∷ [])
  ∋ refl

-- ** substitution

_ = (` a) [ a / ` b ] ≡ ` b
  ∋ refl

_ = (` a) [ a / ` b · ` b ] ≡ ` b · ` b
  ∋ refl

_ = (` a · ` a) [ a / ` b ] ≡ ` b · ` b
  ∋ refl

_ = (` a · ` a) [ a / ` b · ` b ] ≡ (` b · ` b) · (` b · ` b)
  ∋ refl

a' = $ 0 -- fresh in [a, b]

_ = (ƛ a ⇒ ` a) [ a / ` b ] ≡ (ƛ a' ⇒ ` a')
  ∋ refl

_ = (` a · (ƛ a ⇒ ` a)) [ a / ` b ] ≡ ` b · (ƛ a' ⇒ ` a')
  ∋ refl

b' = $ 0 -- fresh in [b, c]

_ = (ƛ b ⇒ ` b) [ b / ` c ] ≡ (ƛ b' ⇒ ` b')
  ∋ refl

c' = $ 0 -- fresh in [a, b, c]

_ = (` a · (ƛ c ⇒ ` c · ` a)) [ a / ` b ] ≡ (` b · (ƛ c' ⇒ ` c' · ` b))
  ∋ refl

_ = (` a · (ƛ c ⇒ ` c · ` a)) [ a / ` c' ] ≢ (` c' · (ƛ c' ⇒ ` c' · ` c'))
  ∋ λ ()

c'' = $ 1 -- fresh in [a, c, c']

_ = (` a · (ƛ c ⇒ ` c · ` a)) [ a / ` c' ] ≡ (` c' · (ƛ c'' ⇒ ` c'' · ` c'))
  ∋ refl

-- ** barendregt
a'' = $ 1 -- fresh in [a]

_ = barendregt (ƛ a ⇒ ƛ a ⇒ ` a · ` a) ≡ (ƛ a' ⇒ ƛ a'' ⇒ ` a'' · ` a'')
  ∋ refl

_ = barendregt ((ƛ a ⇒ ` a) · (ƛ a ⇒ ` a)) ≡ ((ƛ a' ⇒ ` a') · (ƛ a' ⇒ ` a'))
  ∋ refl

-- ** grown-up substitution
{-
_ = (abs a $ ` a) ULC.[ ` b ] ≡ (` b)
  ∋ refl

_ = (abs b $ ` b) ULC.[ ` c ] ≡ (` c)
  ∋ refl

_ = (abs c $ ` c · ` a) ULC.[ ` b ] ≡ (` b · ` a)
  ∋ refl

_ = (abs b $ ` a) ULC.[ ` b ] ≡ (` a)
  ∋ refl

_ = (abs b $ ` a · ` b) ULC.[ ` c ] ≡ (` a · ` c)
  ∋ refl

_ = (abs b $ ƛ a ⇒ ` a) ULC.[ ` b ] ≡ (ƛ c'' ⇒ ` c'')
  ∋ refl
-}
