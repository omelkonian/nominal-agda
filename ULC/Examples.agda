module ULC.Examples where

open import Prelude.Init
open import Prelude.DecEq
open import Prelude.Membership

-- ** instantiate atoms to be the natural numbers
data Atom : Set where
  $_ : ℕ → Atom
unquoteDecl DecEq-Atom = DERIVE DecEq [ quote Atom , DecEq-Atom ]
open import Nominal Atom
open import ULC     Atom

s = $ 0; z = $ 1; m = $ 2; n = $ 3
a = $ 10; b = $ 11; c = $ 12; d = $ 13; e = $ 14

private
  _ = (` a) ≡α (` a) ∋ ν≡

  _ : (ƛ a ⇒ ` a) ≡α (ƛ b ⇒ ` b)
  _ = ζ≡ (-, qed)
    where qed : ∀ y → y L.Mem.∉ [] → swap y a (` a) ≡α swap y b (` b)
          qed y _ rewrite swapʳ y a | swapʳ y b = ν≡

  -- _ : (ƛ c ⇒ ƛ a ⇒ ` c · ` a) ≡α (ƛ c ⇒ ƛ b ⇒ ` c · ` b)
  -- _ : (ƛ c ⇒ ƛ a ⇒ ` c · ` a) ≡α (ƛ d ⇒ ƛ b ⇒ ` d · ` b)
  -- _ : (ƛ c ⇒ ƛ a ⇒ ` c · ` a) ≢α (ƛ d ⇒ ƛ b ⇒ ` c · ` b)

  ex : Term
  ex = ƛ a ⇒ ` a · ` a

  suppEx = [ a ]

  finEx : FinSupp ex
  finEx = -, go
    where
      go : ∀ 𝕒 𝕓 → 𝕒 ∉ suppEx → 𝕓 ∉ suppEx → swap 𝕓 𝕒 ex ≡α ex
      go 𝕒 𝕓 𝕒∉ 𝕓∉ = {!!}
      --   with z ≟ 𝕓
      -- ... | yes refl rewrite ∀x∉suppG 𝕒∉ | ∀x∉suppG 𝕓∉ = refl
      -- ... | no _ with z ≟ 𝕒
      -- ... | yes refl rewrite ∀x∉suppG 𝕒∉ | ∀x∉suppG 𝕓∉ = refl
      -- ... | no _ = refl
