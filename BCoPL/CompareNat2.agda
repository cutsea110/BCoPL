module BCoPL.CompareNat2 where

open import Data.Nat renaming (ℕ to ℕ; zero to Z; suc to S) public

data _is-less-than_ : ℕ → ℕ → Set where
  L-Zero : ∀ {n} → Z is-less-than S n
  L-SuccSucc : ∀ {n₁ n₂} → n₁ is-less-than n₂ → S n₁ is-less-than S n₂
