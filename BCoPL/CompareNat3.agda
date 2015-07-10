module BCoPL.CompareNat3 where

open import Data.Nat renaming (ℕ to ℕ; zero to Z; suc to S) public

data _is-less-than_ : ℕ → ℕ → Set where
  L-Succ : ∀ {n} → n is-less-than S n
  L-SuccR : ∀ {n₁ n₂} → n₁ is-less-than n₂ → n₁ is-less-than S n₂
