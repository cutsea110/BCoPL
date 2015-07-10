module BCoPL.CompareNat1 where

open import Data.Nat renaming (ℕ to ℕ; zero to Z; suc to S) public

data _is-less-than_ : ℕ → ℕ → Set where
  L-Succ : ∀ {n} → n is-less-than S n
  L-Trans : ∀ {n₁ n₂ n₃} → n₁ is-less-than n₂ → n₂ is-less-than n₃ → n₁ is-less-than n₃
