module BCoPL.Nat where

open import Data.Nat renaming (ℕ to ℕ; zero to Z; suc to S) public

-- Nat
data _plus_is_ : ℕ → ℕ → ℕ → Set where
  P-Zero : ∀ {n} → Z plus n is n
  P-Succ : ∀ {n₁ n₂ n₃} → n₁ plus n₂ is n₃ → S n₁ plus n₂ is S n₃

data _times_is_ : ℕ → ℕ → ℕ → Set where
  T-Zero : ∀ {n} → Z times n is Z
  T-Succ : ∀ {n₁ n₂ n₃ n₄} → n₁ times n₂ is n₃ → n₂ plus n₃ is n₄ → S n₁ times n₂ is n₄
