module BCoPL.Show.CompareNat2 where

open import Data.String
open import BCoPL.Nat
open import BCoPL.CompareNat2

showDerivationLessThan : ∀ {n₁ n₂} → n₁ is-less-than n₂ → String

private
  showℕ : ℕ → String
  showℕ Z = "Z"
  showℕ (S n) = "S(" ++ showℕ n ++ ")"

  showJudgeLessThan : ∀ {n₁ n₂} → n₁ is-less-than n₂ → String
  showJudgeLessThan L-Zero = "L-Zero {};"
  showJudgeLessThan (L-SuccSucc p) = "L-SuccSucc {" ++ showDerivationLessThan p ++ "};"

  showDerivationLessThan {n₁} {n₂} p =
    showℕ n₁ ++ " is less than " ++ showℕ n₂ ++ " by " ++ showJudgeLessThan p
