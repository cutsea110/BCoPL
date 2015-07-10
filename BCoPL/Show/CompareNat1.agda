module BCoPL.Show.CompareNat1 where

open import Data.String
open import BCoPL.Nat
open import BCoPL.CompareNat1

showDerivationLessThan : ∀ {n₁ n₂} → n₁ is-less-than n₂ → String

private
  showℕ : ℕ → String
  showℕ Z = "Z"
  showℕ (S n) = "S(" ++ showℕ n ++ ")"

  showJudgeLessThan : ∀ {n₁ n₂} → n₁ is-less-than n₂ → String
  showJudgeLessThan L-Succ = "L-Succ {};"
  showJudgeLessThan (L-Trans p q) = "L-Trans {" ++ showDerivationLessThan p ++ showDerivationLessThan q ++ "};"

  showDerivationLessThan {n₁} {n₂} p =
    showℕ n₁ ++ " is less than " ++ showℕ n₂ ++ " by " ++ showJudgeLessThan p
