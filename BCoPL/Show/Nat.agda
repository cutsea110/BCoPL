module BCoPL.Show.Nat where

open import Data.String
open import BCoPL.Nat

showDerivationPlus : ∀ {n₁ n₂ n₃} → n₁ plus n₂ is n₃ → String
showDerivationTimes : ∀ {n₁ n₂ n₃} → n₁ times n₂ is n₃ → String
showℕ : ℕ → String

private
  showℕ Z = "Z"
  showℕ (S n) = "S(" ++ showℕ n ++ ")"

  showJudgePlus : ∀ {n₁ n₂ n₃} → n₁ plus n₂ is n₃ → String
  showJudgePlus P-Zero = "P-Zero {};"
  showJudgePlus (P-Succ p) =  "P-Succ {" ++ showDerivationPlus p ++ "};"

  showDerivationPlus {n₁} {n₂} {n₃} p =
    showℕ n₁ ++ " plus " ++ showℕ n₂ ++ " is " ++ showℕ n₃ ++ " by " ++ showJudgePlus p

  showJudgeTimes : ∀ {n₁ n₂ n₃} → n₁ times n₂ is n₃ → String
  showJudgeTimes T-Zero = "T-Zero {};"
  showJudgeTimes (T-Succ t p) = "T-Succ {" ++ showDerivationTimes t ++ showDerivationPlus p ++ "};"

  showDerivationTimes {n₁} {n₂} {n₃} p =
    showℕ n₁ ++ " times " ++ showℕ n₂ ++ " is " ++ showℕ n₃ ++ " by " ++ showJudgeTimes p

