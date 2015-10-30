module BCoPL.Show.TypingML4 where

open import Data.String
open import Data.Nat.Show renaming (show to showℕ)
open import Data.Integer renaming (show to showℤ)
open import Data.Bool.Show renaming (show to show𝔹)

open import BCoPL.TypingML4
open import BCoPL.Show.EvalML4 public

showDerivationTypes : ∀ {Γ e τ} → Γ ⊢ e ∶ τ → String

private
  showBinding : (Var × Types) → String
  showTypes : Types → String
  showTEnv : TEnv → String

  showBinding (x , τ) = x ++ ":" ++ showTypes τ

  showTEnv ● = ""
  showTEnv (● ⊱ x) = showBinding x
  showTEnv (Γ ⊱ x) = showTEnv Γ ++ "," ++ showBinding x

  showTypes type-error = "*** Type Error! ***"
  showTypes bool = "bool"
  showTypes int = "int"
  showTypes (τ₁ ⇀ τ₂) = "(" ++ showTypes τ₁ ++ ")" ++ " -> " ++ showTypes τ₂
  showTypes (τ list) = "((" ++ showTypes τ ++ ") list)"

showJudgeTypes : ∀ {Γ e τ} → Γ ⊢ e ∶ τ → String
showJudgeTypes T-Int = "T-Int {};"
showJudgeTypes T-Bool = "T-Bool {};"
showJudgeTypes (T-If τ₁ τ₂ τ₃)
  = "T-If {" ++ showDerivationTypes τ₁ ++ showDerivationTypes τ₂ ++ showDerivationTypes τ₃ ++ "};"
showJudgeTypes (T-Plus τ₁ τ₂)
  = "T-Plus {" ++ showDerivationTypes τ₁ ++ showDerivationTypes τ₂ ++ "};"
showJudgeTypes (T-Minus τ₁ τ₂)
  = "T-Minus {" ++ showDerivationTypes τ₁ ++ showDerivationTypes τ₂ ++ "};"
showJudgeTypes (T-Times τ₁ τ₂)
  = "T-Times {" ++ showDerivationTypes τ₁ ++ showDerivationTypes τ₂ ++ "};"
showJudgeTypes (T-Lt τ₁ τ₂)
  = "T-Lt {" ++ showDerivationTypes τ₁ ++ showDerivationTypes τ₂ ++ "};"
showJudgeTypes (T-Var prf) = "T-Var {};"
showJudgeTypes (T-Let τ₁ τ₂) = "T-Let {" ++ showDerivationTypes τ₁ ++ showDerivationTypes τ₂ ++ "};"
showJudgeTypes (T-Fun τ) = "T-Fun {" ++ showDerivationTypes τ ++ "};"
showJudgeTypes (T-App τ₁ τ₂) = "T-App {" ++ showDerivationTypes τ₁ ++ showDerivationTypes τ₂ ++ "};"
showJudgeTypes (T-LetRec τ₁ τ₂) = "T-LetRec {" ++ showDerivationTypes τ₁ ++ showDerivationTypes τ₂ ++ "};"
showJudgeTypes T-Nil = "T-Nil {};"
showJudgeTypes (T-Cons τ₁ τ₂) = "T-Cons {" ++ showDerivationTypes τ₁ ++ showDerivationTypes τ₂ ++ "};"
showJudgeTypes (T-Match τ₁ τ₂ τ₃) = "T-Match {" ++ showDerivationTypes τ₁ ++ showDerivationTypes τ₂ ++ showDerivationTypes τ₃ ++ "};"

showDerivationTypes {Γ} {e} {τ} d
  = showTEnv Γ ++ " |- " ++ showExp e ++ " : " ++ showTypes τ ++ " by " ++ showJudgeTypes d
