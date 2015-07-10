module BCoPL.Show.EvalNatExp where

open import Data.String
open import BCoPL.Nat
open import BCoPL.EvalNatExp
open import BCoPL.Show.Nat public

showDerivation⇓ : ∀ {e n} → e ⇓ n → String
showExp : Exp → String

private
  showExp (Nat n) = showℕ n
  showExp (e₁ ⊕ e₂) = showExp e₁ ++ " + " ++ showExp e₂
  showExp (e₁ ⊛ e₂) = showExp e₁ ++ " * " ++ showExp e₂

  showJudge⇓ : ∀ {e n} → e ⇓ n → String
  showJudge⇓ E-Const = "E-Const {};"
  showJudge⇓ (E-Plus r₁ r₂ p) =
    "E-Plus {" ++ showDerivation⇓ r₁ ++ showDerivation⇓ r₂ ++ showDerivationPlus p  ++ "};"
  showJudge⇓ (E-Times r₁ r₂ p) =
    "E-Times {" ++ showDerivation⇓ r₁ ++ showDerivation⇓ r₂ ++ showDerivationTimes p  ++ "};"

  showDerivation⇓ {e} {n} p = showExp e ++ " evalto " ++ showℕ n ++ " by " ++ showJudge⇓ p
