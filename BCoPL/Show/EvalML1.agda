module BCoPL.Show.EvalML1 where

open import Data.String
open import Data.Nat.Show renaming (show to showℕ)
open import Data.Integer renaming (show to showℤ)
open import Data.Bool.Show renaming (show to show𝔹)
open import BCoPL.EvalML1

showDerivation⇓ : ∀ {e v} → e ⇓ v → String
showExp : Exp → String

showExp (i n) = showℤ n
showExp (b v) = show𝔹 v
showExp (e₁ ⊕ e₂) = showExp e₁ ++ " + " ++ showExp e₂
showExp (e₁ ⊝ e₂) = showExp e₁ ++ " - " ++ showExp e₂
showExp (e₁ ⊛ e₂) = showExp e₁ ++ " * " ++ showExp e₂
showExp (e₁ ≺ e₂) = showExp e₁ ++ " < " ++ showExp e₂
showExp (if e₁ then e₂ else e₃) = "if " ++ showExp e₁ ++ " then " ++ showExp e₂ ++ " else " ++ showExp e₃

showValue : Value → String
showValue (i n) = showℤ n
showValue (b v) = show𝔹 v

showDerivationPlus : ∀ {i₁ i₂ i₃} → i₁ plus i₂ is i₃ → String
showDerivationPlus {i₁} {i₂} {i₃} p
  = showValue i₁ ++ " plus " ++ showValue i₂ ++ " is " ++ showValue i₃ ++ " by B-Plus {};"
showDerivationMinus : ∀ {i₁ i₂ i₃} → i₁ minus i₂ is i₃ → String
showDerivationMinus {i₁} {i₂} {i₃} p
  = showValue i₁ ++ " minus " ++ showValue i₂ ++ " is " ++ showValue i₃ ++ " by B-Minus {};"
showDerivationTimes : ∀ {i₁ i₂ i₃} → i₁ times i₂ is i₃ → String
showDerivationTimes {i₁} {i₂} {i₃} p
  = showValue i₁ ++ " times " ++ showValue i₂ ++ " is " ++ showValue i₃ ++ " by B-Times {};"
showDerivationLessThan : ∀ {i₁ i₂ b} → i₁ less-than i₂ is b → String
showDerivationLessThan {i₁} {i₂} {v} p
  = showValue i₁ ++ " less than " ++ showValue i₂ ++ " is " ++ showValue v ++ " by B-Lt {};"

showJudge⇓ : ∀ {e v} → e ⇓ v → String
showJudge⇓ E-Int = "E-Int {};"
showJudge⇓ E-Bool = "E-Bool {};"
showJudge⇓ (E-IfT e₁ e₂) = "E-IfT {" ++ showDerivation⇓ e₁ ++ showDerivation⇓ e₂ ++ "};"
showJudge⇓ (E-IfF e₁ e₂) = "E-IfF {" ++ showDerivation⇓ e₁ ++ showDerivation⇓ e₂ ++ "};"
showJudge⇓ (E-Plus e₁ e₂ p) = "E-Plus {" ++ showDerivation⇓ e₁ ++ showDerivation⇓ e₂ ++ showDerivationPlus p ++ "};"
showJudge⇓ (E-Minus e₁ e₂ p) = "E-Minus {" ++ showDerivation⇓ e₁ ++ showDerivation⇓ e₂ ++ showDerivationMinus p ++ "};"
showJudge⇓ (E-Times e₁ e₂ p) = "E-Times {" ++ showDerivation⇓ e₁ ++ showDerivation⇓ e₂ ++ showDerivationTimes p ++ "};"
showJudge⇓ (E-Lt e₁ e₂ p) = "E-Lt {" ++ showDerivation⇓ e₁ ++ showDerivation⇓ e₂ ++ showDerivationLessThan p ++ "};"

showDerivation⇓ {e} {v} p = showExp e ++ " evalto " ++ showValue v ++ " by " ++ showJudge⇓ p
