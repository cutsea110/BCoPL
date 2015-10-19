module BCoPL.Show.EvalML1Err where

open import Data.String
open import Data.Nat.Show renaming (show to showℕ)
open import Data.Integer renaming (show to showℤ)
open import Data.Bool.Show renaming (show to show𝔹)
open import BCoPL.EvalML1Err

showDerivation⇓ : ∀ {e v} → e ⇓ v → String
showExp : Exp → String

showExp (i n) = showℤ n
showExp (b v) = show𝔹 v
showExp (op prim⊕ e₁ e₂) = "(" ++ showExp e₁ ++ " + " ++ showExp e₂ ++ ")"
showExp (op prim⊝ e₁ e₂) = "(" ++ showExp e₁ ++ " - " ++ showExp e₂ ++ ")"
showExp (op prim⊛ e₁ e₂) = "(" ++ showExp e₁ ++ " * " ++ showExp e₂ ++ ")"
showExp (op prim≺ e₁ e₂) = "(" ++ showExp e₁ ++ " < " ++ showExp e₂ ++ ")"
showExp (if e₁ then e₂ else e₃) = "if " ++ showExp e₁ ++ " then " ++ showExp e₂ ++ " else " ++ showExp e₃

showError : Error → String
showError ε = "error"

showValue : Value → String
showValue (right (i n)) = showℤ n
showValue (right (b v)) = show𝔹 v
showValue (left err) = showError err

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

showJudge⇓ (E-IfInt e₁) = "E-IfInt {" ++ showDerivation⇓ e₁ ++ "};"
showJudge⇓ (E-PlusBoolL e₁) = "E-PlusBoolL {" ++ showDerivation⇓ e₁ ++ "};"
showJudge⇓ (E-PlusBoolR e₁) = "E-PlusBoolR {" ++ showDerivation⇓ e₁ ++ "};"
showJudge⇓ (E-MinusBoolL e₁) = "E-MinusBoolL {" ++ showDerivation⇓ e₁ ++ "};"
showJudge⇓ (E-MinusBoolR e₁) = "E-MinusBoolR {" ++ showDerivation⇓ e₁ ++ "};"
showJudge⇓ (E-TimesBoolL e₁) = "E-TimesBoolL {" ++ showDerivation⇓ e₁ ++ "};"
showJudge⇓ (E-TimesBoolR e₁) = "E-TimesBoolR {" ++ showDerivation⇓ e₁ ++ "};"
showJudge⇓ (E-LtBoolL e₁) = "E-LtBoolL {" ++ showDerivation⇓ e₁ ++ "};"
showJudge⇓ (E-LtBoolR e₁) = "E-LtBoolR {" ++ showDerivation⇓ e₁ ++ "};"
showJudge⇓ (E-IfError p) = "E-IfError {" ++ showDerivation⇓ p ++ "};"
showJudge⇓ (E-IfTError (e₁ , e₂)) = "E-IfTError {" ++ showDerivation⇓ e₁ ++ showDerivation⇓ e₂ ++ "};"
showJudge⇓ (E-IfFError (e₁ , e₂)) = "E-IfFError {" ++ showDerivation⇓ e₁ ++ showDerivation⇓ e₂ ++ "};"
showJudge⇓ (E-PlusErrorL p) = "E-PlusErrorL {" ++ showDerivation⇓ p ++ "};"
showJudge⇓ (E-PlusErrorR p) = "E-PlusErrorR {" ++ showDerivation⇓ p ++ "};"
showJudge⇓ (E-MinusErrorL p) = "E-MinusErrorL {" ++ showDerivation⇓ p ++ "};"
showJudge⇓ (E-MinusErrorR p) = "E-MinusErrorR {" ++ showDerivation⇓ p ++ "};"
showJudge⇓ (E-TimesErrorL p) = "E-TimesErrorL {" ++ showDerivation⇓ p ++ "};"
showJudge⇓ (E-TimesErrorR p) = "E-TimesErrorR {" ++ showDerivation⇓ p ++ "};"
showJudge⇓ (E-LtErrorL p) = "E-LtErrorL {" ++ showDerivation⇓ p ++ "};"
showJudge⇓ (E-LtErrorR p) = "E-LtErrorR {" ++ showDerivation⇓ p ++ "};"

showDerivation⇓ {e} {v} p = showExp e ++ " evalto " ++ showValue v ++ " by " ++ showJudge⇓ p
