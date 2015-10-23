module BCoPL.Show.EvalNamelessML3 where

open import Data.String
open import Data.Nat.Show renaming (show to showℕ)
open import Data.Integer renaming (show to showℤ)
open import Data.Bool.Show renaming (show to show𝔹)
open import BCoPL.EvalNamelessML3

showDerivation⇓ : ∀ {ν e d} → ν ⊢ e ⇓ d → String
showVarList : VarList → String
showExp : Exp → String
showDBExp : DBExp → String

showVarList ● = ""
showVarList (● ⊱ x) = x
showVarList (χ ⊱ x) = showVarList χ ++ "," ++ x

showExp (i n) = showℤ n
showExp (b v) = show𝔹 v
showExp (var x) = x
showExp (op prim⊕ e₁ e₂) = "(" ++ showExp e₁ ++ " + " ++ showExp e₂ ++ ")"
showExp (op prim⊝ e₁ e₂) = "(" ++ showExp e₁ ++ " - " ++ showExp e₂ ++ ")"
showExp (op prim⊛ e₁ e₂) = "(" ++ showExp e₁ ++ " * " ++ showExp e₂ ++ ")"
showExp (op prim≺ e₁ e₂) = "(" ++ showExp e₁ ++ " < " ++ showExp e₂ ++ ")"
showExp (if e₁ then e₂ else e₃) = "if " ++ showExp e₁ ++ " then " ++ showExp e₂ ++ " else " ++ showExp e₃
showExp (ℓet x ≔ e₁ ιn e₂) = "let " ++ x ++ " = " ++ showExp e₁ ++ " in " ++ showExp e₂
showExp (ℓetrec f ≔fun x ⇒ e₁ ιn e₂) = "let rec " ++ f ++ " = fun " ++ x ++ " -> " ++ showExp e₁ ++ " in " ++ showExp e₂
showExp (fun x ⇒ e) = "(fun " ++ x ++ " -> " ++ showExp e ++ ")"
showExp (app e₁ e₂) = showExp e₁ ++ "(" ++ showExp e₂ ++ ")"

showDBValueList : DBValueList → String

showDBValue : DBValue → String
showDBValue error = "*** Error occured by illegal DBValue! ***"
showDBValue (i n) = showℤ n
showDBValue (b v) = show𝔹 v
showDBValue ⟨ ν ⟩[fuṇ⇒ e ] = "(" ++ showDBValueList ν ++ ")[fun . -> " ++ showDBExp e ++ "]"
showDBValue ⟨ ν ⟩[rec̣≔fuṇ⇒ e ] = "(" ++ showDBValueList ν ++ ")[rec . = fun . -> " ++ showDBExp e ++ "]"

showDBValueList ● = ""
showDBValueList (● ⊱ w) = showDBValue w
showDBValueList (ν ⊱ w) = showDBValueList ν ++ "," ++ showDBValue w

showDBExp (i n) = showℤ n
showDBExp (b v) = show𝔹 v
showDBExp (# idx) = "#" ++ showℕ idx
showDBExp (op prim⊕ d₁ d₂) = "(" ++ showDBExp d₁ ++ " + " ++ showDBExp d₂ ++ ")"
showDBExp (op prim⊝ d₁ d₂) = "(" ++ showDBExp d₁ ++ " - " ++ showDBExp d₂ ++ ")"
showDBExp (op prim⊛ d₁ d₂) = "(" ++ showDBExp d₁ ++ " * " ++ showDBExp d₂ ++ ")"
showDBExp (op prim≺ d₁ d₂) = "(" ++ showDBExp d₁ ++ " < " ++ showDBExp d₂ ++ ")"
showDBExp (if d₁ then d₂ else d₃) = "if " ++ showDBExp d₁ ++ " then " ++ showDBExp d₂ ++ " else " ++ showDBExp d₃
showDBExp (ℓeṭ≔ d₁ ιn d₂) = "let . = " ++ showDBExp d₁ ++ " in " ++ showDBExp d₂
showDBExp (ℓetrec̣≔fuṇ⇒ d₁ ιn d₂) = "let rec . = fun . -> " ++ showDBExp d₁ ++ " in " ++ showDBExp d₂
showDBExp (fuṇ⇒ d) = "(fun . -> " ++ showDBExp d ++ ")"
showDBExp (app d₁ d₂) = showDBExp d₁ ++ "(" ++ showDBExp d₂ ++ ")"

showValue : DBValue → String
showValue error = "*** Error occured by illegal DBValue ***"
showValue (i n) = showℤ n
showValue (b v) = show𝔹 v
showValue ⟨ ν ⟩[fuṇ⇒ e ] = "(" ++ showDBValueList ν ++ ")[fun . -> " ++ showDBExp e ++ "]"
showValue ⟨ ν ⟩[rec̣≔fuṇ⇒ e ] = "(" ++ showDBValueList ν ++ ")[rec . = fun . -> " ++ showDBExp e ++ "]"

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

showJudge⇓ : ∀ {ε e v} → ε ⊢ e ⇓ v → String
showJudge⇓ E-Int = "E-Int {};"
showJudge⇓ E-Bool = "E-Bool {};"
showJudge⇓ (E-IfT p₁ p₂) = "E-IfT {" ++ showDerivation⇓ p₁ ++ showDerivation⇓ p₂ ++ "};"
showJudge⇓ (E-IfF p₁ p₂) = "E-IfF {" ++ showDerivation⇓ p₁ ++ showDerivation⇓ p₂ ++ "};"
showJudge⇓ (E-Plus p₁ p₂ x) = "E-Plus {" ++ showDerivation⇓ p₁ ++ showDerivation⇓ p₂ ++ showDerivationPlus x ++ "};"
showJudge⇓ (E-Minus p₁ p₂ x) = "E-Minus {" ++ showDerivation⇓ p₁ ++ showDerivation⇓ p₂ ++ showDerivationMinus x ++ "};"
showJudge⇓ (E-Times p₁ p₂ x) = "E-Times {" ++ showDerivation⇓ p₁ ++ showDerivation⇓ p₂ ++ showDerivationTimes x ++ "};"
showJudge⇓ (E-Lt p₁ p₂ x) = "E-Lt {" ++ showDerivation⇓ p₁ ++ showDerivation⇓ p₂ ++ showDerivationLessThan x ++ "};"
showJudge⇓ (E-Var prf) = "E-Var {};"
showJudge⇓ (E-Let p₁ p₂) = "E-Let {" ++ showDerivation⇓ p₁ ++ showDerivation⇓ p₂ ++ "};"
showJudge⇓ E-Fun = "E-Fun {};"
showJudge⇓ (E-App p₁ p₂ p₃) = "E-App {" ++ showDerivation⇓ p₁ ++ showDerivation⇓ p₂ ++ showDerivation⇓ p₃ ++ "};"
showJudge⇓ (E-LetRec p) = "E-LetRec {" ++ showDerivation⇓ p ++ "};"
showJudge⇓ (E-AppRec p₁ p₂ p₃) = "E-AppRec {" ++ showDerivation⇓ p₁ ++ showDerivation⇓ p₂ ++ showDerivation⇓ p₃ ++ "};"

showDerivation⇓ {ν} {e} {v} p = showDBValueList ν ++ " |- " ++ showDBExp e ++ " evalto " ++ showValue v ++ " by " ++ showJudge⇓ p
