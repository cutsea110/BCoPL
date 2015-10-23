module BCoPL.Show.NamelessML3 where

open import Data.String
open import Data.Nat.Show renaming (show to showℕ)
open import Data.Integer renaming (show to showℤ)
open import Data.Bool.Show renaming (show to show𝔹)
open import BCoPL.NamelessML3

showDerivation⟾ : ∀ {ε e d} → ε ⊢ e ⟾ d → String
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

showJudge⟾ : ∀ {χ e d} → χ ⊢ e ⟾ d → String
showJudge⟾ TR-Int = "Tr-Int {};"
showJudge⟾ TR-Bool = "Tr-Bool {};"
showJudge⟾ (TR-If p₁ p₂ p₃) = "Tr-If {" ++ showDerivation⟾ p₁ ++ showDerivation⟾ p₂ ++ showDerivation⟾ p₃ ++ "};"
showJudge⟾ (TR-Plus p₁ p₂) = "Tr-Plus {" ++ showDerivation⟾ p₁ ++ showDerivation⟾ p₂ ++ "};"
showJudge⟾ (TR-Minus p₁ p₂) = "Tr-Minus {" ++ showDerivation⟾ p₁ ++ showDerivation⟾ p₂ ++ "};"
showJudge⟾ (TR-Times p₁ p₂) = "Tr-Times {" ++ showDerivation⟾ p₁ ++ showDerivation⟾ p₂ ++ "};"
showJudge⟾ (TR-Lt p₁ p₂) = "Tr-Lt {" ++ showDerivation⟾ p₁ ++ showDerivation⟾ p₂ ++ "};"
showJudge⟾ (TR-Var1 prf) = "Tr-Var1 {};"
showJudge⟾ (TR-Var2 prf p) = "Tr-Var2 {" ++ showDerivation⟾ p ++ "};"
showJudge⟾ (TR-Let p₁ p₂) = "Tr-Let {" ++ showDerivation⟾ p₁ ++ showDerivation⟾ p₂ ++ "};"
showJudge⟾ (TR-Fun p) = "Tr-Fun {" ++ showDerivation⟾ p ++ "};"
showJudge⟾ (TR-App p₁ p₂) = "Tr-App {" ++ showDerivation⟾ p₁ ++ showDerivation⟾ p₂ ++ "}"
showJudge⟾ (TR-LetRec p₁ p₂) = "Tr-LetRec {" ++ showDerivation⟾ p₁ ++ showDerivation⟾ p₂ ++ "};"


showDerivation⟾ {χ} {e} {d} p = showVarList χ ++ " |- " ++ showExp e ++ " ==> " ++ showDBExp d ++ " by " ++ showJudge⟾ p
