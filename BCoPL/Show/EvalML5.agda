module BCoPL.Show.EvalML5 where

open import Data.String
open import Data.Nat.Show renaming (show to showℕ)
open import Data.Integer renaming (show to showℤ)
open import Data.Bool.Show renaming (show to show𝔹)
open import BCoPL.EvalML5

showDerivation⇓ : ∀ {ε e v} → ε ⊢ e ⇓ v → String
showEnv : Env → String
showExp : Exp → String
showValue : Value → String

showBinding : BindedValue → String
showBinding (x , v) = x ++ " = " ++ showValue v

showEnv ● = ""
showEnv (● ⊱ x) = showBinding x
showEnv (ε ⊱ x) = showEnv ε ++ "," ++ showBinding x

showPat : Pat → String
showPat (var x) = x
showPat [] = "[]"
showPat (x ∷ y) = "(" ++ showPat x ++ "::" ++ showPat y ++ ")"
showPat ̱ = "_"

showClauses : Clauses → String
showClauses (p ↦ e ̣) = showPat p ++ " -> " ++ showExp e
showClauses (p ↦ e ∣ c) = showPat p ++ " -> " ++ showExp e ++ " | " ++ showClauses c

showExp (i n) = showℤ n
showExp (b v) = show𝔹 v
showExp (var x) = x
showExp (op prim⊕ e₁ e₂) = "(" ++ showExp e₁ ++ " + " ++ showExp e₂ ++ ")"
showExp (op prim⊝ e₁ e₂) = "(" ++ showExp e₁ ++ " - " ++ showExp e₂ ++ ")"
showExp (op prim⊛ e₁ e₂) = "(" ++ showExp e₁ ++ " * " ++ showExp e₂ ++ ")"
showExp (op prim≺ e₁ e₂) = "(" ++ showExp e₁ ++ " < " ++ showExp e₂ ++ ")"
showExp (if e₁ then e₂ else e₃) = "if " ++ showExp e₁ ++ " then " ++ showExp e₂ ++ " else " ++ showExp e₃
showExp (ℓet x ≔ e₁ ιn e₂)
  = "let " ++ x ++ " = " ++ showExp e₁ ++ " in " ++ showExp e₂
showExp (ℓetrec f ≔fun x ⇒ e₁ ιn e₂)
  = "let rec " ++ f ++ " = fun " ++ x ++ " -> " ++ showExp e₁ ++ " in " ++ showExp e₂
showExp (fun x ⇒ e) = "(fun " ++ x ++ " -> " ++ showExp e ++ ")"
showExp (app e₁ e₂) = showExp e₁ ++ "(" ++ showExp e₂ ++ ")"
showExp [] = "[]"
showExp (x ∷ y) = "(" ++ showExp x ++ " :: " ++ showExp y ++ ")"
showExp (match e ωith c) = "(match " ++ showExp e ++ " with " ++ showClauses c ++ ")"

showValue error = "*** Error occured by illegal Value ***"
showValue (i n) = showℤ n
showValue (b v) = show𝔹 v
showValue (⟨ ε ⟩[fun x ⇒ e ])
  = "(" ++ showEnv ε ++ ")[fun " ++ x ++ " -> " ++ showExp e ++ "]"
showValue (⟨ ε ⟩[rec f ≔fun x ⇒ e₁ ])
  = "(" ++ showEnv ε ++ ")[rec " ++ f ++ " = fun " ++ x ++ " -> " ++ showExp e₁ ++ "]"
showValue [] = "[]"
showValue (x ∷ y) = "(" ++ showValue x ++ " :: " ++ showValue y ++ ")"


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
showJudge⇓ (E-Var prf) = "E-Var {};"
showJudge⇓ (E-IfT e₁ e₂) = "E-IfT {" ++ showDerivation⇓ e₁ ++ showDerivation⇓ e₂ ++ "};"
showJudge⇓ (E-IfF e₁ e₂) = "E-IfF {" ++ showDerivation⇓ e₁ ++ showDerivation⇓ e₂ ++ "};"
showJudge⇓ (E-Plus e₁ e₂ p) = "E-Plus {" ++ showDerivation⇓ e₁ ++ showDerivation⇓ e₂ ++ showDerivationPlus p ++ "};"
showJudge⇓ (E-Minus e₁ e₂ p) = "E-Minus {" ++ showDerivation⇓ e₁ ++ showDerivation⇓ e₂ ++ showDerivationMinus p ++ "};"
showJudge⇓ (E-Times e₁ e₂ p) = "E-Times {" ++ showDerivation⇓ e₁ ++ showDerivation⇓ e₂ ++ showDerivationTimes p ++ "};"
showJudge⇓ (E-Lt e₁ e₂ p) = "E-Lt {" ++ showDerivation⇓ e₁ ++ showDerivation⇓ e₂ ++ showDerivationLessThan p ++ "};"
showJudge⇓ (E-Let e₁ e₂) = "E-Let {" ++ showDerivation⇓ e₁ ++ showDerivation⇓ e₂ ++ "};"
showJudge⇓ (E-LetRec e₁) = "E-LetRec {" ++ showDerivation⇓ e₁ ++ "};"
showJudge⇓ E-Fun = "E-Fun {};"
showJudge⇓ (E-App e₁ e₂ e₃)
  = "E-App {" ++ showDerivation⇓ e₁ ++ showDerivation⇓ e₂ ++ showDerivation⇓ e₃ ++ "};"
showJudge⇓ (E-AppRec e₁ e₂ e₃)
  = "E-AppRec {" ++ showDerivation⇓ e₁ ++ showDerivation⇓ e₂ ++ showDerivation⇓ e₃ ++ "};"
showJudge⇓ E-Nil = "E-Nil {};"
showJudge⇓ (E-Cons e₁ e₂) = "E-Cons {" ++ showDerivation⇓ e₁ ++ showDerivation⇓ e₂ ++ "};"
showJudge⇓ (E-MatchM1 e₁ p₁ p₂ e₂) = {!!}
showJudge⇓ (E-MatchM2 e₁ p₁ p₂ e₂) = {!!}
showJudge⇓ (E-MatchN e₁ p₁ e₂) = {!!}

showDerivation⇓ {ε} {e} {v} p = showEnv ε ++ " |- " ++ showExp e ++ " evalto " ++ showValue v ++ " by " ++ showJudge⇓ p
