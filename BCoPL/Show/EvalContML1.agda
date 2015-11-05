module BCoPL.Show.EvalContML1 where

open import Data.String
open import Data.Nat.Show renaming (show to showℕ)
open import Data.Integer renaming (show to showℤ)
open import Data.Bool.Show renaming (show to show𝔹)
open import BCoPL.EvalContML1

showDerivation⇓ : ∀ {e k v} → e ≫ k ⇓ v → String
showDerivation⇒ : ∀ {v₁ k v₂} → v₁ ⇒ k ⇓ v₂ → String
showExp : Exp → String

showExp (i n) = showℤ n
showExp (b v) = show𝔹 v
showExp (op prim⊕ e₁ e₂) = "(" ++ showExp e₁ ++ " + " ++ showExp e₂ ++ ")"
showExp (op prim⊝ e₁ e₂) = "(" ++ showExp e₁ ++ " - " ++ showExp e₂ ++ ")"
showExp (op prim⊛ e₁ e₂) = "(" ++ showExp e₁ ++ " * " ++ showExp e₂ ++ ")"
showExp (op prim≺ e₁ e₂) = "(" ++ showExp e₁ ++ " < " ++ showExp e₂ ++ ")"
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

showPrim : Prim → String
showPrim prim⊕ = " + "
showPrim prim⊝ = " - "
showPrim prim⊛ = " * "
showPrim prim≺ = " < "

showSection : Section → String
showSection (⊗ <$ e) = "_ " ++ showPrim ⊗ ++ " " ++ showExp e
showSection (v $> ⊗) = showValue v ++ " " ++ showPrim ⊗ ++ " _"
showSection (if⋆then e₁ else e₂) = "if _ then " ++ showExp e₁ ++ " else " ++ showExp e₂

showCont : Cont → String
showCont ⋆ = "_"
showCont (⟦ sop ⟧≫ cont) = "{" ++ showSection sop ++ "} >> " ++ showCont cont

showJudge⇒ : ∀ {v₁ v₂ k} → v₁ ⇒ k ⇓ v₂ → String
showJudge⇒ C-Ret = "C-Ret {};"
showJudge⇒ (C-EvalR d) = "C-EvalR {" ++ showDerivation⇓ d ++ "};"
showJudge⇒ (C-Plus p d) = "C-Plus {" ++ showDerivationPlus p ++ showDerivation⇒ d ++ "};"
showJudge⇒ (C-Minus p d) = "C-Minus {" ++ showDerivationMinus p ++ showDerivation⇒ d ++ "};"
showJudge⇒ (C-Times p d) = "C-Times {" ++ showDerivationTimes p ++ showDerivation⇒ d ++ "};"
showJudge⇒ (C-Lt p d) = "C-Lt {" ++ showDerivationLessThan p ++ showDerivation⇒ d ++ "};"
showJudge⇒ (C-IfT d) = "C-IfT {" ++ showDerivation⇓ d ++ "};"
showJudge⇒ (C-IfF d) = "C-IfF {" ++ showDerivation⇓ d ++ "};"

showJudge⇓ : ∀ {e k v} → e ≫ k ⇓ v → String
showJudge⇓ (E-Int p) = "E-Int {" ++ showDerivation⇒ p ++ "};"
showJudge⇓ (E-Bool p) = "E-Bool {" ++ showDerivation⇒ p ++ "};"
showJudge⇓ (E-BinOp p) = "E-BinOp {" ++ showDerivation⇓ p ++ "};"
showJudge⇓ (E-If p) = "E-If {" ++ showDerivation⇓ p ++ "};"

showDerivation⇒ {v₁} {k} {v₂} p = showValue v₁ ++ " => " ++ showCont k ++ " evalto " ++ showValue v₂ ++ " by " ++ showJudge⇒ p
showDerivation⇓ {e} {k} {v} p = showExp e ++ " >> " ++ showCont k ++ " evalto " ++ showValue v ++ " by " ++ showJudge⇓ p
