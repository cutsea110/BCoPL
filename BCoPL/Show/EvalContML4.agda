module BCoPL.Show.EvalContML4 where

open import Data.String
open import Data.Nat.Show renaming (show to showℕ)
open import Data.Integer renaming (show to showℤ)
open import Data.Bool.Show renaming (show to show𝔹)
open import BCoPL.EvalContML4

showDerivation⇓ : ∀ {ε e k v} → ε ⊢ e ≫ k ⇓ v → String
showDerivation⇒ : ∀ {v₁ k v₂} → v₁ ⇒ k ⇓ v₂ → String
showEnv : Env → String
showExp : Exp → String
showValue : Value → String
showCont : Cont → String

private
  showBinding : BindedValue → String
  showBinding (x , v) = x ++ " = " ++ showValue v

  showEnv ● = ""
  showEnv (● ⊱ x) = showBinding x
  showEnv (ε ⊱ x) = showEnv ε ++ "," ++ showBinding x

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
showExp (match e₁ with[]⇒ e₂ ∣ x ∷ y ⇒ e₃)
  = "match " ++ showExp e₁ ++ " with [] -> " ++ showExp e₂ ++ " | " ++ x ++ " :: " ++ y ++ " -> " ++ showExp e₃
showExp (letcc x ιn e)
  = "letcc " ++ x ++ " in " ++ showExp e

showValue error = "*** Error occured by illegal Value ***"
showValue (i n) = showℤ n
showValue (b v) = show𝔹 v
showValue (⟨ ε ⟩[fun x ⇒ e ])
  = "(" ++ showEnv ε ++ ")[fun " ++ x ++ " -> " ++ showExp e ++ "]"
showValue (⟨ ε ⟩[rec f ≔fun x ⇒ e₁ ])
  = "(" ++ showEnv ε ++ ")[rec " ++ f ++ " = fun " ++ x ++ " -> " ++ showExp e₁ ++ "]"
showValue [] = "[]"
showValue (x ∷ y) = "(" ++ showValue x ++ " :: " ++ showValue y ++ ")"
showValue (⟪ k ⟫) = "[" ++ showCont k ++ "]"

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
showSection (ε ⊢ ⊗ <$ e) = showEnv ε ++ " |- _ " ++ showPrim ⊗ ++ " " ++ showExp e
showSection (v $> ⊗) = " " ++ showValue v ++ showPrim ⊗ ++ " _"
showSection (ε ⊢if⋆then e₁ else e₂) = showEnv ε ++ " |- if _ then " ++ showExp e₁ ++ " else " ++ showExp e₂
showSection (ε ⊢let x ≔⋆in e) = showEnv ε ++ " |- let " ++ x ++ " = _ in " ++ showExp e
showSection (ε ⊢app⋆ e) = showEnv ε ++ " |- _ " ++ showExp e
showSection (v ⋆ppa) = showValue v ++ " _"
showSection (ε ⊢⋆∷ y) = showEnv ε ++ " |- _ :: " ++ showExp y
showSection (x ∷⋆) = " " ++ showValue x ++ " :: _"
showSection (ε ⊢match⋆with[]⇒ e₁ ∣ x ∷ y ⇒ e₂) = showEnv ε ++ " |- match _ with [] -> " ++ showExp e₁ ++ " | " ++ x ++ "::" ++ y ++ " -> " ++ showExp e₂

showCont ⋆ = "_"
showCont (⟦ sop ⟧≫ cont) = "{" ++ showSection sop ++ "} >> " ++ showCont cont

showJudge⇒ : ∀ {v₁ k v₂} → v₁ ⇒ k ⇓ v₂ → String
showJudge⇒ C-Ret = "C-Ret {};"
showJudge⇒ (C-EvalR d) = "C-EvalR {" ++ showDerivation⇓ d ++ "};"
showJudge⇒ (C-Plus p d) = "C-Plus {" ++ showDerivationPlus p ++ showDerivation⇒ d ++ "};"
showJudge⇒ (C-Minus p d) = "C-Minus {" ++ showDerivationMinus p ++ showDerivation⇒ d ++ "};"
showJudge⇒ (C-Times p d) = "C-Times {" ++ showDerivationTimes p ++ showDerivation⇒ d ++ "};"
showJudge⇒ (C-Lt p d) = "C-Lt {" ++ showDerivationLessThan p ++ showDerivation⇒ d ++ "};"
showJudge⇒ (C-IfT d) = "C-IfT {" ++ showDerivation⇓ d ++ "};"
showJudge⇒ (C-IfF d) = "C-IfF {" ++ showDerivation⇓ d ++ "};"
showJudge⇒ (C-LetBody d) = "C-LetBody {" ++ showDerivation⇓ d ++ "};"
showJudge⇒ (C-EvalArg d) = "C-EvalArg {" ++ showDerivation⇓ d ++ "};"
showJudge⇒ (C-EvalFun d) = "C-EvalFun {" ++ showDerivation⇓ d ++ "};"
showJudge⇒ (C-EvalFunR d) = "C-EvalFunR {" ++ showDerivation⇓ d ++ "};"
showJudge⇒ (C-EvalConsR d) = "C-EvalConsR {" ++ showDerivation⇓ d ++ "};"
showJudge⇒ (C-Cons d) = "C-Cons {" ++ showDerivation⇒ d ++ "};"
showJudge⇒ (C-MatchNil d) = "C-MatchNil {" ++ showDerivation⇓ d ++ "};"
showJudge⇒ (C-MatchCons d) = "C-MatchCons {" ++ showDerivation⇓ d ++ "};"
showJudge⇒ (C-EvalFunC d) = "C-EvalFunC {" ++ showDerivation⇒ d ++ "};"

showJudge⇓ : ∀ {ε e k v} → ε ⊢ e ≫ k ⇓ v → String
showJudge⇓ (E-Int p) = "E-Int {" ++ showDerivation⇒ p ++ "};"
showJudge⇓ (E-Bool p) = "E-Bool {" ++ showDerivation⇒ p ++ "};"
showJudge⇓ (E-BinOp p) = "E-BinOp {" ++ showDerivation⇓ p ++ "};"
showJudge⇓ (E-If p) = "E-If {" ++ showDerivation⇓ p ++ "};"
showJudge⇓ (E-Var x p) = "E-Var {" ++ showDerivation⇒ p ++ "};"
showJudge⇓ (E-Let p) = "E-Let {" ++ showDerivation⇓ p ++ "};"
showJudge⇓ (E-Fun p) = "E-Fun {" ++ showDerivation⇒ p ++ "};"
showJudge⇓ (E-App p) = "E-App {" ++ showDerivation⇓ p ++ "};"
showJudge⇓ (E-LetRec p) = "E-LetRec {" ++ showDerivation⇓ p ++ "};"
showJudge⇓ (E-Nil p) = "E-Nil {" ++ showDerivation⇒ p ++ "};"
showJudge⇓ (E-Cons p) = "E-Cons {" ++ showDerivation⇓ p ++ "};"
showJudge⇓ (E-Match p) = "E-Match {" ++ showDerivation⇓ p ++ "};"
showJudge⇓ (E-LetCc p) = "E-LetCc {" ++ showDerivation⇓ p ++ "};"

showDerivation⇒ {v₁} {k} {v₂} p = showValue v₁ ++ " => " ++ showCont k ++ " evalto " ++ showValue v₂ ++ " by " ++ showJudge⇒ p
showDerivation⇓ {ε} {e} {k} {v} p = showEnv ε ++ " |- " ++ showExp e ++ " >> " ++ showCont k ++ " evalto " ++ showValue v ++ " by " ++ showJudge⇓ p
