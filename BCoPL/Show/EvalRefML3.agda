module BCoPL.Show.EvalRefML3 where

open import Data.String
open import Data.Nat.Show renaming (show to showℕ)
open import Data.Integer renaming (show to showℤ)
open import Data.Bool.Show renaming (show to show𝔹)
open import BCoPL.EvalRefML3 hiding (_++_)

showDerivation⇓ : ∀ {S₁ ε e v S₂} → S₁ ╱ ε ⊢ e ⇓ v ╱ S₂ → String
showStore : Store → String
showEnv : Env → String
showExp : Exp → String
showValue : Value → String

showBinding : BindedValue → String
showBinding (x , v) = x ++ " = " ++ showValue v

showStoring : StoredValue → String
showStoring (l , v) = l ++ " = " ++ showValue v

showEnv ● = ""
showEnv (● ⊱ x) = showBinding x
showEnv (ε ⊱ x) = showEnv ε ++ "," ++ showBinding x

showStoreBefore : Store → String
showStoreBefore ● = ""
showStoreBefore s = showStore s ++ " / "
showStoreAfter : Store → String
showStoreAfter ● = ""
showStoreAfter s = " / " ++ showStore s

showStore ● = ""
showStore (● ⊱ x) = showStoring x
showStore (s ⊱ x) = showStore s ++ "," ++ showStoring x

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
showExp (ref e) = "(ref " ++ showExp e ++ ")"
showExp (! e) = "(! " ++ showExp e ++ ")"
showExp (e₁ ≔ e₂) = "(" ++ showExp e₁ ++ " := " ++ showExp e₂ ++ ")"

showValue error = "*** Error occured by illegal Value ***"
showValue (i n) = showℤ n
showValue (b v) = show𝔹 v
showValue (⟨ ε ⟩[fun x ⇒ e ])
  = "(" ++ showEnv ε ++ ")[fun " ++ x ++ " -> " ++ showExp e ++ "]"
showValue (⟨ ε ⟩[rec f ≔fun x ⇒ e₁ ])
  = "(" ++ showEnv ε ++ ")[rec " ++ f ++ " = fun " ++ x ++ " -> " ++ showExp e₁ ++ "]"
showValue (ℓ l) = l

showDerivationPlus : ∀ {i₁ i₂ i₃} → i₁ plus i₂ is i₃ → String
showDerivationPlus {i₁} {i₂} {i₃} p
  = showValue i₁ ++ " plus " ++ showValue i₂ ++ " is " ++ showValue i₃ ++ " by B-Plus {};"
showDerivationMinus : ∀ {i₁ i₂ i₃} → i₁ minus i₂ is i₃ → String
showDerivationMinus {i₁} {i₂} {i₃} p
  = showValue i₁ ++ " minus " ++ showValue i₂ ++ " is " ++ showValue i₃ ++ " by B-Minus {};"
showDerivationTimes : ∀ {i₁ i₂ i₃} → i₁ times i₂ is i₃ → String
showDerivationTimes {i₁} {i₂} {i₃} p
  = showValue i₁ ++ " times " ++ showValue i₂ ++ " is " ++ showValue i₃ ++ " by B-Mult {};"
showDerivationLessThan : ∀ {i₁ i₂ b} → i₁ less-than i₂ is b → String
showDerivationLessThan {i₁} {i₂} {v} p
  = showValue i₁ ++ " less than " ++ showValue i₂ ++ " is " ++ showValue v ++ " by B-Lt {};"

showJudge⇓ : ∀ {S₁ ε e v S₂} → S₁ ╱ ε ⊢ e ⇓ v ╱ S₂ → String
showJudge⇓ E-Int = "E-Int {};"
showJudge⇓ E-Bool = "E-Bool {};"
showJudge⇓ (E-IfT d₁ d₂)
  = "E-IfT {" ++ showDerivation⇓ d₁ ++ showDerivation⇓ d₂ ++ "};"
showJudge⇓ (E-IfF d₁ d₂)
  = "E-IfF {" ++ showDerivation⇓ d₁ ++ showDerivation⇓ d₂ ++ "};"
showJudge⇓ (E-Plus d₁ d₂ p)
  = "E-Plus {" ++ showDerivation⇓ d₁ ++ showDerivation⇓ d₂ ++ showDerivationPlus p ++ "};"
showJudge⇓ (E-Minus d₁ d₂ p)
  = "E-Minus {" ++ showDerivation⇓ d₁ ++ showDerivation⇓ d₂ ++ showDerivationMinus p ++ "};"
showJudge⇓ (E-Mult d₁ d₂ p)
  = "E-Mult {" ++ showDerivation⇓ d₁ ++ showDerivation⇓ d₂ ++ showDerivationTimes p ++ "};"
showJudge⇓ (E-Lt d₁ d₂ p)
  = "E-Lt {" ++ showDerivation⇓ d₁ ++ showDerivation⇓ d₂ ++ showDerivationLessThan p ++ "};"
showJudge⇓ (E-Var prf) = "E-Var {};"
showJudge⇓ (E-Let d₁ d₂)
  = "E-Let {" ++ showDerivation⇓ d₁ ++ showDerivation⇓ d₂ ++ "};"
showJudge⇓ E-Fun = "E-Fun {};"
showJudge⇓ (E-App d₁ d₂ d₃)
  = "E-App {" ++ showDerivation⇓ d₁ ++ showDerivation⇓ d₂ ++ showDerivation⇓ d₃ ++ "};"
showJudge⇓ (E-LetRec d)
  = "E-LetRec {" ++ showDerivation⇓ d ++ "};"
showJudge⇓ (E-AppRec d₁ d₂ d₃)
  = "E-AppRec {" ++ showDerivation⇓ d₁ ++ showDerivation⇓ d₂ ++ showDerivation⇓ d₃ ++ "};"
showJudge⇓ (E-Ref d prf)
  = "E-Ref {" ++ showDerivation⇓ d ++ "};"
showJudge⇓ (E-Deref d prf)
  = "E-Deref {" ++ showDerivation⇓ d ++ "};"
showJudge⇓ (E-Assign d₁ d₂ prf)
  = "E-Assign {" ++ showDerivation⇓ d₁ ++ showDerivation⇓ d₂ ++ "};"

showDerivation⇓ {S₁} {ε} {e} {v} {S₂} p = showStoreBefore S₁ ++ showEnv ε ++ " |- " ++ showExp e ++ " evalto " ++ showValue v ++ showStoreAfter S₂ ++ " by " ++ showJudge⇓ p
