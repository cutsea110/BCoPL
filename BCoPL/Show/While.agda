module BCoPL.Show.While where

open import Data.String
open import Data.Nat.Show renaming (show to showℕ)
open import Data.Integer renaming (show to showℤ)
open import Data.Bool.Show renaming (show to show𝔹)
open import BCoPL.While

showDerivationChangesTo : ∀ {c σ₁ σ₂} → c changes σ₁ to σ₂ → String
showDerivation⇓ : ∀ {σ a₁ i₁} → σ ⊢ a₁ ⇓ i₁ → String
showDerivation↓ : ∀ {σ b₁ bv₁} → σ ⊢ b₁ ↓ bv₁ → String
showAExp : AExp → String
showBExp : BExp → String

showAExp (i n) = showℤ n
showAExp (var v) = v
showAExp (aop prim⊕ a₁ a₂) = "(" ++ showAExp a₁ ++ " + " ++ showAExp a₂ ++ ")"
showAExp (aop prim⊝ a₁ a₂) = "(" ++ showAExp a₁ ++ " - " ++ showAExp a₂ ++ ")"
showAExp (aop prim⊛ a₁ a₂) = "(" ++ showAExp a₁ ++ " * " ++ showAExp a₂ ++ ")"

showBExp (b v) = show𝔹 v
showBExp (! b₁) = "(!" ++ showBExp b₁ ++ ")"
showBExp (lop prim&& b₁ b₂) = "(" ++ showBExp b₁ ++ " && " ++ showBExp b₂ ++ ")"
showBExp (lop prim|| b₁ b₂) = "(" ++ showBExp b₁ ++ " || " ++ showBExp b₂ ++ ")"
showBExp (comp prim≺ a₁ a₂) = "(" ++ showAExp a₁ ++ " < " ++ showAExp a₂ ++ ")"
showBExp (comp prim≈ a₁ a₂) = "(" ++ showAExp a₁ ++ " == " ++ showAExp a₂ ++ ")"
showBExp (comp prim≼ a₁ a₂) = "(" ++ showAExp a₁ ++ " <= " ++ showAExp a₂ ++ ")"

showIValue : IValue → String
showIValue error = "*** Error occured! ***"
showIValue (i n) = showℤ n

showBValue : BValue → String
showBValue (b v) = show𝔹 v

showCom : Com → String
showCom skip = "skip"
showCom (x ≔ a) = x ++ ":=" ++ showAExp a
showCom (c₁ >> c₂) = showCom c₁ ++ ";" ++ showCom c₂
showCom (if b₁ then c₁ else c₂) = "if " ++ showBExp b₁ ++ " then " ++ showCom c₁ ++ " else " ++ showCom c₂
showCom (while b₁ do c) = "while (" ++ showBExp b₁ ++ ") do " ++ showCom c

showBinding : BindedValue → String
showBinding (x , v) = x ++ " = " ++ showIValue v

showStore : Store → String
showStore ● = ""
showStore (● ⊱ x) = showBinding x
showStore (σ ⊱ x) = showStore σ ++ "," ++ showBinding x

showDerivationPlus : ∀ {i₁ i₂ i₃} → i₁ plus i₂ is i₃ → String
showDerivationPlus {i₁} {i₂} {i₃} p
  = showIValue i₁ ++ " plus " ++ showIValue i₂ ++ " is " ++ showIValue i₃ ++ " by B-Plus {};"
showDerivationMinus : ∀ {i₁ i₂ i₃} → i₁ minus i₂ is i₃ → String
showDerivationMinus {i₁} {i₂} {i₃} p
  = showIValue i₁ ++ " minus " ++ showIValue i₂ ++ " is " ++ showIValue i₃ ++ " by B-Minus {};"
showDerivationTimes : ∀ {i₁ i₂ i₃} → i₁ times i₂ is i₃ → String
showDerivationTimes {i₁} {i₂} {i₃} p
  = showIValue i₁ ++ " times " ++ showIValue i₂ ++ " is " ++ showIValue i₃ ++ " by B-Times {};"
showDerivationLessThan : ∀ {i₁ i₂ b} → i₁ less-than i₂ is b → String
showDerivationLessThan {i₁} {i₂} {v} p
  = showIValue i₁ ++ " less than " ++ showIValue i₂ ++ " is " ++ showBValue v ++ " by B-Lt {};"

showJudge⇓ : ∀ {σ a₁ i₁} → σ ⊢ a₁ ⇓ i₁ → String
showJudge↓ : ∀ {σ b₁ bv₁} → σ ⊢ b₁ ↓ bv₁ → String


showJudge⇓ A-Const = "A-Const {};"
showJudge⇓ (A-Var p) = "A-Var {};"
showJudge⇓ (A-Plus p₁ p₂ prf) = "A-Plus {" ++ showDerivation⇓ p₁ ++ showDerivation⇓ p₂ ++ "};"
showJudge⇓ (A-Minus p₁ p₂ prf) = "A-Minus {" ++ showDerivation⇓ p₁ ++ showDerivation⇓ p₂ ++ "};"
showJudge⇓ (A-Times p₁ p₂ prf) = "A-Times {" ++ showDerivation⇓ p₁ ++ showDerivation⇓ p₂ ++ "};"

showJudge↓ B-Const = "B-Const {};"
showJudge↓ (B-Not p prf) = "B-Not {" ++ showDerivation↓ p ++ "};"
showJudge↓ (B-And p₁ p₂ prf) = "B-And {" ++ showDerivation↓ p₁ ++ showDerivation↓ p₂ ++ "};"
showJudge↓ (B-Or p₁ p₂ prf) = "B-Or {" ++ showDerivation↓ p₁ ++ showDerivation↓ p₂ ++ "};"
showJudge↓ (B-Lt p₁ p₂ prf) = "B-Lt {" ++ showDerivation⇓ p₁ ++ showDerivation⇓ p₂ ++ "};"
showJudge↓ (B-Eq p₁ p₂ prf) = "B-Eq {" ++ showDerivation⇓ p₁ ++ showDerivation⇓ p₂ ++ "};"
showJudge↓ (B-Le p₁ p₂ prf) = "B-Le {" ++ showDerivation⇓ p₁ ++ showDerivation⇓ p₂ ++ "};"

showJudgeChangesTo : ∀ {c σ₁ σ₂} → c changes σ₁ to σ₂ → String
showJudgeChangesTo C-Skip = "C-Skip {};"
showJudgeChangesTo (C-Assign d p)
  = "C-Assign {" ++ showDerivation⇓ d ++ "};"
showJudgeChangesTo (C-Seq d₁ d₂)
  = "C-Seq {" ++ showDerivationChangesTo d₁ ++ showDerivationChangesTo d₂ ++ "};"
showJudgeChangesTo (C-IfT p d)
  = "C-IfT {" ++ showDerivation↓ p ++ showDerivationChangesTo d ++ "};"
showJudgeChangesTo (C-IfF p d)
  = "C-IfF {" ++ showDerivation↓ p ++ showDerivationChangesTo d ++ "};"
showJudgeChangesTo (C-WhileT p d₁ d₂)
  = "C-WhileT {" ++ showDerivation↓ p ++ showDerivationChangesTo d₁ ++ showDerivationChangesTo d₂ ++ "};"
showJudgeChangesTo (C-WhileF p)
  = "C-WhileF {" ++ showDerivation↓ p ++ "};"

showDerivation⇓ {σ} {a₁} {i₁} p = showStore σ ++ " |- " ++ showAExp a₁ ++ " evalto " ++ showIValue i₁ ++ " by " ++ showJudge⇓ p

showDerivation↓ {σ} {b₁} {bv₁} p = showStore σ ++ " |- " ++ showBExp b₁ ++ " evalto " ++ showBValue bv₁ ++ " by " ++ showJudge↓ p

showDerivationChangesTo {c} {σ₁} {σ₂} p = showCom c ++ " changes " ++ showStore σ₁ ++ " to " ++ showStore σ₂ ++ " by " ++ showJudgeChangesTo p

