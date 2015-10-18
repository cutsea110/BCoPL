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
showDerivationPlus = {!!}
showDerivationMinus : ∀ {i₁ i₂ i₃} → i₁ minus i₂ is i₃ → String
showDerivationMinus = {!!}
showDerivationTimes : ∀ {i₁ i₂ i₃} → i₁ times i₂ is i₃ → String
showDerivationTimes = {!!}
showDerivationLessThan : ∀ {i₁ i₂ b} → i₁ less-than i₂ is b → String
showDerivationLessThan = {!!}

showJudge⇓ : ∀ {e v} → e ⇓ v → String
showJudge⇓ E-Int = "E-Int {};"
showJudge⇓ E-Bool = "E-Bool {};"
showJudge⇓ (E-IfT e₁ e₂) = "E-IfT {" ++ showJudge⇓ e₁ ++ showJudge⇓ e₂ ++ "};"
showJudge⇓ (E-IfF e₁ e₂) = "E-IfF {" ++ showJudge⇓ e₁ ++ showJudge⇓ e₂ ++ "};"
showJudge⇓ (E-Plus e₁ e₂ p) = "E-Plus {" ++ showJudge⇓ e₁ ++ showJudge⇓ e₂ ++ showDerivationPlus p ++ "};"
showJudge⇓ (E-Minus e₁ e₂ p) = "E-Minus {" ++ showJudge⇓ e₁ ++ showJudge⇓ e₂ ++ showDerivationMinus p ++ "};"
showJudge⇓ (E-Times e₁ e₂ p) = "E-Times {" ++ showJudge⇓ e₁ ++ showJudge⇓ e₂ ++ showDerivationTimes p ++ "};"
showJudge⇓ (E-Lt e₁ e₂ p) = "E-Lt {" ++ showJudge⇓ e₁ ++ showJudge⇓ e₂ ++ showDerivationLessThan p ++ "};"

showDerivation⇓ {e} {v} p = showExp e ++ " evalto " ++ showValue v ++ " by " ++ showJudge⇓ p
