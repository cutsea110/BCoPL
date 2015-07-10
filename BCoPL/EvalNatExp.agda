module BCoPL.EvalNatExp where

open import BCoPL.Nat public

data Exp : Set where
  Nat : ℕ → Exp
  _⊕_ : Exp → Exp → Exp
  _⊛_ : Exp → Exp → Exp

infixl 5 _⊛_
infixl 4 _⊕_

infix 3 _⇓_
data _⇓_ : Exp → ℕ → Set where
  E-Const : ∀ {n} → Nat n ⇓ n
  E-Plus : ∀ {e₁ n₁ e₂ n₂ n} → e₁ ⇓ n₁ → e₂ ⇓ n₂ → n₁ plus n₂ is n → e₁ ⊕ e₂ ⇓ n
  E-Times : ∀ {e₁ n₁ e₂ n₂ n} → e₁ ⇓ n₁ → e₂ ⇓ n₂ → n₁ times n₂ is n → e₁ ⊛ e₂ ⇓ n

