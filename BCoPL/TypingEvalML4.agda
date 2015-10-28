module BCoPL.TypingEvalML4 where

open import Data.Nat hiding (_<_; _+_; _*_) renaming (suc to S; zero to Z)

open import BCoPL.EvalML4 public

-- Types
data Types : Set where
  type-error : Types
  bool : Types
  int : Types
  _⇀_ : Types → Types → Types
  _list : Types → Types

data TEnv : Set where
  ● : TEnv
  _⊱_ : TEnv → (Var × Types) → TEnv

_〖_〗 : TEnv → Var → Types
● 〖 x 〗 = type-error
Γ ⊱ (y , e) 〖 x 〗 = y == x ¿ e ∶ Γ 〖 x 〗

infixl 20 _⊱_

infix 10 _〖_〗
infix 7 _list
infixr 6 _⇀_
infix 5 _⊢_∶_

data _⊢_∶_ : TEnv → Exp → Types → Set where
  T-Int : ∀ {Γ n} → Γ ⊢ i n ∶ int
  T-Bool : ∀ {Γ v} → Γ ⊢ b v ∶ bool
  T-If : ∀ {Γ e₁ e₂ e₃ τ}
         → Γ ⊢ e₁ ∶ bool
         → Γ ⊢ e₂ ∶ τ
         → Γ ⊢ e₃ ∶ τ
         → Γ ⊢ if e₁ then e₂ else e₃ ∶ τ
  T-Plus : ∀ {Γ e₁ e₂}
           → Γ ⊢ e₁ ∶ int
           → Γ ⊢ e₂ ∶ int
           → Γ ⊢ e₁ ⊕ e₂ ∶ int
  T-Minus : ∀ {Γ e₁ e₂}
            → Γ ⊢ e₁ ∶ int
            → Γ ⊢ e₂ ∶ int
            → Γ ⊢ e₁ ⊝ e₂ ∶ int
  T-Times : ∀ {Γ e₁ e₂}
            → Γ ⊢ e₁ ∶ int
            → Γ ⊢ e₂ ∶ int
            → Γ ⊢ e₁ ⊛ e₂ ∶ int
  T-Lt : ∀ {Γ e₁ e₂}
         → Γ ⊢ e₁ ∶ int
         → Γ ⊢ e₂ ∶ int
         → Γ ⊢ e₁ ≺ e₂ ∶ bool
  T-Var : ∀ {Γ x τ}
          → Γ 〖 x 〗 ≡ τ
          → Γ ⊢ var x ∶ τ
  T-Let : ∀ {Γ e₁ e₂ τ₁ τ₂ x}
          → Γ ⊢ e₁ ∶ τ₁
          → Γ ⊱ (x , τ₁) ⊢ e₂ ∶ τ₂
          → Γ ⊢ ℓet x ≔ e₁ ιn e₂ ∶ τ₂
  T-Fun : ∀ {Γ x e τ₁ τ₂}
          → Γ ⊱ (x , τ₁) ⊢ e ∶ τ₂
          → Γ ⊢ fun x ⇒ e ∶ τ₁ ⇀ τ₂
  T-App : ∀ {Γ e₁ e₂ τ₁ τ₂}
          → Γ ⊢ e₁ ∶ τ₁ ⇀ τ₂
          → Γ ⊢ e₂ ∶ τ₁
          → Γ ⊢ app e₁ e₂ ∶ τ₂
  T-LetRec : ∀ {Γ x y e₁ e₂ τ₁ τ₂ τ}
             → Γ ⊱ (x , τ₁ ⇀ τ₂) ⊱ (y , τ₁) ⊢ e₁ ∶ τ₂
             → Γ ⊱ (x , τ₁ ⇀ τ₂) ⊢ e₂ ∶ τ
             → Γ ⊢ ℓetrec x ≔fun y ⇒ e₁ ιn e₂ ∶ τ
  T-Nil : ∀ {Γ τ} → Γ ⊢ [] ∶ τ list
  T-Cons : ∀ {Γ τ e₁ e₂}
           → Γ ⊢ e₁ ∶ τ
           → Γ ⊢ e₂ ∶ τ list
           → Γ ⊢ e₁ ∷ e₂ ∶ τ list
  T-Match : ∀ {Γ e₁ e₂ e₃ τ τ' x y}
            → Γ ⊢ e₁ ∶ τ' list
            → Γ ⊢ e₂ ∶ τ
            → Γ ⊱ (x , τ') ⊱ (y , τ' list) ⊢ e₃ ∶ τ
            → Γ ⊢ match e₁ with[]⇒ e₂ ∣ x ∷ y ⇒ e₃ ∶ τ
