module BCoPL.TypeSafe where

open import Data.Empty using (⊥)
open import Data.Unit using (⊤)
open import BCoPL.EvalML4Err public
open import BCoPL.TypingML4Err hiding (Value; Env) public


_isℤ : Value → Set
_isℤ (left x) = ⊥
_isℤ (right (i x)) = ⊤
_isℤ (right (b x)) = ⊥
_isℤ (right ⟨ x ⟩[fun x₁ ⇒ x₂ ]) = ⊥
_isℤ (right ⟨ x ⟩[rec x₁ ≔fun x₂ ⇒ x₃ ]) = ⊥
_isℤ (right []) = ⊥
_isℤ (right (y ∷ y₁)) = ⊥

_isBool : Value → Set
_isBool (left x) = ⊥
_isBool (right (i x)) = ⊥
_isBool (right (b x)) = ⊤
_isBool (right ⟨ x ⟩[fun x₁ ⇒ x₂ ]) = ⊥
_isBool (right ⟨ x ⟩[rec x₁ ≔fun x₂ ⇒ x₃ ]) = ⊥
_isBool (right []) = ⊥
_isBool (right (y ∷ y₁)) = ⊥

_isClosure : Value → Set
left x isClosure = ⊥
right (i x) isClosure = ⊥
right (b x) isClosure = ⊥
right ⟨ x ⟩[fun x₁ ⇒ x₂ ] isClosure = ⊤
right ⟨ x ⟩[rec x₁ ≔fun x₂ ⇒ x₃ ] isClosure = ⊤
right [] isClosure = ⊥
right (y ∷ y₁) isClosure = ⊥

_isList : Value → Set
left x isList = ⊥
right (i x) isList = ⊥
right (b x) isList = ⊥
right ⟨ x ⟩[fun x₁ ⇒ x₂ ] isList = ⊥
right ⟨ x ⟩[rec x₁ ≔fun x₂ ⇒ x₃ ] isList = ⊥
right [] isList = ⊤
right (y ∷ y₁) isList = ⊤

infix 6 ⊫_∶_ ⊨_∶_

data ⊨_∶_ : (v : Value) → (τ : Types) → Set

data ⊫_∶_ : Env → TEnv → Set where
  EMPTY : ∀ {ε Γ} → ε ≡ ● × Γ ≡ ● → ⊫ ε ∶ Γ
  NONEMPTY : ∀ {ε ε′ Γ Γ′ x v τ} → ε ≡ ε′ ⊱ (x , v) × Γ ≡ Γ′ ⊱ (x , τ) × ⊫ ε′ ∶ Γ′ × ⊨ v ∶ τ → ⊫ ε ∶ Γ

data ⊨_∶_ where
  INT : ∀ {τ v} → τ ≡ int × v isℤ → ⊨ v ∶ τ
  BOOL : ∀ {τ v} → τ ≡ bool × v isBool → ⊨ v ∶ τ
  CLOSURE : ∀ {τ v τ₁ τ₂ ε x e Γ} →
            τ ≡ (τ₁ ⇀ τ₂) × v ≡ right (⟨ ε ⟩[fun x ⇒ e ]) × ⊫ ε ∶ Γ → (Γ ⊱ (x , τ₁) ⊢ e ∶ τ₂) → ⊨ v ∶ τ
  RECCLOSURE : ∀ {τ v τ₁ τ₂ ε x y e Γ} →
               τ ≡ (τ₁ ⇀ τ₂) × v ≡ right (⟨ ε ⟩[rec x ≔fun y ⇒ e ]) × (⊫ ε ∶ Γ) × Γ ⊱ (x , τ₁ ⇀ τ₂) ⊱ (y , τ₁) ⊢ e ∶ τ₂ → ⊨ v ∶ τ
  NIL : ∀ {τ τ′ v} → τ ≡ τ′ list × v ≡ right [] → ⊨ v ∶ τ
  CONS : ∀ {τ v τ′ v₁ v₂} → τ ≡ τ′ list × v ≡ right (v₁ ∷ v₂) × ⊨ right v₁ ∶ τ′ × ⊨ right v₂ ∶ τ′ list → ⊨ v ∶ τ
