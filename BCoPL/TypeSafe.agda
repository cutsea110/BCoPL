module BCoPL.TypeSafe where

open import Data.Empty using (⊥)
open import Data.Unit using (⊤)
open import BCoPL.EvalML4Err renaming (isℤ to isℤ'; isBool to isBool'; isClosure to isClosure'; isList to isList') public
open import BCoPL.TypingML4Err hiding (Value; Env; isℤ; isBool; isClosure; isList) public

isℤ : Value → Set
isℤ (left x) = ⊥
isℤ (right v) = isℤ' v

isBool : Value → Set
isBool (left x) = ⊥
isBool (right v) = isBool' v

isClosure : Value → Set
isClosure (left x) = ⊥
isClosure (right v) = isClosure' v

isList : Value → Set
isList (left x) = ⊥
isList (right v) = isList' v

isError : Value → Set
isError (left x) = ⊤
isError (right y) = ⊥

infix 6 ⊫_∶_ ⊨_∶_

data ⊨_∶_ : (v : Value) → (τ : Type-Error ∨ Types) → Set

data ⊫_∶_ : Env → TEnv → Set where
  EMPTY : ∀ {ε Γ} → ε ≡ ● × Γ ≡ ● → ⊫ ε ∶ Γ
  NONEMPTY : ∀ {ε ε′ Γ Γ′ x v τ} → ε ≡ ε′ ⊱ (x , v) × Γ ≡ Γ′ ⊱ (x , τ) × ⊫ ε′ ∶ Γ′ × ⊨ v ∶ right τ → ⊫ ε ∶ Γ

data ⊨_∶_ where
  INT : ∀ {τ v} → τ ≡ int × isℤ v → ⊨ v ∶ right τ
  BOOL : ∀ {τ v} → τ ≡ bool × isBool v → ⊨ v ∶ right τ
  CLOSURE : ∀ {τ v τ₁ τ₂ ε x e Γ} →
            τ ≡ (τ₁ ⇀ τ₂) × v ≡ right (⟨ ε ⟩[fun x ⇒ e ]) × ⊫ ε ∶ Γ → (Γ ⊱ (x , τ₁) ⊢ e ∶ τ₂) → ⊨ v ∶ right τ
  RECCLOSURE : ∀ {τ v τ₁ τ₂ ε x y e Γ} →
               τ ≡ (τ₁ ⇀ τ₂) × v ≡ right (⟨ ε ⟩[rec x ≔fun y ⇒ e ]) × (⊫ ε ∶ Γ) × Γ ⊱ (x , τ₁ ⇀ τ₂) ⊱ (y , τ₁) ⊢ e ∶ τ₂ → ⊨ v ∶ right τ
  NIL : ∀ {τ τ′ v} → τ ≡ τ′ list × v ≡ right [] → ⊨ v ∶ right τ
  CONS : ∀ {τ v τ′ v₁ v₂} → τ ≡ τ′ list × v ≡ right (v₁ ∷ v₂) × ⊨ right v₁ ∶ right τ′ × ⊨ right v₂ ∶ right (τ′ list) → ⊨ v ∶ right τ
