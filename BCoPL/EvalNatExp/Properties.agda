module BCoPL.EvalNatExp.Properties where

open import Data.Product
open import Relation.Binary.PropositionalEquality as PropEq

open import BCoPL.Nat.Properties

-- theorem 2.15
open import BCoPL.EvalNatExp

eval-plus : ∀ n₁ n₂ → n₁ plus n₂ is (n₁ + n₂)
eval-plus Z n₂ = P-Zero
eval-plus (S n₁) n₂ = P-Succ (eval-plus n₁ n₂)

eval-times : ∀ n₁ n₂ → n₁ times n₂ is (n₁ * n₂)
eval-times Z n₂ = T-Zero
eval-times (S n₁) n₂ = T-Succ (eval-times n₁ n₂) (eval-plus n₂ (n₁ * n₂))

totality-⇓ : (e : Exp) → ∃ λ n → e ⇓ n
totality-⇓ (Nat n) = n , E-Const
totality-⇓ (e₁ ⊕ e₂) with totality-⇓ e₁ | totality-⇓ e₂
totality-⇓ (e₁ ⊕ e₂) | v₁ , prf₁ | v₂ , prf₂ = v₁ + v₂ , E-Plus prf₁ prf₂ (eval-plus v₁ v₂)
totality-⇓ (e₁ ⊛ e₂) with totality-⇓ e₁ | totality-⇓ e₂
totality-⇓ (e₁ ⊛ e₂) | v₁ , prf₁ | v₂ , prf₂ = (v₁ * v₂) , E-Times prf₁ prf₂ (eval-times v₁ v₂)

-- theorem 2.16
uniqueness-⇓ : ∀ {n₁ n₂ e} → e ⇓ n₁ × e ⇓ n₂ → n₁ ≡ n₂
uniqueness-⇓ (E-Const , E-Const) = refl
uniqueness-⇓ (E-Plus s₁ s₂ p₁ , E-Plus s₃ s₄ p₂)
  rewrite uniqueness-⇓ (s₁ , s₃) | uniqueness-⇓ (s₂ , s₄) | uniqueness-plus (p₁ , p₂) = refl
uniqueness-⇓ (E-Times s₁ s₂ t₁ , E-Times s₃ s₄ t₂)
  rewrite uniqueness-⇓ (s₁ , s₃) | uniqueness-⇓ (s₂ , s₄) | uniqueness-times (t₁ , t₂) = refl

-- theorem 2.17
commutativity-⊕ : ∀ {e₁ e₂ n} → e₁ ⊕ e₂ ⇓ n → e₂ ⊕ e₁ ⇓ n
commutativity-⊕ (E-Plus s₁ s₂ p) with commutativity-plus p
... | prf = E-Plus s₂ s₁ prf

-- theorem 2.18
associativity-⊕ : ∀ {e₁ e₂ e₃ n} → (e₁ ⊕ e₂) ⊕ e₃ ⇓ n → e₁ ⊕ (e₂ ⊕ e₃) ⇓ n
associativity-⊕ (E-Plus (E-Plus s₁ s₂ p₁) s₃ p₂) with associativity-plus (p₁ , p₂)
associativity-⊕ (E-Plus (E-Plus s₁ s₂ p₁) s₃ p₂) | proj₁ , proj₂ , proj₃
  = E-Plus s₁ (E-Plus s₂ s₃ proj₂) proj₃

-- theorem 2.19
commutativity-⊛ : ∀ {e₁ e₂ n} → e₁ ⊛ e₂ ⇓ n → e₂ ⊛ e₁ ⇓ n
commutativity-⊛ (E-Times s₁ s₂ t) with commutativity-times t
... | prf = E-Times s₂ s₁ prf

-- theorem 2.20
associativity-⊛ : ∀ {e₁ e₂ e₃ n} → (e₁ ⊛ e₂) ⊛ e₃ ⇓ n → e₁ ⊛ (e₂ ⊛ e₃) ⇓ n
associativity-⊛ (E-Times (E-Times s₁ s₂ t₁) s₃ t₂) with associativity-times (t₁ , t₂)
associativity-⊛ (E-Times (E-Times s₁ s₂ t₁) s₃ t₂) | proj₁ , proj₂ , proj₃
  = E-Times s₁ (E-Times s₂ s₃ proj₂) proj₃

