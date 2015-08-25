module BCoPL.Nat.Properties where

open import Function
open import Data.Product using (∃; _,_; _×_)
open import Relation.Binary.PropositionalEquality as PropEq

open import BCoPL.Nat
open import BCoPL.Show.Nat
open import BCoPL.Induction

-- theorem 2.1 (1)
left-identity-plus : (n : ℕ) → Z plus n is n
left-identity-plus = inductionℕ (P-Zero , (λ n x → P-Zero))

-- theorem 2.1 (2)
right-identity-plus : (n : ℕ) → n plus Z is n
right-identity-plus = inductionℕ (P-Zero , (λ n → P-Succ))

-- theorem 2.2
uniqueness-plus : ∀ {n₂ n₃ n₄} (n₁ : ℕ) → (n₁ plus n₂ is n₃) × (n₁ plus n₂ is n₄) → n₃ ≡ n₄
uniqueness-plus = inductionℕ (base , step)
  where
    base : ∀ {n₂ n₃ n₄} → (Z plus n₂ is n₃) × (Z plus n₂ is n₄) → n₃ ≡ n₄
    base (P-Zero , P-Zero) = refl
    step : ∀ {n₂ n₃ n₄} → (n : ℕ) →
         ((n plus n₂ is n₃) × (n plus n₂ is n₄) → n₃ ≡ n₄) →
         (S n plus n₂ is n₃) × (S n plus n₂ is n₄) → n₃ ≡ n₄
    step n₁ prf (P-Succ p₁ , P-Succ p₂) = {!!}
