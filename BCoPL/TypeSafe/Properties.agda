module BCoPL.TypeSafe.Properties where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤)
open import Relation.Binary.Core
open import Relation.Nullary using (yes; no; ¬_; Dec)
open import Relation.Nullary.Negation using (contraposition)
open import Relation.Binary.PropositionalEquality as PropEq

open import BCoPL.TypeSafe hiding (_≟_)

_≟_ : Decidable {A = Types} _≡_
type-error ≟ type-error = yes refl
type-error ≟ bool = no (λ ())
type-error ≟ int = no (λ ())
type-error ≟ (τ₂ ⇀ τ₃) = no (λ ())
type-error ≟ (τ₂ list) = no (λ ())
bool ≟ type-error = no (λ ())
bool ≟ bool = yes refl
bool ≟ int = no (λ ())
bool ≟ (τ₂ ⇀ τ₃) = no (λ ())
bool ≟ (τ₂ list) = no (λ ())
int ≟ type-error = no (λ ())
int ≟ bool = no (λ ())
int ≟ int = yes refl
int ≟ (τ₂ ⇀ τ₃) = no (λ ())
int ≟ (τ₂ list) = no (λ ())
(τ₁ ⇀ τ₂) ≟ type-error = no (λ ())
(τ₁ ⇀ τ₂) ≟ bool = no (λ ())
(τ₁ ⇀ τ₂) ≟ int = no (λ ())
(τ₁ ⇀ τ₂) ≟ (τ₃ ⇀ τ₄) with τ₁ ≟ τ₃ | τ₂ ≟ τ₄
(τ₁ ⇀ τ₂) ≟ (τ₃ ⇀ τ₄) | yes τ₁≡τ₃ | yes τ₂≡τ₄ = yes (cong₂ _⇀_ τ₁≡τ₃ τ₂≡τ₄)
(τ₁ ⇀ τ₂) ≟ (τ₃ ⇀ τ₄) | yes τ₁≡τ₃ | no τ₂≢τ₄ rewrite τ₁≡τ₃ = no (contraposition help₀ τ₂≢τ₄)
  where
    help₀ : ∀ {τ₃ τ₂ τ₄} → τ₃ ⇀ τ₂ ≡ τ₃ ⇀ τ₄ → τ₂ ≡ τ₄
    help₀ refl = refl
(τ₁ ⇀ τ₂) ≟ (τ₃ ⇀ τ₄) | no τ₁≢τ₃ | yes τ₂≡τ₄ rewrite τ₂≡τ₄ = no (contraposition help₁ τ₁≢τ₃)
  where
    help₁ : ∀ {τ₄ τ₁ τ₃} → τ₁ ⇀ τ₄ ≡ τ₃ ⇀ τ₄ → τ₁ ≡ τ₃
    help₁ refl = refl
(τ₁ ⇀ τ₂) ≟ (τ₃ ⇀ τ₄) | no τ₁≢τ₃ | no τ₂≢τ₄ = no (contraposition help₂ τ₁≢τ₃)
  where
    help₂ : ∀ {τ₁ τ₂ τ₃ τ₄} → τ₁ ⇀ τ₂ ≡ τ₃ ⇀ τ₄ → τ₁ ≡ τ₃
    help₂ refl = refl
(τ₁ ⇀ τ₂) ≟ (τ₃ list) = no (λ ())
(τ₁ list) ≟ type-error = no (λ ())
(τ₁ list) ≟ bool = no (λ ())
(τ₁ list) ≟ int = no (λ ())
(τ₁ list) ≟ (τ₂ ⇀ τ₃) = no (λ ())
(τ₁ list) ≟ (τ₂ list) with τ₁ ≟ τ₂
(τ₁ list) ≟ (τ₂ list) | yes p = yes (cong _list p)
(τ₁ list) ≟ (τ₂ list) | no ¬p = no (contraposition help₃ ¬p)
  where
    help₃ : ∀ {τ₁ τ₂} → τ₁ list ≡ τ₂ list → τ₁ ≡ τ₂
    help₃ refl = refl

type-safety : ∀ {e τ r v τ₁ τ₂ τ′} →
              ● ⊢ e ∶ τ × ● ⊢ e ⇓ r →
              r ≡ v × (τ ≡ int → v isℤ) × (τ ≡ bool → v isBool) × (τ ≡ τ₁ ⇀ τ₂ → v isClosure) × (τ ≡ τ′ list → v isList)
type-safety (⊢e∶τ , ⊢e⇓r) = {!!}
