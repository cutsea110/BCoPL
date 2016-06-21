module BCoPL.TypeSafe.Properties where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (∃)
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

{- Theorem 8.3 -}
type-safety : ∀ {Γ ε e τ r} →
                Γ ⊢ e ∶ τ × ε ⊢ e ⇓ r × ⊫ ε ∶ Γ →
                ∃ λ v → r ≡ v × ⊨ v ∶ τ
type-safety (T-Int , E-Int , ⊫ε∶Γ) = (right (i _)) , (refl , INT (refl , ⊤.tt))
type-safety (T-Bool , E-Bool , ⊫ε∶Γ) = (right (b _)) , (refl , BOOL (refl , ⊤.tt))
type-safety (Γ⊢e∶τ , E-Var x₁ , ⊫ε∶Γ) = {!!}
type-safety (Γ⊢e∶τ , E-VarErr , ⊫ε∶Γ) = {!!}
type-safety (Γ⊢e∶τ , E-Plus ε⊢e⇓r ε⊢e⇓r₁ x , ⊫ε∶Γ) = {!!}
type-safety (Γ⊢e∶τ , E-PlusErr1 ε⊢e⇓r , ⊫ε∶Γ) = {!!}
type-safety (Γ⊢e∶τ , E-PlusErr2 ε⊢e⇓r ε⊢e⇓r₁ , ⊫ε∶Γ) = {!!}
type-safety (Γ⊢e∶τ , E-Minus ε⊢e⇓r ε⊢e⇓r₁ x , ⊫ε∶Γ) = {!!}
type-safety (Γ⊢e∶τ , E-MinusErr1 ε⊢e⇓r , ⊫ε∶Γ) = {!!}
type-safety (Γ⊢e∶τ , E-MinusErr2 ε⊢e⇓r ε⊢e⇓r₁ , ⊫ε∶Γ) = {!!}
type-safety (Γ⊢e∶τ , E-Times ε⊢e⇓r ε⊢e⇓r₁ x , ⊫ε∶Γ) = {!!}
type-safety (Γ⊢e∶τ , E-TimesErr1 ε⊢e⇓r , ⊫ε∶Γ) = {!!}
type-safety (Γ⊢e∶τ , E-TimesErr2 ε⊢e⇓r ε⊢e⇓r₁ , ⊫ε∶Γ) = {!!}
type-safety (Γ⊢e∶τ , E-Lt ε⊢e⇓r ε⊢e⇓r₁ x , ⊫ε∶Γ) = {!!}
type-safety (Γ⊢e∶τ , E-LtErr1 ε⊢e⇓r , ⊫ε∶Γ) = {!!}
type-safety (Γ⊢e∶τ , E-LtErr2 ε⊢e⇓r ε⊢e⇓r₁ , ⊫ε∶Γ) = {!!}
type-safety (Γ⊢e∶τ , E-IfT ε⊢e⇓r ε⊢e⇓r₁ , ⊫ε∶Γ) = {!!}
type-safety (Γ⊢e∶τ , E-IfF ε⊢e⇓r ε⊢e⇓r₁ , ⊫ε∶Γ) = {!!}
type-safety (Γ⊢e∶τ , E-IfErr1 ε⊢e⇓r , ⊫ε∶Γ) = {!!}
type-safety (Γ⊢e∶τ , E-IfErr2 ε⊢e⇓r ε⊢e⇓r₁ , ⊫ε∶Γ) = {!!}
type-safety (Γ⊢e∶τ , E-IfErr3 ε⊢e⇓r ε⊢e⇓r₁ , ⊫ε∶Γ) = {!!}
type-safety (Γ⊢e∶τ , E-Let ε⊢e⇓r ε⊢e⇓r₁ , ⊫ε∶Γ) = {!!}
type-safety (Γ⊢e∶τ , E-LetErr1 ε⊢e⇓r , ⊫ε∶Γ) = {!!}
type-safety (Γ⊢e∶τ , E-LetErr2 ε⊢e⇓r ε⊢e⇓r₁ , ⊫ε∶Γ) = {!!}
type-safety (Γ⊢e∶τ , E-LetRec ε⊢e⇓r , ⊫ε∶Γ) = {!!}
type-safety (Γ⊢e∶τ , E-LetRecErr ε⊢e⇓r , ⊫ε∶Γ) = {!!}
type-safety (Γ⊢e∶τ , E-Fun , ⊫ε∶Γ) = {!!}
type-safety (Γ⊢e∶τ , E-App ε⊢e⇓r ε⊢e⇓r₁ ε⊢e⇓r₂ , ⊫ε∶Γ) = {!!}
type-safety (Γ⊢e∶τ , E-AppErr1 ε⊢e⇓r , ⊫ε∶Γ) = {!!}
type-safety (Γ⊢e∶τ , E-AppErr2 ε⊢e⇓r ε⊢e⇓r₁ , ⊫ε∶Γ) = {!!}
type-safety (Γ⊢e∶τ , E-AppErr3 ε⊢e⇓r ε⊢e⇓r₁ , ⊫ε∶Γ) = {!!}
type-safety (Γ⊢e∶τ , E-AppErr4 ε⊢e⇓r ε⊢e⇓r₁ ε⊢e⇓r₂ , ⊫ε∶Γ) = {!!}
type-safety (Γ⊢e∶τ , E-AppErr5 ε⊢e⇓r ε⊢e⇓r₁ ε⊢e⇓r₂ , ⊫ε∶Γ) = {!!}
type-safety (Γ⊢e∶τ , E-AppRec ε⊢e⇓r ε⊢e⇓r₁ ε⊢e⇓r₂ , ⊫ε∶Γ) = {!!}
type-safety (Γ⊢e∶τ , E-Nil , ⊫ε∶Γ) = {!!}
type-safety (Γ⊢e∶τ , E-Cons ε⊢e⇓r ε⊢e⇓r₁ , ⊫ε∶Γ) = {!!}
type-safety (Γ⊢e∶τ , E-ConsErr1 ε⊢e⇓r , ⊫ε∶Γ) = {!!}
type-safety (Γ⊢e∶τ , E-ConsErr2 ε⊢e⇓r ε⊢e⇓r₁ , ⊫ε∶Γ) = {!!}
type-safety (Γ⊢e∶τ , E-MatchNil ε⊢e⇓r ε⊢e⇓r₁ , ⊫ε∶Γ) = {!!}
type-safety (Γ⊢e∶τ , E-MatchCons ε⊢e⇓r ε⊢e⇓r₁ , ⊫ε∶Γ) = {!!}
type-safety (Γ⊢e∶τ , E-MatchErr1 ε⊢e⇓r , ⊫ε∶Γ) = {!!}
type-safety (Γ⊢e∶τ , E-MatchErr2 ε⊢e⇓r ε⊢e⇓r₁ , ⊫ε∶Γ) = {!!}
type-safety (Γ⊢e∶τ , E-MatchErr3 ε⊢e⇓r ε⊢e⇓r₁ , ⊫ε∶Γ) = {!!}

{-
type-safety : ∀ {e τ r v τ₁ τ₂ τ′} →
              ● ⊢ e ∶ τ × ● ⊢ e ⇓ r →
              r ≡ v × (τ ≡ int → v isℤ) × (τ ≡ bool → v isBool) × (τ ≡ τ₁ ⇀ τ₂ → v isClosure) × (τ ≡ τ′ list → v isList)
type-safety (⊢e∶τ , ⊢e⇓r) = {!!}
-}
