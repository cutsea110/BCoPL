module BCoPL.TypeSafe.Properties where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (∃)
open import Data.Unit using (⊤; tt)
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
type-safety (T-Int , E-Int , ⊫ε∶Γ) = (right (i _)) , (refl , INT (refl , tt))
type-safety (T-Bool , E-Bool , ⊫ε∶Γ) = (right (b _)) , (refl , BOOL (refl , tt))
type-safety (T-Var refl , E-Var refl , EMPTY (refl , refl)) = (left (error _)) , (refl , ERROR (left refl))
type-safety (T-Var {x = x} refl , E-Var {x = .x} refl , NONEMPTY {x = y} (refl , refl , proj₃ , proj₄)) = {!!}
type-safety (T-Var refl , E-VarErr , ⊫ε∶Γ) = (left (error _)) , (refl , (ERROR (right tt)))

type-safety (T-Plus Γ⊢e∶τ Γ⊢e∶τ₁ , E-Plus ε⊢e⇓r ε⊢e⇓r₁ (B-Plus refl) , ⊫ε∶Γ) = (right (i _)) , (refl , (INT (refl , tt)))
type-safety (T-Plus Γ⊢e∶τ Γ⊢e∶τ₁ , E-PlusErr1 ε⊢e⇓r {r≢ℤ = r≢ℤ} , ⊫ε∶Γ) = {!!}
type-safety (T-Plus Γ⊢e∶τ Γ⊢e∶τ₁ , E-PlusErr2 ε⊢e⇓r ε⊢e⇓r₁ {r≢ℤ = r≢ℤ} , ⊫ε∶Γ) = {!!}

type-safety (T-Minus Γ⊢e∶τ Γ⊢e∶τ₁ , E-Minus ε⊢e⇓r ε⊢e⇓r₁ (B-Minus refl) , ⊫ε∶Γ) = (right (i _)) , (refl , (INT (refl , tt)))
type-safety (T-Minus Γ⊢e∶τ Γ⊢e∶τ₁ , E-MinusErr1 ε⊢e⇓r , ⊫ε∶Γ) = {!!}
type-safety (T-Minus Γ⊢e∶τ Γ⊢e∶τ₁ , E-MinusErr2 ε⊢e⇓r ε⊢e⇓r₁ , ⊫ε∶Γ) = {!!}

type-safety (T-Times Γ⊢e∶τ Γ⊢e∶τ₁ , E-Times ε⊢e⇓r ε⊢e⇓r₁ (B-Times refl) , ⊫ε∶Γ) = (right (i _)) , (refl , INT (refl , tt))
type-safety (T-Times Γ⊢e∶τ Γ⊢e∶τ₁ , E-TimesErr1 ε⊢e⇓r , ⊫ε∶Γ) = {!!}
type-safety (T-Times Γ⊢e∶τ Γ⊢e∶τ₁ , E-TimesErr2 ε⊢e⇓r ε⊢e⇓r₁ , ⊫ε∶Γ) = {!!}

type-safety (T-Lt Γ⊢e∶τ Γ⊢e∶τ₁ , E-Lt ε⊢e⇓r ε⊢e⇓r₁ (B-Lt refl) , ⊫ε∶Γ) = (right (b _)) , (refl , (BOOL (refl , tt)))
type-safety (T-Lt Γ⊢e∶τ Γ⊢e∶τ₁ , E-LtErr1 ε⊢e⇓r , ⊫ε∶Γ) = {!!}
type-safety (T-Lt Γ⊢e∶τ Γ⊢e∶τ₁ , E-LtErr2 ε⊢e⇓r ε⊢e⇓r₁ , ⊫ε∶Γ) = {!!}

type-safety (T-If Γ⊢e∶τ Γ⊢e∶τ₁ Γ⊢e∶τ₂ , E-IfT ε⊢e⇓r ε⊢e⇓r₁ , ⊫ε∶Γ) with type-safety (Γ⊢e∶τ₁ , ε⊢e⇓r₁ , ⊫ε∶Γ)
... | r , refl , proj₃ = r , (refl , proj₃)
type-safety (T-If Γ⊢e∶τ Γ⊢e∶τ₁ Γ⊢e∶τ₂ , E-IfF ε⊢e⇓r ε⊢e⇓r₁ , ⊫ε∶Γ) with type-safety (Γ⊢e∶τ₂ , ε⊢e⇓r₁ , ⊫ε∶Γ)
... | r , refl , proj₃ = r , (refl , proj₃)
type-safety (Γ⊢e∶τ , E-IfErr1 ε⊢e⇓r , ⊫ε∶Γ) = {!!}
type-safety (Γ⊢e∶τ , E-IfErr2 ε⊢e⇓r ε⊢e⇓r₁ , ⊫ε∶Γ) = {!!}
type-safety (Γ⊢e∶τ , E-IfErr3 ε⊢e⇓r ε⊢e⇓r₁ , ⊫ε∶Γ) = {!!}

type-safety (T-Let Γ⊢e∶τ Γ⊢e∶τ₁ , E-Let ε⊢e⇓r ε⊢e⇓r₁ , ⊫ε∶Γ) with type-safety (Γ⊢e∶τ , ε⊢e⇓r , ⊫ε∶Γ)
... | v₁ , refl , proj₃ with type-safety (Γ⊢e∶τ₁ , ε⊢e⇓r₁ , NONEMPTY (refl , (refl , (⊫ε∶Γ , proj₃))))
... | r , refl , proj₄ = r , (refl , proj₄)
type-safety (Γ⊢e∶τ , E-LetErr1 ε⊢e⇓r , ⊫ε∶Γ) = {!!}
type-safety (Γ⊢e∶τ , E-LetErr2 ε⊢e⇓r ε⊢e⇓r₁ , ⊫ε∶Γ) = {!!}

type-safety (Γ⊢e∶τ , E-LetRec ε⊢e⇓r , ⊫ε∶Γ) = {!!}
type-safety (Γ⊢e∶τ , E-LetRecErr ε⊢e⇓r , ⊫ε∶Γ) = {!!}

type-safety (T-Fun Γ⊢e∶τ , E-Fun , ⊫ε∶Γ) = right ⟨ _ ⟩[fun _ ⇒ _ ] , (refl , CLOSURE (refl , (refl , ⊫ε∶Γ)) Γ⊢e∶τ)

type-safety (T-App Γ⊢e∶τ Γ⊢e∶τ₁ , E-App {v = v} ε⊢e⇓r ε⊢e⇓r₁ ε⊢e⇓r₂ , ⊫ε∶Γ) with type-safety (Γ⊢e∶τ , ε⊢e⇓r , ⊫ε∶Γ) | type-safety (Γ⊢e∶τ₁ , ε⊢e⇓r₁ , ⊫ε∶Γ)
type-safety (T-App Γ⊢e∶τ Γ⊢e∶τ₁ , E-App {v = v} ε⊢e⇓r ε⊢e⇓r₁ ε⊢e⇓r₂ , ⊫ε∶Γ) | _ , refl , proj₃ | v₂ , refl , proj₆ = v , (refl , {!!})
type-safety (Γ⊢e∶τ , E-AppErr1 ε⊢e⇓r , ⊫ε∶Γ) = {!!}
type-safety (Γ⊢e∶τ , E-AppErr2 ε⊢e⇓r ε⊢e⇓r₁ , ⊫ε∶Γ) = {!!}
type-safety (Γ⊢e∶τ , E-AppErr3 ε⊢e⇓r ε⊢e⇓r₁ , ⊫ε∶Γ) = {!!}
type-safety (Γ⊢e∶τ , E-AppErr4 ε⊢e⇓r ε⊢e⇓r₁ ε⊢e⇓r₂ , ⊫ε∶Γ) = {!!}
type-safety (Γ⊢e∶τ , E-AppErr5 ε⊢e⇓r ε⊢e⇓r₁ ε⊢e⇓r₂ , ⊫ε∶Γ) = {!!}

type-safety (Γ⊢e∶τ , E-AppRec ε⊢e⇓r ε⊢e⇓r₁ ε⊢e⇓r₂ , ⊫ε∶Γ) = {!!}

type-safety (T-Nil , E-Nil , ⊫ε∶Γ) = (right []) , (refl , (NIL (refl , refl)))
type-safety (T-Cons Γ⊢e∶τ Γ⊢e∶τ₁ , E-Cons ε⊢e⇓r ε⊢e⇓r₁ , ⊫ε∶Γ) with type-safety (Γ⊢e∶τ , ε⊢e⇓r , ⊫ε∶Γ) | type-safety (Γ⊢e∶τ₁ , ε⊢e⇓r₁ , ⊫ε∶Γ)
... | _ , refl , proj₃ | _ , refl , proj₆ = (right (_ ∷ _)) , (refl , CONS (refl , (refl , (proj₃ , proj₆))))
type-safety (Γ⊢e∶τ , E-ConsErr1 ε⊢e⇓r , ⊫ε∶Γ) = {!!}
type-safety (Γ⊢e∶τ , E-ConsErr2 ε⊢e⇓r ε⊢e⇓r₁ , ⊫ε∶Γ) = {!!}

type-safety (T-Match Γ⊢e∶τ Γ⊢e∶τ₁ Γ⊢e∶τ₂ , E-MatchNil ε⊢e⇓r ε⊢e⇓r₁ , ⊫ε∶Γ) = type-safety (Γ⊢e∶τ₁ , ε⊢e⇓r₁ , ⊫ε∶Γ)
type-safety (T-Match Γ⊢e∶τ Γ⊢e∶τ₁ Γ⊢e∶τ₂ , E-MatchCons ε⊢e⇓r ε⊢e⇓r₁ , ⊫ε∶Γ) with type-safety (Γ⊢e∶τ , ε⊢e⇓r , ⊫ε∶Γ)
... | _ , refl , proj₃ = type-safety (Γ⊢e∶τ₂ , ε⊢e⇓r₁ , NONEMPTY (refl , refl , (NONEMPTY (refl , (refl , (⊫ε∶Γ , help₀ proj₃))) , help₁ proj₃)))
  where
    help₀ : ∀ {v₁ v₂ τ'} →
        ⊨ right (v₁ ∷ v₂) ∶ τ' list → ⊨ right v₁ ∶ τ'
    help₀ (ERROR (left ()))
    help₀ (ERROR (right ()))
    help₀ (INT (() , proj₂))
    help₀ (BOOL (() , proj₂))
    help₀ (CLOSURE (() , proj₂) x₂)
    help₀ (RECCLOSURE (() , proj₂))
    help₀ (NIL (proj₁ , ()))
    help₀ (CONS (refl , refl , proj₁ , proj₂)) = proj₁

    help₁ : ∀ {v₁ v₂ τ'} →
        ⊨ right (v₁ ∷ v₂) ∶ τ' list → ⊨ right v₂ ∶ τ' list
    help₁ (ERROR (left ()))
    help₁ (ERROR (right ()))
    help₁ (INT (() , proj₂))
    help₁ (BOOL (() , proj₂))
    help₁ (CLOSURE (() , proj₂) x₂)
    help₁ (RECCLOSURE (() , proj₂))
    help₁ (NIL (proj₁ , ()))
    help₁ (CONS (refl , refl , proj₁ , proj₂)) = proj₂
type-safety (Γ⊢e∶τ , E-MatchErr1 ε⊢e⇓r , ⊫ε∶Γ) = {!!}
type-safety (Γ⊢e∶τ , E-MatchErr2 ε⊢e⇓r ε⊢e⇓r₁ , ⊫ε∶Γ) = {!!}
type-safety (Γ⊢e∶τ , E-MatchErr3 ε⊢e⇓r ε⊢e⇓r₁ , ⊫ε∶Γ) = {!!}

{-
type-safety : ∀ {e τ r v τ₁ τ₂ τ′} →
              ● ⊢ e ∶ τ × ● ⊢ e ⇓ r →
              r ≡ v × (τ ≡ int → v isℤ) × (τ ≡ bool → v isBool) × (τ ≡ τ₁ ⇀ τ₂ → v isClosure) × (τ ≡ τ′ list → v isList)
type-safety (⊢e∶τ , ⊢e⇓r) = {!!}
-}
