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
bool ≟ bool = yes refl
bool ≟ int = no (λ ())
bool ≟ (τ₂ ⇀ τ₃) = no (λ ())
bool ≟ (τ₂ list) = no (λ ())
int ≟ bool = no (λ ())
int ≟ int = yes refl
int ≟ (τ₂ ⇀ τ₃) = no (λ ())
int ≟ (τ₂ list) = no (λ ())
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
(τ₁ list) ≟ bool = no (λ ())
(τ₁ list) ≟ int = no (λ ())
(τ₁ list) ≟ (τ₂ ⇀ τ₃) = no (λ ())
(τ₁ list) ≟ (τ₂ list) with τ₁ ≟ τ₂
(τ₁ list) ≟ (τ₂ list) | yes p = yes (cong _list p)
(τ₁ list) ≟ (τ₂ list) | no ¬p = no (contraposition help₃ ¬p)
  where
    help₃ : ∀ {τ₁ τ₂} → τ₁ list ≡ τ₂ list → τ₁ ≡ τ₂
    help₃ refl = refl


help-car : ∀ {v₁ v₂ τ} →
           ⊨ right (v₁ ∷ v₂) ∶ right (τ list) → ⊨ right v₁ ∶ right τ
help-car (INT (() , proj₂))
help-car (BOOL (() , proj₂))
help-car (CLOSURE (() , proj₂) x₂)
help-car (RECCLOSURE (() , proj₂))
help-car (NIL (refl , ()))
help-car (CONS (refl , refl , proj₁ , proj₂)) = proj₁

help-cdr : ∀ {v₁ v₂ τ} →
           ⊨ right (v₁ ∷ v₂) ∶ right (τ list) → ⊨ right v₂ ∶ right (τ list)
help-cdr (INT (() , proj₂))
help-cdr (BOOL (() , proj₂))
help-cdr (CLOSURE (() , proj₂) x₂)
help-cdr (RECCLOSURE (() , proj₂))
help-cdr (NIL (refl , ()))
help-cdr (CONS (refl , refl , proj₁ , proj₂)) = proj₂

open import Data.String renaming (_≟_ to _=?=_)

trivial : ∀ {ε x x′ v} → x ∉ (ε ⊱ (x′ , v)) → x ∉ ε
trivial {x = x} {x′} prf with x =?= x′
... | yes p = ⊥-elim (prf tt)
... | no ¬p = prf

{- Theorem 8.3 -}
type-safety : ∀ {Γ ε e τ r} →
                Γ ⊢ e ∶ τ × ε ⊢ e ⇓ r × ⊫ ε ∶ Γ →
                ∃ λ v → r ≡ v × ⊨ v ∶ right τ
type-safety (T-Int , E-Int , ⊫ε∶Γ) = (right (i _)) , (refl , INT (refl , tt))
type-safety (T-Bool , E-Bool , ⊫ε∶Γ) = (right (b _)) , (refl , BOOL (refl , tt))
type-safety (T-Var () , E-Var proj₁ , EMPTY (refl , refl))
type-safety (T-Var {x = x} prf , E-Var {x = .x} proj₁ , NONEMPTY {x = y} (refl , refl , proj₃ , proj₄)) with y =?= x
type-safety (T-Var refl , E-Var {v = v} refl , NONEMPTY {v = right .v} (refl , refl , proj₃ , proj₄)) | yes refl = (right v) , (refl , proj₄)
type-safety (T-Var {x = x} prf , E-Var {x = .x} {v} proj₁ , NONEMPTY {x = y} (refl , refl , proj₃ , proj₄)) | no ¬p = (right v) , (refl , {!!})
type-safety (T-Var prf , E-VarErr {x∉ε = x∉ε} , ⊫ε∶Γ) = ⊥-elim {!!}

type-safety (T-Plus Γ⊢e∶τ Γ⊢e∶τ₁ , E-Plus ε⊢e⇓r ε⊢e⇓r₁ (B-Plus refl) , ⊫ε∶Γ) = (right (i _)) , (refl , (INT (refl , tt)))
type-safety (T-Plus Γ⊢e∶τ Γ⊢e∶τ₁ , E-PlusErr1 ε⊢e⇓r {r≢ℤ = r≢ℤ} , ⊫ε∶Γ) with type-safety (Γ⊢e∶τ , ε⊢e⇓r , ⊫ε∶Γ)
... | _ , refl , INT (refl , proj₂) = ⊥-elim (r≢ℤ proj₂)
... | _ , refl , BOOL (() , proj₂)
... | _ , refl , CLOSURE (() , proj₂) x₂
... | _ , refl , RECCLOSURE (() , proj₂)
... | _ , refl , NIL (() , proj₂)
... | _ , refl , CONS (() , proj₂)
type-safety (T-Plus Γ⊢e∶τ Γ⊢e∶τ₁ , E-PlusErr2 ε⊢e⇓r ε⊢e⇓r₁ {r≢ℤ = r≢ℤ} , ⊫ε∶Γ) with type-safety (Γ⊢e∶τ , ε⊢e⇓r , ⊫ε∶Γ) | type-safety (Γ⊢e∶τ₁ , ε⊢e⇓r₁ , ⊫ε∶Γ)
... | _ , refl , proj₃ | _ , refl , INT (refl , proj₂) = ⊥-elim (r≢ℤ proj₂)
... | _ , refl , proj₃ | _ , refl , BOOL (() , proj₂)
... | _ , refl , proj₃ | _ , refl , CLOSURE (() , proj₂) x₂
... | _ , refl , proj₃ | _ , refl , RECCLOSURE (() , proj₂)
... | _ , refl , proj₃ | _ , refl , NIL (() , proj₂)
... | _ , refl , proj₃ | _ , refl , CONS (() , proj₂)

type-safety (T-Minus Γ⊢e∶τ Γ⊢e∶τ₁ , E-Minus ε⊢e⇓r ε⊢e⇓r₁ (B-Minus refl) , ⊫ε∶Γ) = (right (i _)) , (refl , (INT (refl , tt)))
type-safety (T-Minus Γ⊢e∶τ Γ⊢e∶τ₁ , E-MinusErr1 ε⊢e⇓r {r≢ℤ = r≢ℤ} , ⊫ε∶Γ) with type-safety (Γ⊢e∶τ , ε⊢e⇓r , ⊫ε∶Γ)
... | _ , refl , INT (refl , proj₂) = ⊥-elim (r≢ℤ proj₂)
... | _ , refl , BOOL (() , proj₂)
... | _ , refl , CLOSURE (() , proj₂) x₂
... | _ , refl , RECCLOSURE (() , proj₂)
... | _ , refl , NIL (() , proj₂)
... | _ , refl , CONS (() , proj₂)
type-safety (T-Minus Γ⊢e∶τ Γ⊢e∶τ₁ , E-MinusErr2 ε⊢e⇓r ε⊢e⇓r₁ {r≢ℤ = r≢ℤ} , ⊫ε∶Γ) with type-safety (Γ⊢e∶τ , ε⊢e⇓r , ⊫ε∶Γ) | type-safety (Γ⊢e∶τ₁ , ε⊢e⇓r₁ , ⊫ε∶Γ)
... | _ , refl , proj₃ | _ , refl , INT (refl , proj₂) = ⊥-elim (r≢ℤ proj₂)
... | _ , refl , proj₃ | _ , refl , BOOL (() , proj₂)
... | _ , refl , proj₃ | _ , refl , CLOSURE (() , proj₂) x₂
... | _ , refl , proj₃ | _ , refl , RECCLOSURE (() , proj₂)
... | _ , refl , proj₃ | _ , refl , NIL (() , proj₂)
... | _ , refl , proj₃ | _ , refl , CONS (() , proj₂)

type-safety (T-Times Γ⊢e∶τ Γ⊢e∶τ₁ , E-Times ε⊢e⇓r ε⊢e⇓r₁ (B-Times refl) , ⊫ε∶Γ) = (right (i _)) , (refl , INT (refl , tt))
type-safety (T-Times Γ⊢e∶τ Γ⊢e∶τ₁ , E-TimesErr1 ε⊢e⇓r {r≢ℤ = r≢ℤ} , ⊫ε∶Γ) with type-safety (Γ⊢e∶τ , ε⊢e⇓r , ⊫ε∶Γ)
... | _ , refl , INT (refl , proj₂) = ⊥-elim (r≢ℤ proj₂)
... | _ , refl , BOOL (() , proj₂)
... | _ , refl , CLOSURE (() , proj₂) x₂
... | _ , refl , RECCLOSURE (() , proj₂)
... | _ , refl , NIL (() , proj₂)
... | _ , refl , CONS (() , proj₂)
type-safety (T-Times Γ⊢e∶τ Γ⊢e∶τ₁ , E-TimesErr2 ε⊢e⇓r ε⊢e⇓r₁ {r≢ℤ = r≢ℤ} , ⊫ε∶Γ) with type-safety (Γ⊢e∶τ , ε⊢e⇓r , ⊫ε∶Γ) | type-safety (Γ⊢e∶τ₁ , ε⊢e⇓r₁ , ⊫ε∶Γ)
... | _ , refl , proj₃ | _ , refl , INT (refl , proj₂) = ⊥-elim (r≢ℤ proj₂)
... | _ , refl , proj₃ | _ , refl , BOOL (() , proj₂)
... | _ , refl , proj₃ | _ , refl , CLOSURE (() , proj₂) x₂
... | _ , refl , proj₃ | _ , refl , RECCLOSURE (() , proj₂)
... | _ , refl , proj₃ | _ , refl , NIL (() , proj₂)
... | _ , refl , proj₃ | _ , refl , CONS (() , proj₂)

type-safety (T-Lt Γ⊢e∶τ Γ⊢e∶τ₁ , E-Lt ε⊢e⇓r ε⊢e⇓r₁ (B-Lt refl) , ⊫ε∶Γ) = (right (b _)) , (refl , (BOOL (refl , tt)))
type-safety (T-Lt Γ⊢e∶τ Γ⊢e∶τ₁ , E-LtErr1 ε⊢e⇓r {r≢ℤ = r≢ℤ} , ⊫ε∶Γ) with type-safety (Γ⊢e∶τ , ε⊢e⇓r , ⊫ε∶Γ)
... | _ , refl , INT (refl , proj₂) = ⊥-elim (r≢ℤ proj₂)
... | _ , refl , BOOL (() , proj₂)
... | _ , refl , CLOSURE (() , proj₂) x₂
... | _ , refl , RECCLOSURE (() , proj₂)
... | _ , refl , NIL (() , proj₂)
... | _ , refl , CONS (() , proj₂)
type-safety (T-Lt Γ⊢e∶τ Γ⊢e∶τ₁ , E-LtErr2 ε⊢e⇓r ε⊢e⇓r₁ {r≢ℤ = r≢ℤ} , ⊫ε∶Γ) with type-safety (Γ⊢e∶τ , ε⊢e⇓r , ⊫ε∶Γ) | type-safety (Γ⊢e∶τ₁ , ε⊢e⇓r₁ , ⊫ε∶Γ)
... | _ , refl , proj₃ | _ , refl , INT (refl , proj₂) = ⊥-elim (r≢ℤ proj₂)
... | _ , refl , proj₃ | _ , refl , BOOL (() , proj₂)
... | _ , refl , proj₃ | _ , refl , CLOSURE (() , proj₂) x₂
... | _ , refl , proj₃ | _ , refl , RECCLOSURE (() , proj₂)
... | _ , refl , proj₃ | _ , refl , NIL (() , proj₂)
... | _ , refl , proj₃ | _ , refl , CONS (() , proj₂)

type-safety (T-If Γ⊢e∶τ Γ⊢e∶τ₁ Γ⊢e∶τ₂ , E-IfT {v = v} ε⊢e⇓r ε⊢e⇓r₁ , ⊫ε∶Γ) with type-safety (Γ⊢e∶τ₁ , ε⊢e⇓r₁ , ⊫ε∶Γ)
... | _ , refl , proj₃ = (right v) , (refl , proj₃)
type-safety (T-If Γ⊢e∶τ Γ⊢e∶τ₁ Γ⊢e∶τ₂ , E-IfF {v = v} ε⊢e⇓r ε⊢e⇓r₁ , ⊫ε∶Γ) with type-safety (Γ⊢e∶τ₂ , ε⊢e⇓r₁ , ⊫ε∶Γ)
... | _ , refl , proj₃ = right v , (refl , proj₃)
type-safety (T-If Γ⊢e∶τ Γ⊢e∶τ₁ Γ⊢e∶τ₂ , E-IfErr1 ε⊢e⇓r {r≢Bool = r≢Bool} , ⊫ε∶Γ) with type-safety (Γ⊢e∶τ , ε⊢e⇓r , ⊫ε∶Γ)
... | _ , refl , INT (() , proj₂)
... | _ , refl , BOOL (refl , proj₂) = ⊥-elim (r≢Bool proj₂)
... | _ , refl , CLOSURE (() , proj₂) x₂
... | _ , refl , RECCLOSURE (() , proj₂)
... | _ , refl , NIL (() , proj₂)
... | _ , refl , CONS (() , proj₂)
type-safety (T-If Γ⊢e∶τ Γ⊢e∶τ₁ Γ⊢e∶τ₂ , E-IfErr2 ε⊢e⇓r ε⊢e⇓r₁ , ⊫ε∶Γ) with type-safety (Γ⊢e∶τ , ε⊢e⇓r , ⊫ε∶Γ) | type-safety (Γ⊢e∶τ₁ , ε⊢e⇓r₁ , ⊫ε∶Γ)
... | .(right (b true)) , refl , proj₃ | .(left error) , refl , proj₆ = (left error) , (refl , proj₆)
type-safety (T-If Γ⊢e∶τ Γ⊢e∶τ₁ Γ⊢e∶τ₂ , E-IfErr3 ε⊢e⇓r ε⊢e⇓r₁ , ⊫ε∶Γ) with type-safety (Γ⊢e∶τ , ε⊢e⇓r , ⊫ε∶Γ) | type-safety (Γ⊢e∶τ₂ , ε⊢e⇓r₁ , ⊫ε∶Γ)
... | .(right (b false)) , refl , proj₃ | .(left error) , refl , proj₆ = (left error) , (refl , proj₆)

type-safety (T-Let Γ⊢e∶τ Γ⊢e∶τ₁ , E-Let {v = v} ε⊢e⇓r ε⊢e⇓r₁ , ⊫ε∶Γ) with type-safety (Γ⊢e∶τ , ε⊢e⇓r , ⊫ε∶Γ) | type-safety (Γ⊢e∶τ₁ , ε⊢e⇓r₁ , NONEMPTY (refl , refl , ⊫ε∶Γ , help (type-safety (Γ⊢e∶τ , ε⊢e⇓r , ⊫ε∶Γ))))
  where
    help : ∀ {τ₁ v₁} →
       Data.Product.Σ (Error ∨ Val)
       (λ v → Data.Product.Σ (right v₁ ≡ v) (λ x → ⊨ v ∶ right τ₁)) →
       ⊨ right v₁ ∶ right τ₁
    help (_ , refl , proj₃) = proj₃
... | _ , refl , proj₃ | _ , refl , proj₆ = (right v) , (refl , proj₆)
type-safety (T-Let Γ⊢e∶τ Γ⊢e∶τ₁ , E-LetErr1 ε⊢e⇓r , ⊫ε∶Γ) with type-safety (Γ⊢e∶τ , ε⊢e⇓r , ⊫ε∶Γ)
... | .(left error) , refl , INT (proj₁ , ())
... | .(left error) , refl , BOOL (proj₁ , ())
... | .(left error) , refl , CLOSURE (proj₁ , () , proj₃) x₂
... | .(left error) , refl , RECCLOSURE (proj₁ , () , proj₃)
... | .(left error) , refl , NIL (proj₁ , ())
... | .(left error) , refl , CONS (proj₁ , () , proj₃)
type-safety (T-Let Γ⊢e∶τ Γ⊢e∶τ₁ , E-LetErr2 ε⊢e⇓r ε⊢e⇓r₁ , ⊫ε∶Γ) with type-safety (Γ⊢e∶τ , ε⊢e⇓r , ⊫ε∶Γ) | type-safety (Γ⊢e∶τ₁ , ε⊢e⇓r₁ , NONEMPTY (refl , (refl , (⊫ε∶Γ , help (type-safety (Γ⊢e∶τ , ε⊢e⇓r , ⊫ε∶Γ))))))
  where
    help : ∀ {τ₁ v₁} →
       Data.Product.Σ (Error ∨ Val)
       (λ v → Data.Product.Σ (v₁ ≡ v) (λ x → ⊨ v ∶ τ₁)) →
       ⊨ v₁ ∶ τ₁
    help (v₁ , refl , proj₃) = proj₃
... | v₁ , proj₂ , proj₃ | .(left error) , refl , proj₆ = (left error) , (refl , proj₆)

type-safety (T-LetRec Γ⊢e∶τ Γ⊢e∶τ₁ , E-LetRec {v = v} ε⊢e⇓r , ⊫ε∶Γ) with type-safety (Γ⊢e∶τ₁ , ε⊢e⇓r , NONEMPTY (refl , refl , ⊫ε∶Γ , RECCLOSURE (refl , refl , ⊫ε∶Γ , Γ⊢e∶τ)))
... | _ , refl , proj₃ = (right v) , (refl , proj₃)
type-safety (T-LetRec Γ⊢e∶τ Γ⊢e∶τ₁ , E-LetRecErr ε⊢e⇓r , ⊫ε∶Γ) with type-safety (Γ⊢e∶τ₁ , ε⊢e⇓r , NONEMPTY (refl , refl , ⊫ε∶Γ , (RECCLOSURE (refl , refl , ⊫ε∶Γ , Γ⊢e∶τ))))
type-safety (T-LetRec Γ⊢e∶τ Γ⊢e∶τ₁ , E-LetRecErr ε⊢e⇓r , ⊫ε∶Γ) | .(left error) , refl , proj₃ = (left error) , (refl , proj₃)

type-safety (T-Fun Γ⊢e∶τ , E-Fun , ⊫ε∶Γ) = right ⟨ _ ⟩[fun _ ⇒ _ ] , (refl , CLOSURE (refl , (refl , ⊫ε∶Γ)) Γ⊢e∶τ)

type-safety (T-App Γ⊢e∶τ Γ⊢e∶τ₁ , E-App {v = v} ε⊢e⇓r ε⊢e⇓r₁ ε⊢e⇓r₂ , ⊫ε∶Γ) with type-safety (Γ⊢e∶τ , ε⊢e⇓r , ⊫ε∶Γ) | type-safety (Γ⊢e∶τ₁ , ε⊢e⇓r₁ , ⊫ε∶Γ)
... | _ , refl , INT (proj₁ , ()) | _ , refl , proj₆
... | _ , refl , BOOL (proj₁ , ()) | _ , refl , proj₆
... | _ , refl , CLOSURE (refl , refl , proj₃) x₃ | _ , refl , proj₆ = (right v) , (refl , {!!})
... | _ , refl , RECCLOSURE (proj₁ , () , proj₃) | _ , refl , proj₆
... | _ , refl , NIL (() , proj₂) | _ , refl , proj₆
... | _ , refl , CONS (() , proj₂) | _ , refl , proj₆

type-safety (T-App Γ⊢e∶τ Γ⊢e∶τ₁ , E-AppErr1 ε⊢e⇓r {r≢Closure = r≢Closure} , ⊫ε∶Γ) with type-safety (Γ⊢e∶τ , ε⊢e⇓r , ⊫ε∶Γ)
... | _ , refl , INT (() , proj₂)
... | _ , refl , BOOL (() , proj₂)
... | _ , refl , CLOSURE (refl , refl , proj₂) x₂ = ⊥-elim (r≢Closure tt)
... | _ , refl , RECCLOSURE (refl , refl , proj₂ , proj₃) = ⊥-elim (r≢Closure tt)
... | _ , refl , NIL (() , proj₂)
... | _ , refl , CONS (() , proj₂)
type-safety (T-App Γ⊢e∶τ Γ⊢e∶τ₁ , E-AppErr2 ε⊢e⇓r ε⊢e⇓r₁ , ⊫ε∶Γ) with type-safety (Γ⊢e∶τ , ε⊢e⇓r , ⊫ε∶Γ) | type-safety (Γ⊢e∶τ₁ , ε⊢e⇓r₁ , ⊫ε∶Γ)
... | _ , refl , proj₃ | .(left error) , refl , INT (proj₁ , ())
... | _ , refl , proj₃ | .(left error) , refl , BOOL (proj₁ , ())
... | _ , refl , proj₃ | .(left error) , refl , CLOSURE (proj₁ , () , proj₄) x₃
... | _ , refl , proj₃ | .(left error) , refl , RECCLOSURE (proj₁ , () , proj₄)
... | _ , refl , proj₃ | .(left error) , refl , NIL (proj₁ , ())
... | _ , refl , proj₃ | .(left error) , refl , CONS (proj₁ , () , proj₄)
type-safety (T-App Γ⊢e∶τ Γ⊢e∶τ₁ , E-AppErr3 ε⊢e⇓r ε⊢e⇓r₁ , ⊫ε∶Γ) with type-safety (Γ⊢e∶τ , ε⊢e⇓r , ⊫ε∶Γ) | type-safety (Γ⊢e∶τ₁ , ε⊢e⇓r₁ , ⊫ε∶Γ)
... | _ , refl , proj₃ | .(left error) , refl , INT (proj₁ , ())
... | _ , refl , proj₃ | .(left error) , refl , BOOL (proj₁ , ())
... | _ , refl , proj₃ | .(left error) , refl , CLOSURE (proj₁ , () , proj₄) x₃
... | _ , refl , proj₃ | .(left error) , refl , RECCLOSURE (proj₁ , () , proj₄)
... | _ , refl , proj₃ | .(left error) , refl , NIL (proj₁ , ())
... | _ , refl , proj₃ | .(left error) , refl , CONS (proj₁ , () , proj₄)
type-safety (T-App Γ⊢e∶τ Γ⊢e∶τ₁ , E-AppErr4 ε⊢e⇓r ε⊢e⇓r₁ ε⊢e⇓r₂ , ⊫ε∶Γ) with type-safety (Γ⊢e∶τ , ε⊢e⇓r , ⊫ε∶Γ) | type-safety (Γ⊢e∶τ₁ , ε⊢e⇓r₁ , ⊫ε∶Γ)
... | _ , refl , INT (proj₁ , ()) | _ , refl , proj₆
... | _ , refl , BOOL (proj₁ , ()) | _ , refl , proj₆
... | _ , refl , CLOSURE (refl , refl , proj₃) x₃ | _ , refl , proj₆ = (left error) , (refl , {!!})
... | _ , refl , RECCLOSURE (proj₁ , () , proj₃) | _ , refl , proj₆
... | _ , refl , NIL (() , proj₂) | _ , refl , proj₆
... | _ , refl , CONS (() , proj₂) | _ , refl , proj₆
type-safety (T-App Γ⊢e∶τ Γ⊢e∶τ₁ , E-AppErr5 ε⊢e⇓r ε⊢e⇓r₁ ε⊢e⇓r₂ , ⊫ε∶Γ) with type-safety (Γ⊢e∶τ , ε⊢e⇓r , ⊫ε∶Γ) | type-safety (Γ⊢e∶τ₁ , ε⊢e⇓r₁ , ⊫ε∶Γ)
... | _ , refl , INT (proj₁ , ()) | _ , refl , proj₆
... | _ , refl , BOOL (proj₁ , ()) | _ , refl , proj₆
... | _ , refl , CLOSURE (proj₁ , () , proj₃) x₃ | _ , refl , proj₆
... | _ , refl , RECCLOSURE (refl , refl , proj₃ , proj₄) | _ , refl , proj₆ = (left error) , (refl , {!!})
... | _ , refl , NIL (() , proj₂) | _ , refl , proj₆
... | _ , refl , CONS (() , proj₂) | _ , refl , proj₆

type-safety (T-App Γ⊢e∶τ Γ⊢e∶τ₁ , E-AppRec {v = v} ε⊢e⇓r ε⊢e⇓r₁ ε⊢e⇓r₂ , ⊫ε∶Γ) with type-safety (Γ⊢e∶τ , ε⊢e⇓r , ⊫ε∶Γ) | type-safety (Γ⊢e∶τ₁ , ε⊢e⇓r₁ , ⊫ε∶Γ)
... | _ , refl , INT (proj₁ , ()) | _ , refl , proj₆
... | _ , refl , BOOL (proj₁ , ()) | _ , refl , proj₆
... | _ , refl , CLOSURE (refl , () , proj₂) x₃ | _ , refl , proj₆
... | _ , refl , RECCLOSURE (refl , refl , proj₁ , proj₂) | _ , refl , proj₆ = {!!}
... | _ , refl , NIL (proj₁ , ()) | _ , refl , proj₆
... | _ , refl , CONS (() , proj₂) | _ , refl , proj₆

type-safety (T-Nil , E-Nil , ⊫ε∶Γ) = (right []) , (refl , (NIL (refl , refl)))
type-safety (T-Cons Γ⊢e∶τ Γ⊢e∶τ₁ , E-Cons ε⊢e⇓r ε⊢e⇓r₁ , ⊫ε∶Γ) with type-safety (Γ⊢e∶τ , ε⊢e⇓r , ⊫ε∶Γ) | type-safety (Γ⊢e∶τ₁ , ε⊢e⇓r₁ , ⊫ε∶Γ)
... | _ , refl , proj₃ | _ , refl , proj₆ = (right (_ ∷ _)) , (refl , CONS (refl , refl , proj₃ , proj₆))
type-safety (T-Cons Γ⊢e∶τ Γ⊢e∶τ₁ , E-ConsErr1 ε⊢e⇓r , ⊫ε∶Γ) with type-safety (Γ⊢e∶τ , ε⊢e⇓r , ⊫ε∶Γ)
... | .(left error) , refl , INT (proj₁ , ())
... | .(left error) , refl , BOOL (proj₁ , ())
... | .(left error) , refl , CLOSURE (proj₁ , () , proj₂) x₂
... | .(left error) , refl , RECCLOSURE (proj₁ , () , proj₂ , proj₃)
... | .(left error) , refl , NIL (proj₁ , ())
... | .(left error) , refl , CONS (refl , () , proj₂)
type-safety (T-Cons Γ⊢e∶τ Γ⊢e∶τ₁ , E-ConsErr2 ε⊢e⇓r ε⊢e⇓r₁ , ⊫ε∶Γ) with type-safety (Γ⊢e∶τ , ε⊢e⇓r , ⊫ε∶Γ) | type-safety (Γ⊢e∶τ₁ , ε⊢e⇓r₁ , ⊫ε∶Γ)
... | _ , refl , proj₃ | .(left error) , refl , INT (proj₁ , ())
... | _ , refl , proj₃ | .(left error) , refl , BOOL (proj₁ , ())
... | _ , refl , proj₃ | .(left error) , refl , CLOSURE (() , proj₂) x₂
... | _ , refl , proj₃ | .(left error) , refl , RECCLOSURE (() , proj₂)
... | _ , refl , proj₃ | .(left error) , refl , NIL (proj₁ , ())
... | _ , refl , proj₃ | .(left error) , refl , CONS (proj₁ , () , proj₄)

type-safety (T-Match Γ⊢e∶τ Γ⊢e∶τ₁ Γ⊢e∶τ₂ , E-MatchNil ε⊢e⇓r ε⊢e⇓r₁ , ⊫ε∶Γ) = type-safety (Γ⊢e∶τ₁ , ε⊢e⇓r₁ , ⊫ε∶Γ)
type-safety (T-Match Γ⊢e∶τ Γ⊢e∶τ₁ Γ⊢e∶τ₂ , E-MatchCons ε⊢e⇓r ε⊢e⇓r₁ , ⊫ε∶Γ) with type-safety (Γ⊢e∶τ , ε⊢e⇓r , ⊫ε∶Γ)
... | _ , refl , proj₃ = type-safety (Γ⊢e∶τ₂ , ε⊢e⇓r₁ , NONEMPTY (refl , refl , (NONEMPTY (refl , (refl , (⊫ε∶Γ , help-car proj₃))) , help-cdr proj₃)))
type-safety (T-Match Γ⊢e∶τ Γ⊢e∶τ₁ Γ⊢e∶τ₂ , E-MatchErr1 ε⊢e⇓r {r≢List = r≢List} , ⊫ε∶Γ) with type-safety (Γ⊢e∶τ , ε⊢e⇓r , ⊫ε∶Γ)
... | _ , refl , INT (() , proj₂)
... | _ , refl , BOOL (() , proj₂)
... | _ , refl , CLOSURE (() , proj₂) x₂
... | _ , refl , RECCLOSURE (() , proj₂)
... | .(right []) , refl , NIL (refl , refl) = ⊥-elim (r≢List tt)
... | _ , refl , CONS (refl , refl , proj₁ , proj₂) = ⊥-elim (r≢List tt)
type-safety (T-Match Γ⊢e∶τ Γ⊢e∶τ₁ Γ⊢e∶τ₂ , E-MatchErr2 ε⊢e⇓r ε⊢e⇓r₁ , ⊫ε∶Γ) with type-safety (Γ⊢e∶τ , ε⊢e⇓r , ⊫ε∶Γ) | type-safety (Γ⊢e∶τ₁ , ε⊢e⇓r₁ , ⊫ε∶Γ)
... | .(right []) , refl , proj₃ | .(left error) , refl , proj₆ = (left error) , (refl , proj₆)
type-safety (T-Match Γ⊢e∶τ Γ⊢e∶τ₁ Γ⊢e∶τ₂ , E-MatchErr3 ε⊢e⇓r ε⊢e⇓r₁ , ⊫ε∶Γ) with type-safety (Γ⊢e∶τ , ε⊢e⇓r , ⊫ε∶Γ)
type-safety (T-Match Γ⊢e∶τ Γ⊢e∶τ₁ Γ⊢e∶τ₂ , E-MatchErr3 ε⊢e⇓r ε⊢e⇓r₁ , ⊫ε∶Γ) | _ , refl , proj₃ = type-safety (Γ⊢e∶τ₂ , ε⊢e⇓r₁ , NONEMPTY (refl , (refl , ((NONEMPTY (refl , (refl , (⊫ε∶Γ , help-car proj₃)))) , help-cdr proj₃))))


{-
type-safety : ∀ {e τ r v τ₁ τ₂ τ′} →
              ● ⊢ e ∶ τ × ● ⊢ e ⇓ r →
              r ≡ v × (τ ≡ int → v isℤ) × (τ ≡ bool → v isBool) × (τ ≡ τ₁ ⇀ τ₂ → v isClosure) × (τ ≡ τ′ list → v isList)
type-safety (⊢e∶τ , ⊢e⇓r) = {!!}
-}
