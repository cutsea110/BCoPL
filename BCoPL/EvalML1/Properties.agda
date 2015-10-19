module BCoPL.EvalML1.Properties where

open import Data.Product
open import Relation.Binary.PropositionalEquality as PropEq

open import BCoPL.EvalML1

-- theorem 3.2
uniqueness-plus : ∀ {i₁ i₂ v₁ v₂} → i₁ plus i₂ is v₁ × i₁ plus i₂ is v₂ → v₁ ≡ v₂
uniqueness-plus (B-Plus refl , B-Plus refl) = refl

uniqueness-minus : ∀ {i₁ i₂ v₁ v₂} → i₁ minus i₂ is v₁ × i₁ minus i₂ is v₂ → v₁ ≡ v₂
uniqueness-minus (B-Minus refl , B-Minus refl) = refl

uniqueness-times : ∀ {i₁ i₂ v₁ v₂} → i₁ times i₂ is v₁ × i₁ times i₂ is v₂ → v₁ ≡ v₂
uniqueness-times (B-Times refl , B-Times refl) = refl

uniqueness-less-than : ∀ {i₁ i₂ v₁ v₂} → i₁ less-than i₂ is v₁ × i₁ less-than i₂ is v₂ → v₁ ≡ v₂
uniqueness-less-than (B-Lt refl , B-Lt refl) = refl

uniqueness-⇓ : ∀ {e v₁ v₂} → e ⇓ v₁ × e ⇓ v₂ → v₁ ≡ v₂
uniqueness-⇓ (E-Int , E-Int) = refl
uniqueness-⇓ (E-Bool , E-Bool) = refl
uniqueness-⇓ (E-IfT p₁ e₁ , E-IfT p₂ e₂)
 rewrite uniqueness-⇓ (p₁ , p₂) | uniqueness-⇓ (e₁ , e₂) = refl
uniqueness-⇓ (E-IfT p₁ e₁ , E-IfF p₂ e₂) with uniqueness-⇓ (p₁ , p₂)
... | ()
uniqueness-⇓ (E-IfF p₁ e₁ , E-IfT p₂ e₂) with uniqueness-⇓ (p₁ , p₂)
... | ()
uniqueness-⇓ (E-IfF p₁ e₁ , E-IfF p₂ e₂)
 rewrite uniqueness-⇓ (p₁ , p₂) | uniqueness-⇓ (e₁ , e₂) = refl
uniqueness-⇓ (E-Plus e₁ e₂ p₁ , E-Plus e₃ e₄ p₂)
 rewrite uniqueness-⇓ (e₁ , e₃) | uniqueness-⇓ (e₂ , e₄) | uniqueness-plus (p₁ , p₂) = refl
uniqueness-⇓ (E-Minus e₁ e₂ m₁ , E-Minus e₃ e₄ m₂)
 rewrite uniqueness-⇓ (e₁ , e₃) | uniqueness-⇓ (e₂ , e₄) | uniqueness-minus (m₁ , m₂) = refl
uniqueness-⇓ (E-Times e₁ e₂ t₁ , E-Times e₃ e₄ t₂)
 rewrite uniqueness-⇓ (e₁ , e₃) | uniqueness-⇓ (e₂ , e₄) | uniqueness-times (t₁ , t₂) = refl
uniqueness-⇓ (E-Lt e₁ e₂ c₁ , E-Lt e₃ e₄ c₂)
 rewrite uniqueness-⇓ (e₁ , e₃) | uniqueness-⇓ (e₂ , e₄) | uniqueness-less-than (c₁ , c₂) = refl
