module BCoPL.EvalML1.Properties where

open import Data.Product
open import Relation.Binary.PropositionalEquality as PropEq

open import BCoPL.EvalML1
open import BCoPL.Induction

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

uniqueness-⇓-by-induction : (e : Exp) → ∀ {v₁ v₂} → e ⇓ v₁ × e ⇓ v₂ → v₁ ≡ v₂
uniqueness-⇓-by-induction = induction-EvalML1 help-int help-bool help-bop help-cond
  where
    help-int : ∀ n {v₁ v₂} → (i n ⇓ v₁) × (i n ⇓ v₂) → v₁ ≡ v₂
    help-int n (E-Int , E-Int) = refl
    help-bool : ∀ v {v₁ v₂} → (b v ⇓ v₁) × (b v ⇓ v₂) → v₁ ≡ v₂
    help-bool v (E-Bool , E-Bool) = refl
    help-bop : ∀ e₁ e₂ ⊗ →
           (∀ {v₁ v₂} → (e₁ ⇓ v₁) × (e₁ ⇓ v₂) → v₁ ≡ v₂) ×
           (∀ {v₁ v₂} → (e₂ ⇓ v₁) × (e₂ ⇓ v₂) → v₁ ≡ v₂) →
           ∀ {v₁ v₂} → (op ⊗ e₁ e₂ ⇓ v₁) × (op ⊗ e₁ e₂ ⇓ v₂) → v₁ ≡ v₂
    help-bop e₁ e₂ prim⊕ (proj₁ , proj₂) (E-Plus p₁ p₂ (B-Plus refl) , E-Plus p₃ p₄ (B-Plus refl))
      with proj₁ (p₁ , p₃) | proj₂ (p₂ , p₄)
    ... | refl | refl = refl
    help-bop e₁ e₂ prim⊝ (proj₁ , proj₂) (E-Minus p₁ p₂ (B-Minus refl) , E-Minus p₃ p₄ (B-Minus refl))
      with proj₁ (p₁ , p₃) | proj₂ (p₂ , p₄)
    ... | refl | refl = refl
    help-bop e₁ e₂ prim⊛ (proj₁ , proj₂) (E-Times p₁ p₂ (B-Times refl) , E-Times p₃ p₄ (B-Times refl))
      with proj₁ (p₁ , p₃) | proj₂ (p₂ , p₄)
    ... | refl | refl = refl
    help-bop e₁ e₂ prim≺ (proj₁ , proj₂) (E-Lt p₁ p₂ (B-Lt refl) , E-Lt p₃ p₄ (B-Lt refl))
      with proj₁ (p₁ , p₃) | proj₂ (p₂ , p₄)
    ... | refl | refl = refl
    help-cond : ∀ e₁ e₂ e₃ →
            (∀ {v₁ v₂} → (e₁ ⇓ v₁) × (e₁ ⇓ v₂) → v₁ ≡ v₂) ×
            (∀ {v₁ v₂} → (e₂ ⇓ v₁) × (e₂ ⇓ v₂) → v₁ ≡ v₂) ×
            (∀ {v₁ v₂} → (e₃ ⇓ v₁) × (e₃ ⇓ v₂) → v₁ ≡ v₂) →
            ∀ {v₁ v₂} → (if e₁ then e₂ else e₃ ⇓ v₁) × (if e₁ then e₂ else e₃ ⇓ v₂) → v₁ ≡ v₂
    help-cond e₁ e₂ e₃ (proj₁ , proj₂ , proj₃) (E-IfT p₁ p₂ , E-IfT p₃ p₄) = proj₂ (p₂ , p₄)
    help-cond e₁ e₂ e₃ (proj₁ , proj₂ , proj₃) (E-IfT p₁ p₂ , E-IfF p₃ p₄) with proj₁ (p₁ , p₃)
    ... | ()
    help-cond e₁ e₂ e₃ (proj₁ , proj₂ , proj₃) (E-IfF p₁ p₂ , E-IfT p₃ p₄) with proj₁ (p₁ , p₃)
    ... | ()
    help-cond e₁ e₂ e₃ (proj₁ , proj₂ , proj₃) (E-IfF p₁ p₂ , E-IfF p₃ p₄) = proj₃ (p₂ , p₄)
