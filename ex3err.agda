module ex3err where

open import Data.Product
open import Data.Sum

open import BCoPL.EvalML1Err
open import BCoPL.Show.EvalML1Err
open import Data.Nat hiding (_<_; _+_) renaming (_*_ to _⋆_)

-- excercise 3.3
ex-3-3-1 : i (+ 1) ⊕ b true ⊕ i (+ 2) ⇓ left error
ex-3-3-1 = E-PlusErrorL (E-PlusBoolR E-Bool)
{-
((1 + true) + 2) evalto error by E-PlusErrorL {
  (1 + true) evalto error by E-PlusBoolR {
    true evalto true by E-Bool {};
  };
};
-}
ex-3-3-2 : if i (+ 2) ⊕ i (+ 3) then i (+ 1) else i (+ 3) ⇓ left error
ex-3-3-2 = E-IfInt (E-Plus E-Int E-Int (B-Plus refl))
{-
if (2 + 3) then 1 else 3 evalto error by E-IfInt {
  (2 + 3) evalto 5 by E-Plus {
    2 evalto 2 by E-Int {};
    3 evalto 3 by E-Int {};
    2 plus 3 is 5 by B-Plus {};
  };
};
-}
ex-3-3-3 : if i (+ 3) ≺ i (+ 4) then i (+ 1) ≺ b true else i (+ 3) ⊝ b false ⇓ left error
ex-3-3-3 = E-IfTError (E-Lt E-Int E-Int (B-Lt refl) , E-LtBoolR E-Bool)
{-
if (3 < 4) then (1 < true) else (3 - false) evalto error by E-IfTError {
  (3 < 4) evalto true by E-Lt {
    3 evalto 3 by E-Int {};
    4 evalto 4 by E-Int {};
    3 less than 4 is true by B-Lt {};
  };
  (1 < true) evalto error by E-LtBoolR {
    true evalto true by E-Bool {};
  };
};
-}

-- theorem 3.4
open import Data.Sign using () renaming (_*_ to _<>_)

totality-⇓ : (e : Exp) → ∃ λ v → e ⇓ right v ⊎ ∃ λ ε → e ⇓ left ε
totality-⇓ (i n) = i n , inj₁ E-Int
totality-⇓ (b v) = b v , inj₁ E-Bool
totality-⇓ (op ⊗ e₁ e₂) with totality-⇓ e₁ | totality-⇓ e₂
totality-⇓ (op prim⊕ e₁ e₂) | i x , inj₁ p₁ | i x₁ , inj₁ p₂ = i (x + x₁) , inj₁ (E-Plus p₁ p₂ (B-Plus refl))
totality-⇓ (op prim⊕ e₁ e₂) | i x , inj₁ p₁ | b x₁ , inj₁ p₂ = b x₁ , inj₂ (error , E-PlusBoolR p₂)
totality-⇓ (op prim⊕ e₁ e₂) | b x , inj₁ p₁ | i x₁ , inj₁ p₂ = b x , inj₂ (error , E-PlusBoolL p₁)
totality-⇓ (op prim⊕ e₁ e₂) | b x , inj₁ p₁ | b x₁ , inj₁ p₂ = b x , inj₂ (error , E-PlusBoolL p₁)
totality-⇓ (op prim⊝ e₁ e₂) | i x , inj₁ p₁ | i x₁ , inj₁ p₂ = i (x + - x₁) , inj₁ (E-Minus p₁ p₂ (B-Minus refl))
totality-⇓ (op prim⊝ e₁ e₂) | i x , inj₁ p₁ | b x₁ , inj₁ p₂ = b x₁ , inj₂ (error , E-MinusBoolR p₂)
totality-⇓ (op prim⊝ e₁ e₂) | b x , inj₁ p₁ | i x₁ , inj₁ p₂ = b x , inj₂ (error , E-MinusBoolL p₁)
totality-⇓ (op prim⊝ e₁ e₂) | b x , inj₁ p₁ | b x₁ , inj₁ p₂ = b x , inj₂ (error , E-MinusBoolL p₁)
totality-⇓ (op prim⊛ e₁ e₂) | i x , inj₁ p₁ | i x₁ , inj₁ p₂ = i (sign x <> sign x₁ ◃ ∣ x ∣ ⋆ ∣ x₁ ∣) , inj₁ (E-Times p₁ p₂ (B-Times refl))
totality-⇓ (op prim⊛ e₁ e₂) | i x , inj₁ p₁ | b x₁ , inj₁ p₂ = b x₁ , inj₂ (error , E-TimesBoolR p₂)
totality-⇓ (op prim⊛ e₁ e₂) | b x , inj₁ p₁ | i x₁ , inj₁ p₂ = b x , inj₂ (error , E-TimesBoolL p₁)
totality-⇓ (op prim⊛ e₁ e₂) | b x , inj₁ p₁ | b x₁ , inj₁ p₂ = b x , inj₂ (error , E-TimesBoolL p₁)
totality-⇓ (op prim≺ e₁ e₂) | i x , inj₁ p₁ | i x₁ , inj₁ p₂ = b (x < x₁) , inj₁ (E-Lt p₁ p₂ (B-Lt refl))
totality-⇓ (op prim≺ e₁ e₂) | i x , inj₁ p₁ | b x₁ , inj₁ p₂ = b x₁ , inj₂ (error , E-LtBoolR p₂)
totality-⇓ (op prim≺ e₁ e₂) | b x , inj₁ p₁ | i x₁ , inj₁ p₂ = b x , inj₂ (error , E-LtBoolL p₁)
totality-⇓ (op prim≺ e₁ e₂) | b x , inj₁ p₁ | b x₁ , inj₁ p₂ = b x , inj₂ (error , E-LtBoolL p₁)
totality-⇓ (op prim⊕ e₁ e₂) | i x , inj₁ x₁ | i x₂ , inj₂ (error , p₂) = i x₂ , inj₂ (error , E-PlusErrorR p₂)
totality-⇓ (op prim⊕ e₁ e₂) | i x , inj₁ x₁ | b x₂ , inj₂ (error , p₂) = i x , inj₂ (error , E-PlusErrorR p₂)
totality-⇓ (op prim⊕ e₁ e₂) | b x , inj₁ x₁ | i x₂ , inj₂ y = b x , inj₂ (error , E-PlusBoolL x₁)
totality-⇓ (op prim⊕ e₁ e₂) | b x , inj₁ x₁ | b x₂ , inj₂ y = b x , inj₂ (error , E-PlusBoolL x₁)
totality-⇓ (op prim⊝ e₁ e₂) | i x , inj₁ x₁ | i x₂ , inj₂ (error , p₂) = i x₂ , inj₂ (error , E-MinusErrorR p₂)
totality-⇓ (op prim⊝ e₁ e₂) | i x , inj₁ x₁ | b x₂ , inj₂ (error , p₂) = i x , inj₂ (error , E-MinusErrorR p₂)
totality-⇓ (op prim⊝ e₁ e₂) | b x , inj₁ x₁ | i x₂ , inj₂ y = b x , inj₂ (error , E-MinusBoolL x₁)
totality-⇓ (op prim⊝ e₁ e₂) | b x , inj₁ x₁ | b x₂ , inj₂ y = b x , inj₂ (error , E-MinusBoolL x₁)
totality-⇓ (op prim⊛ e₁ e₂) | i x , inj₁ x₁ | i x₂ , inj₂ (error , p₂) = i x₂ , inj₂ (error , E-TimesErrorR p₂)
totality-⇓ (op prim⊛ e₁ e₂) | i x , inj₁ x₁ | b x₂ , inj₂ (error , p₂) = b x₂ , inj₂ (error , E-TimesErrorR p₂)
totality-⇓ (op prim⊛ e₁ e₂) | b x , inj₁ x₁ | i x₂ , inj₂ y = b x , inj₂ (error , E-TimesBoolL x₁)
totality-⇓ (op prim⊛ e₁ e₂) | b x , inj₁ x₁ | b x₂ , inj₂ y = b x , inj₂ (error , E-TimesBoolL x₁)
totality-⇓ (op prim≺ e₁ e₂) | i x , inj₁ x₁ | i x₂ , inj₂ (error , p₂) = i x₂ , inj₂ (error , E-LtErrorR p₂)
totality-⇓ (op prim≺ e₁ e₂) | i x , inj₁ x₁ | b x₂ , inj₂ (error , p₂) = i x , inj₂ (error , E-LtErrorR p₂)
totality-⇓ (op prim≺ e₁ e₂) | b x , inj₁ x₁ | i x₂ , inj₂ y = b x , inj₂ (error , E-LtBoolL x₁)
totality-⇓ (op prim≺ e₁ e₂) | b x , inj₁ x₁ | b x₂ , inj₂ y = b x , inj₂ (error , E-LtBoolL x₁)
totality-⇓ (op prim⊕ e₁ e₂) | i x , inj₂ (error , p₂) | i x₁ , inj₁ x₂ = i x₁ , inj₂ (error , E-PlusErrorL p₂)
totality-⇓ (op prim⊕ e₁ e₂) | i x , inj₂ y | b x₁ , inj₁ x₂ = b x₁ , inj₂ (error , E-PlusBoolR x₂)
totality-⇓ (op prim⊕ e₁ e₂) | b x , inj₂ (error , p₂) | i x₁ , inj₁ x₂ = i x₁ , inj₂ (error , E-PlusErrorL p₂)
totality-⇓ (op prim⊕ e₁ e₂) | b x , inj₂ y | b x₁ , inj₁ x₂ = b x , inj₂ (error , E-PlusBoolR x₂)
totality-⇓ (op prim⊝ e₁ e₂) | i x , inj₂ (error , p₂) | i x₁ , inj₁ x₂ = i x₁ , inj₂ (error , E-MinusErrorL p₂)
totality-⇓ (op prim⊝ e₁ e₂) | i x , inj₂ y | b x₁ , inj₁ x₂ = b x₁ , inj₂ (error , E-MinusBoolR x₂)
totality-⇓ (op prim⊝ e₁ e₂) | b x , inj₂ (error , p₂) | i x₁ , inj₁ x₂ = i x₁ , inj₂ (error , E-MinusErrorL p₂)
totality-⇓ (op prim⊝ e₁ e₂) | b x , inj₂ y | b x₁ , inj₁ x₂ = b x , inj₂ (error , E-MinusBoolR x₂)
totality-⇓ (op prim⊛ e₁ e₂) | i x , inj₂ (error , p₂) | i x₁ , inj₁ x₂ = i x , inj₂ (error , E-TimesErrorL p₂)
totality-⇓ (op prim⊛ e₁ e₂) | i x , inj₂ y | b x₁ , inj₁ x₂ = b x₁ , inj₂ (error , E-TimesBoolR x₂)
totality-⇓ (op prim⊛ e₁ e₂) | b x , inj₂ (error , p₂) | i x₁ , inj₁ x₂ = (b x) , inj₂ (error , E-TimesErrorL p₂)
totality-⇓ (op prim⊛ e₁ e₂) | b x , inj₂ y | b x₁ , inj₁ x₂ = b x , inj₂ (error , E-TimesBoolR x₂)
totality-⇓ (op prim≺ e₁ e₂) | i x , inj₂ (error , p₂) | i x₁ , inj₁ x₂ = i x₁ , inj₂ (error , E-LtErrorL p₂)
totality-⇓ (op prim≺ e₁ e₂) | i x , inj₂ y | b x₁ , inj₁ x₂ = b x₁ , inj₂ (error , E-LtBoolR x₂)
totality-⇓ (op prim≺ e₁ e₂) | b x , inj₂ (error , p₂) | i x₁ , inj₁ x₂ = i x₁ , inj₂ (error , E-LtErrorL p₂)
totality-⇓ (op prim≺ e₁ e₂) | b x , inj₂ y | b x₁ , inj₁ x₂ = b x , inj₂ (error , E-LtBoolR x₂)
totality-⇓ (op prim⊕ e₁ e₂) | i x , inj₂ (error , p₂) | i x₁ , inj₂ y₁ = i x₁ , inj₂ (error , E-PlusErrorL p₂)
totality-⇓ (op prim⊕ e₁ e₂) | i x , inj₂ (error , p₂) | b x₁ , inj₂ y₁ = i x , inj₂ (error , E-PlusErrorL p₂)
totality-⇓ (op prim⊕ e₁ e₂) | b x , inj₂ (error , p₂) | i x₁ , inj₂ y₁ = i x₁ , inj₂ (error , E-PlusErrorL p₂)
totality-⇓ (op prim⊕ e₁ e₂) | b x , inj₂ (error , p₂) | b x₁ , inj₂ y₁ = b x₁ , inj₂ (error , E-PlusErrorL p₂)
totality-⇓ (op prim⊝ e₁ e₂) | i x , inj₂ (error , p₂) | i x₁ , inj₂ y₁ = i x₁ , inj₂ (error , E-MinusErrorL p₂)
totality-⇓ (op prim⊝ e₁ e₂) | i x , inj₂ (error , p₂) | b x₁ , inj₂ y₁ = i x , inj₂ (error , E-MinusErrorL p₂)
totality-⇓ (op prim⊝ e₁ e₂) | b x , inj₂ (error , p₂) | i x₁ , inj₂ y₁ = i x₁ , inj₂ (error , E-MinusErrorL p₂)
totality-⇓ (op prim⊝ e₁ e₂) | b x , inj₂ (error , p₂) | b x₁ , inj₂ y₁ = b x₁ , inj₂ (error , E-MinusErrorL p₂)
totality-⇓ (op prim⊛ e₁ e₂) | i x , inj₂ (error , p₂) | i x₁ , inj₂ y₁ = i x , inj₂ (error , E-TimesErrorL p₂)
totality-⇓ (op prim⊛ e₁ e₂) | i x , inj₂ (error , p₂) | b x₁ , inj₂ y₁ = i x , inj₂ (error , E-TimesErrorL p₂)
totality-⇓ (op prim⊛ e₁ e₂) | b x , inj₂ (error , p₂) | i x₁ , inj₂ y₁ = b x , inj₂ (error , E-TimesErrorL p₂)
totality-⇓ (op prim⊛ e₁ e₂) | b x , inj₂ (error , p₂) | b x₁ , inj₂ y₁ = b x , inj₂ (error , E-TimesErrorL p₂)
totality-⇓ (op prim≺ e₁ e₂) | i x , inj₂ (error , p₂) | i x₁ , inj₂ y₁ = i x₁ , inj₂ (error , E-LtErrorL p₂)
totality-⇓ (op prim≺ e₁ e₂) | i x , inj₂ (error , p₂) | b x₁ , inj₂ y₁ = i x , inj₂ (error , E-LtErrorL p₂)
totality-⇓ (op prim≺ e₁ e₂) | b x , inj₂ (error , p₂) | i x₁ , inj₂ y₁ = i x₁ , inj₂ (error , E-LtErrorL p₂)
totality-⇓ (op prim≺ e₁ e₂) | b x , inj₂ (error , p₂) | b x₁ , inj₂ y₁ = b x₁ , inj₂ (error , E-LtErrorL p₂)
totality-⇓ (if e then e₁ else e₂) with totality-⇓ e | totality-⇓ e₁ | totality-⇓ e₂
totality-⇓ (if e then e₁ else e₂) | i x , inj₁ x₁ | p₁ | p₂ = i x , inj₂ (error , E-IfInt x₁)
totality-⇓ (if e then e₁ else e₂) | b true , inj₁ x₁ | i x , inj₂ (error , proj₂) | p₂ = i x , inj₂ (error , E-IfTError (x₁ , proj₂))
totality-⇓ (if e then e₁ else e₂) | b true , inj₁ x₁ | proj₁ , inj₁ x₂ | p₂ = proj₁ , inj₁ (E-IfT x₁ x₂)
totality-⇓ (if e then e₁ else e₂) | b true , inj₁ x₁ | b x , inj₂ (error , proj₂) | p₂ = b x , inj₂ (error , E-IfTError (x₁ , proj₂))
totality-⇓ (if e then e₁ else e₂) | b false , inj₁ x₁ | p₁ | proj₁ , inj₁ x = proj₁ , inj₁ (E-IfF x₁ x)
totality-⇓ (if e then e₁ else e₂) | b false , inj₁ x₁ | p₁ | proj₁ , inj₂ (error , proj₃) = proj₁ , inj₂ (error , E-IfFError (x₁ , proj₃))
totality-⇓ (if e then e₁ else e₂) | proj₁ , inj₂ (error , proj₃) | p₁ | p₂ = proj₁ , inj₂ (error , E-IfError proj₃)
