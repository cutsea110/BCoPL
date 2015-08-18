module BCoPL.Induction where

open import Data.Product using (∃; _,_; _×_)
open import Function using (_∘_)

open import BCoPL.Nat

-- mathematical induction
inductionℕ : {P : ℕ → Set} → P Z × ((n : ℕ) → P n → P (S n)) → ((n : ℕ) → P n)
inductionℕ (z , s) Z = z
inductionℕ (z , s) (S n) = inductionℕ (s Z z , s ∘ S) n
