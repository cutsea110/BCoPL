module BCoPL.Nat.Properties where

open import Function
open import Data.Product using (∃; _,_; _×_)

open import BCoPL.Nat
open import BCoPL.Show.Nat
open import BCoPL.Induction

-- theorem 2.1 (1)
left-identity-plus : (n : ℕ) → Z plus n is n
left-identity-plus = inductionℕ (P-Zero , (λ n x → P-Zero))

-- theorem 2.1 (2)
right-identity-plus : (n : ℕ) → n plus Z is n
right-identity-plus = inductionℕ (P-Zero , (λ n → P-Succ))
