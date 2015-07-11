module ex2 where

open import BCoPL.Nat
open import BCoPL.Show.Nat

-- theorem 2.1 (1)
left-identity-plus : ∀ {n} → Z plus n is n
left-identity-plus = P-Zero
-- theorem 2.1 (2)
right-identity-plus : ∀ {n} → n plus Z is n
right-identity-plus {Z} = P-Zero
right-identity-plus {S n} = P-Succ right-identity-plus

