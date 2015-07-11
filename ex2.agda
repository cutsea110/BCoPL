module ex2 where

open import BCoPL.Nat
open import BCoPL.Show.Nat
open import Relation.Binary.PropositionalEquality as PropEq

-- theorem 2.1 (1)
left-identity-plus : ∀ {n} → Z plus n is n
left-identity-plus = P-Zero
-- theorem 2.1 (2)
right-identity-plus : ∀ {n} → n plus Z is n
right-identity-plus {Z} = P-Zero
right-identity-plus {S n} = P-Succ right-identity-plus

-- theorem 2.2
uniqueness-plus : ∀ {n₁ n₂ n₃ n₄} → n₁ plus n₂ is n₃ → n₁ plus n₂ is n₄ → n₃ ≡ n₄
uniqueness-plus P-Zero P-Zero = refl
uniqueness-plus (P-Succ p) (P-Succ q) = cong S (uniqueness-plus p q)

