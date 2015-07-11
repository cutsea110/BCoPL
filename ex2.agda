module ex2 where

open import BCoPL.Nat
open import BCoPL.Show.Nat
open import Relation.Binary.PropositionalEquality as PropEq
open import Data.Product using (∃; _,_)

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

-- theorem 2.3
closure-plus : ∀ {n₁ n₂} → ∃ λ n₃ → n₁ plus n₂ is n₃
closure-plus {Z} {Z} = Z , P-Zero
closure-plus {Z} {S n₂} = S n₂ , P-Zero
closure-plus {S n₁} {Z} = S n₁ , P-Succ right-identity-plus
closure-plus {S n₁} {S n₂} = S n₁ + S n₂ , P-Succ help
  where
    help : ∀ {n₁ n₂} → n₁ plus S n₂ is (n₁ + S n₂)
    help {Z} = λ {n₃} → P-Zero
    help {S n₃} = P-Succ help
