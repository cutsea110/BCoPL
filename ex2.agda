module ex2 where

open import Data.Product using (∃; _,_)
open import Relation.Binary.PropositionalEquality as PropEq

open import BCoPL.Nat
open import BCoPL.Show.Nat

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

-- theorem 2.4
commutativity-plus : ∀ {n₁ n₂ n₃} → n₁ plus n₂ is n₃ → n₂ plus n₁ is n₃
commutativity-plus {Z} P-Zero = right-identity-plus
commutativity-plus {S n₁} (P-Succ p) = help (commutativity-plus p)
  where
    help : ∀ {n₁ n₂ n₃} → n₁ plus n₂ is n₃ → n₁ plus S n₂ is S n₃
    help P-Zero = P-Zero
    help (P-Succ p) = P-Succ (help p)

-- theorem 2.5
associativity-plus : ∀ {n₁ n₂ n₃ n₄ n₅} → n₁ plus n₂ is n₄ → n₄ plus n₃ is n₅ →
                     ∃ λ n₆ → n₂ plus n₃ is n₆ → n₁ plus n₆ is n₅
associativity-plus {Z} {Z} {Z} {Z} {Z} P-Zero P-Zero = Z , (λ x → x)
associativity-plus {Z} {Z} {Z} {Z} {S n₅} P-Zero ()
associativity-plus {Z} {Z} {n₄ = S n₄} () l₂
associativity-plus {Z} {Z} {S n₃} {Z} {Z} P-Zero ()
associativity-plus {Z} {Z} {S n₃} {Z} {S .n₃} P-Zero P-Zero = S n₃ , (λ x → x)
associativity-plus {Z} {S n₂} {n₄ = Z} () l₂
associativity-plus {Z} {S n₂} {n₄ = S .n₂} {n₅ = Z} P-Zero ()
associativity-plus {Z} {S n₂} {n₄ = S .n₂} {n₅ = S n₅} P-Zero (P-Succ l₂) = S n₅ , (λ x → P-Zero)
associativity-plus {S n₁} {n₄ = Z} () l₂
associativity-plus {S n₁} {n₄ = S n₄} {n₅ = Z} (P-Succ l₁) ()
associativity-plus {S n₁} {Z} {Z} {S n₄} {S n₅} (P-Succ l₁) (P-Succ l₂) = S n₅ , (λ ())
associativity-plus {S n₁} {Z} {S n₃} {S n₄} {S n₅} (P-Succ l₁) (P-Succ l₂) = Z , (λ ())
associativity-plus {S n₁} {S n₂} {n₄ = S n₄} {n₅ = S n₅} (P-Succ l₁) (P-Succ l₂) = Z , (λ ())