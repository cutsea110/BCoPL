module ex2 where

open import Data.Product using (∃; _,_)
open import Function using (const; id)
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
associativity-plus {Z} {n₅ = n₅} p₁ p₂ = n₅ , const P-Zero
associativity-plus {S n₁} {Z} {Z} {n₅ = n₅} p₁ p₂ = S n₅ , (λ ())
associativity-plus {S n₁} {Z} {S n₃} p₁ p₂ = Z , (λ ())
associativity-plus {S n₁} {S n₂} p₁ p₂ = Z , (λ ())

-- theorem 2.6
uniqueness-times : ∀ {n₁ n₂ n₃ n₄} → n₁ times n₂ is n₃ → n₁ times n₂ is n₄ → n₃ ≡ n₄
uniqueness-times T-Zero T-Zero = refl
uniqueness-times (T-Succ t₁ p₁) (T-Succ t₂ p₂)
  rewrite uniqueness-times t₁ t₂ | uniqueness-plus p₁ p₂ = refl

-- theorem 2.8 (1)
left-zero-times : ∀ {n} → Z times n is Z
left-zero-times = T-Zero
-- theorem 2.8 (2)
right-zero-times : ∀ {n} → n times Z is Z
right-zero-times {Z} = T-Zero
right-zero-times {S n} = T-Succ right-zero-times P-Zero

-- theorem 2.7
closure-times : ∀ {n₁ n₂} → ∃ λ n₃ → n₁ times n₂ is n₃
closure-times {Z} = Z , T-Zero
closure-times {S n₁} {Z} = Z , right-zero-times
closure-times {S n₁} {S n₂} = S n₁ * S n₂ , help
  where
    help : ∀ {n₁ n₂} → S n₁ times S n₂ is S (n₂ + n₁ * S n₂)
    help {n₁} {n₂} = T-Succ help₂ (P-Succ help₃)
      where
        help₂ : ∀ {n₁ n₂} → n₁ times S n₂ is (n₁ * S n₂)
        help₂ {Z} {n₂} = T-Zero
        help₂ {S n₁} = help
        help₃ : ∀ {n₁ n₂} → n₁ plus n₂ is (n₁ + n₂)
        help₃ {Z} = P-Zero
        help₃ {S n₁} = P-Succ help₃

-- theorem 2.9
commutativity-times : ∀ {n₁ n₂ n₃} → n₁ times n₂ is n₃ → n₂ times n₁ is n₃
commutativity-times T-Zero = right-zero-times
commutativity-times (T-Succ t p) = help (commutativity-times t) p
  where
    help : ∀ {n₁ n₂ n₃ n₄} → n₁ times n₂ is n₄ → n₁ plus n₄ is n₃ → n₁ times S n₂ is n₃
    help {Z} T-Zero P-Zero = T-Zero
    help {S n₁} (T-Succ t₁ p₁) (P-Succ p₂) = {!!}

-- theorem 2.10
associativity-times : ∀ {n₁ n₂ n₃ n₄ n₅} → n₁ times n₂ is n₄ → n₄ times n₃ is n₅ →
                      ∃ λ n₆ → n₂ times n₃ is n₆ → n₁ times n₆ is n₅
associativity-times t₁ t₂ = {!!}
