module ex2 where

open import Data.Product using (∃; _,_; _×_)
open import Function using (const; id)
open import Relation.Binary.PropositionalEquality as PropEq

open import BCoPL.Nat
open import BCoPL.Show.Nat

-- theorem 2.1 (1)
left-identity-plus : (n : ℕ) → Z plus n is n
left-identity-plus n = P-Zero
-- theorem 2.1 (2)
right-identity-plus : (n : ℕ) → n plus Z is n
right-identity-plus Z = P-Zero
right-identity-plus (S n) = P-Succ (right-identity-plus n)

-- theorem 2.2
uniqueness-plus : ∀ {n₁ n₂ n₃ n₄} → (n₁ plus n₂ is n₃) × (n₁ plus n₂ is n₄) → n₃ ≡ n₄
uniqueness-plus (P-Zero , P-Zero) = refl
uniqueness-plus (P-Succ proj₁ , P-Succ proj₂) = cong S (uniqueness-plus (proj₁ , proj₂))

-- theorem 2.3
closure-plus : (n₁ n₂ : ℕ) → ∃ λ n₃ → n₁ plus n₂ is n₃
closure-plus Z n₂ = n₂ , P-Zero
closure-plus (S n₁) n₂ with closure-plus n₁ n₂
closure-plus (S n₁) n₂ | proj₁ , proj₂ = S proj₁ , P-Succ proj₂

-- theorem 2.4
commutativity-plus : ∀ {n₁ n₂ n₃} → n₁ plus n₂ is n₃ → n₂ plus n₁ is n₃
commutativity-plus {Z} {n₂} P-Zero = right-identity-plus n₂
commutativity-plus {S n₁} (P-Succ p) = help (commutativity-plus p)
  where
    help : ∀ {n₁ n₂ n₃} → n₁ plus n₂ is n₃ → n₁ plus S n₂ is S n₃
    help P-Zero = P-Zero
    help (P-Succ p) = P-Succ (help p)

-- theorem 2.5
associativity-plus : ∀ {n₁ n₂ n₃ n₄ n₅} → (n₁ plus n₂ is n₄) × (n₄ plus n₃ is n₅) →
                     ∃ λ n₆ → (n₂ plus n₃ is n₆) × (n₁ plus n₆ is n₅)
associativity-plus {n₅ = n₅} (P-Zero , proj₂) = n₅ , proj₂ , P-Zero
associativity-plus (P-Succ proj₁ , P-Succ proj₂) with associativity-plus (proj₁ , proj₂)
associativity-plus (P-Succ proj₁ , P-Succ proj₂) | proj₃ , proj₄ , proj₅ = proj₃ , proj₄ , P-Succ proj₅

-- theorem 2.6
uniqueness-times : ∀ {n₁ n₂ n₃ n₄} → (n₁ times n₂ is n₃) × (n₁ times n₂ is n₄) → n₃ ≡ n₄
uniqueness-times (T-Zero , T-Zero) = refl
uniqueness-times (T-Succ t₁ p₁ , T-Succ t₂ p₂)
  rewrite uniqueness-times (t₁ , t₂) | uniqueness-plus (p₁ , p₂) = refl

-- theorem 2.8 (1)
left-zero-times : (n : ℕ) → Z times n is Z
left-zero-times n = T-Zero
-- theorem 2.8 (2)
right-zero-times : (n : ℕ) → n times Z is Z
right-zero-times Z = T-Zero
right-zero-times (S n) = T-Succ (right-zero-times n) P-Zero

-- theorem 2.7
closure-times : (n₁ n₂ : ℕ) → ∃ λ n₃ → n₁ times n₂ is n₃
closure-times Z n₂ = Z , T-Zero
closure-times (S n₁) n₂ with closure-times n₁ n₂
... | proj₁ , proj₂ with closure-plus n₂ proj₁
... | proj₃ , proj₄ = proj₃ , T-Succ proj₂ proj₄

-- theorem 2.9
swap-plus : ∀ {n₁ n₂ n₃ n₄ n₅} → (n₂ plus n₃ is n₄) × (n₁ plus n₄ is n₅) →
            ∃ λ n₆ → (n₁ plus n₃ is n₆) × (n₂ plus n₆ is n₅)
swap-plus {n₃ = n₃} (proj₁ , P-Zero) = n₃ , P-Zero , proj₁
swap-plus (proj₁ , P-Succ proj₂) with swap-plus (proj₁ , proj₂)
... | Z , P-Zero , proj₄
  = (S Z) , (P-Succ P-Zero) , commutativity-plus (P-Succ (commutativity-plus proj₄))
... | S proj₃ , proj₄ , proj₅
  = S (S proj₃) , P-Succ proj₄ , commutativity-plus (P-Succ (commutativity-plus proj₅))

commutativity-times : ∀ {n₁ n₂ n₃} → n₁ times n₂ is n₃ → n₂ times n₁ is n₃
commutativity-times {n₂ = n₂} T-Zero = right-zero-times n₂
commutativity-times (T-Succ t p) = help (commutativity-times t) p
  where
    help : ∀ {n₁ n₂ n₃ n₄} → n₂ times n₁ is n₄ → n₂ plus n₄ is n₃ → n₂ times S n₁ is n₃
    help T-Zero P-Zero = T-Zero
    help (T-Succ t₁ p₁) p₂ = {!!}

-- theorem 2.10
associativity-times : ∀ {n₁ n₂ n₃ n₄ n₅} → (n₁ times n₂ is n₄) × (n₄ times n₃ is n₅) →
                      ∃ λ n₆ → (n₂ times n₃ is n₆) × (n₁ times n₆ is n₅)
associativity-times = {!!}
