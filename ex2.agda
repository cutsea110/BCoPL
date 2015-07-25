module ex2 where

open import Data.Product using (∃; _,_; _×_)
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
uniqueness-plus : ∀ {n₁ n₂ n₃ n₄} → (n₁ plus n₂ is n₃) × (n₁ plus n₂ is n₄) → n₃ ≡ n₄
uniqueness-plus (P-Zero , P-Zero) = refl
uniqueness-plus (P-Succ proj₁ , P-Succ proj₂) = cong S (uniqueness-plus (proj₁ , proj₂))

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
x+0+y=x+y : ∀ {n₁ n₂ n₃ n₄} → n₁ plus Z is n₂ → n₂ plus n₃ is n₄ → n₁ plus n₃ is n₄
x+0+y=x+y P-Zero q = q
x+0+y=x+y (P-Succ p) (P-Succ q) = P-Succ (x+0+y=x+y p q)

x+y+0=x+y : ∀ {n₁ n₂ n₃ n₄} → n₁ plus n₂ is n₃ → n₃ plus Z is n₄ → n₁ plus n₂ is n₄
x+y+0=x+y p P-Zero = p
x+y+0=x+y P-Zero (P-Succ q) = commutativity-plus (P-Succ q)
x+y+0=x+y (P-Succ p) (P-Succ q) = P-Succ (x+y+0=x+y p q)

associativity-plus : ∀ {n₁ n₂ n₃ n₄ n₅} → (n₁ plus n₂ is n₄) × (n₄ plus n₃ is n₅) →
                     ∃ λ n₆ → (n₂ plus n₃ is n₆) × (n₁ plus n₆ is n₅)
associativity-plus {Z} {Z} {n₃ = n₃} (P-Zero , P-Zero) = n₃ , P-Zero , P-Zero
associativity-plus {Z} {S n₂} {n₅ = n₅} (P-Zero , proj₂) = n₅ , proj₂ , P-Zero
associativity-plus {S n₁} {Z} {n₃} (P-Succ proj₁ , P-Succ proj₂)
  = n₃ , P-Zero , P-Succ (x+0+y=x+y proj₁ proj₂)
associativity-plus {S n₁} {S n₂} {Z} (P-Succ proj₁ , P-Succ proj₂)
  = (S n₂) , right-identity-plus , P-Succ (x+y+0=x+y proj₁ proj₂)
associativity-plus {S n₁} {S n₂} {S n₃} (P-Succ proj₁ , P-Succ proj₂) with associativity-plus (proj₁ , proj₂)
associativity-plus {S n₁} {S n₂} {S n₃} (P-Succ proj₁ , P-Succ proj₂) | Z , proj₃ , proj₄
  = Z , proj₃ , P-Succ proj₄
associativity-plus {S n₁} {S n₂} {S n₃} (P-Succ proj₁ , P-Succ proj₂) | S proj₃ , proj₄ , proj₅
  = S proj₃ , proj₄ , P-Succ proj₅

-- theorem 2.6
uniqueness-times : ∀ {n₁ n₂ n₃ n₄} → (n₁ times n₂ is n₃) × (n₁ times n₂ is n₄) → n₃ ≡ n₄
uniqueness-times (T-Zero , T-Zero) = refl
uniqueness-times (T-Succ t₁ p₁ , T-Succ t₂ p₂)
  rewrite uniqueness-times (t₁ , t₂) | uniqueness-plus (p₁ , p₂) = refl

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
swap-plus : ∀ {n₁ n₂ n₃ n₄ n₅} → (n₂ plus n₃ is n₄) × (n₁ plus n₄ is n₅) →
            ∃ λ n₆ → (n₁ plus n₃ is n₆) × (n₂ plus n₆ is n₅)
swap-plus {n₃ = n₃} (proj₁ , P-Zero) = n₃ , P-Zero , proj₁
swap-plus (proj₁ , P-Succ proj₂) with swap-plus (proj₁ , proj₂)
swap-plus (proj₁ , P-Succ proj₂) | Z , P-Zero , proj₄
  = (S Z) , (P-Succ P-Zero) , commutativity-plus (P-Succ (commutativity-plus proj₄))
swap-plus (proj₁ , P-Succ proj₂) | S proj₃ , proj₄ , proj₅
  = S (S proj₃) , P-Succ proj₄ , commutativity-plus (P-Succ (commutativity-plus proj₅))

commutativity-times : ∀ {n₁ n₂ n₃} → n₁ times n₂ is n₃ → n₂ times n₁ is n₃
commutativity-times = {!!}

-- theorem 2.10
associativity-times : ∀ {n₁ n₂ n₃ n₄ n₅} → (n₁ times n₂ is n₄) × (n₄ times n₃ is n₅) →
                      ∃ λ n₆ → (n₂ times n₃ is n₆) × (n₁ times n₆ is n₅)
associativity-times = {!!}
