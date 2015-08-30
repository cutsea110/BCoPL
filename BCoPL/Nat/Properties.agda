module BCoPL.Nat.Properties where

open import Data.Product using (∃; _,_; _×_)
open import Function using (const; id)
open import Relation.Binary.PropositionalEquality as PropEq

open import BCoPL.Nat
open import BCoPL.Show.Nat

-- theorem 2.1 (1)
left-identity-plus : (n : ℕ) → Z plus n is n
left-identity-plus n = P-Zero

{-
-- theorem 2.1 (1)
left-identity-plus : (n : ℕ) → Z plus n is n
left-identity-plus = inductionℕ (P-Zero , (λ n x → P-Zero))

-- theorem 2.1 (2)
right-identity-plus : (n : ℕ) → n plus Z is n
right-identity-plus = inductionℕ (P-Zero , (λ n → P-Succ))
-}

-- theorem 2.1 (2)
right-identity-plus : (n : ℕ) → n plus Z is n
right-identity-plus Z = P-Zero
right-identity-plus (S n) = P-Succ (right-identity-plus n)

-- theorem 2.2
uniqueness-plus : ∀ {n₁ n₂ n₃ n₄} → (n₁ plus n₂ is n₃) × (n₁ plus n₂ is n₄) → n₃ ≡ n₄
uniqueness-plus (P-Zero , P-Zero) = refl
uniqueness-plus (P-Succ proj₁ , P-Succ proj₂) = cong S (uniqueness-plus (proj₁ , proj₂))

-- theorem 2.2
open import BCoPL.Induction

uniqueness-plus′ : (n₁ : ℕ) → ∀ {n₂ n₃ n₄} → (n₁ plus n₂ is n₃) × (n₁ plus n₂ is n₄) → n₃ ≡ n₄
uniqueness-plus′ = inductionℕ ({!base!} , step)
  where
    base : ∀ {n₂ n₃ n₄} → (Z plus n₂ is n₃) × (Z plus n₂ is n₄) → n₃ ≡ n₄
    base (P-Zero , P-Zero) = refl
    step : ∀ n → (∀ {n₂ n₃ n₄} → n plus n₂ is n₃ × n plus n₂ is n₄ → n₃ ≡ n₄) →
       ∀ {n₂ n₃ n₄} → S n plus n₂ is n₃ × S n plus n₂ is n₄ → n₃ ≡ n₄
    step n p (P-Succ p₁ , P-Succ p₂) = cong S (p (p₁ , p₂))

-- theorem 2.3
closure-plus : (n₁ n₂ : ℕ) → ∃ λ n₃ → n₁ plus n₂ is n₃
closure-plus Z n₂ = n₂ , P-Zero
closure-plus (S n₁) n₂ with closure-plus n₁ n₂
closure-plus (S n₁) n₂ | proj₁ , proj₂ = S proj₁ , P-Succ proj₂

{-
-- theorem 2.3
closure-plus : (n₁ n₂ : ℕ) → ∃ λ n₃ → n₁ plus n₂ is n₃
closure-plus = inductionℕ (base , step)
  where
    base : (n₂ : ℕ) → ∃ λ n → Z plus n₂ is n
    base n = n , P-Zero
    step : (n : ℕ) → ((n₂ : ℕ) → ∃ λ n₃ → n plus n₂ is n₃) →
           (n₂ : ℕ) → ∃ λ n₃ → ((S n) plus n₂ is n₃)
    step = {!!}
-}

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

left-identity-times : (n : ℕ) → S Z times n is n
left-identity-times Z = T-Succ T-Zero P-Zero
left-identity-times (S n) with left-identity-times n
... | T-Succ T-Zero n+0=n with right-identity-plus n
... | prf = T-Succ T-Zero (P-Succ n+0=n)

right-identity-times : (n : ℕ) → n times S Z is n
right-identity-times Z = T-Zero
right-identity-times (S n) with right-identity-times n
... | prf = T-Succ prf (P-Succ P-Zero)

commutativity-times : ∀ {n₁ n₂ n₃} → n₁ times n₂ is n₃ → n₂ times n₁ is n₃
commutativity-times {n₂ = n₂} T-Zero = right-zero-times n₂
commutativity-times (T-Succ t p) = help (commutativity-times t) p
  where
    help : ∀ {n₁ n₂ n₃ n₄} → n₂ times n₁ is n₄ → n₂ plus n₄ is n₃ → n₂ times S n₁ is n₃
    help T-Zero P-Zero = T-Zero
    help (T-Succ t₁ p₁) (P-Succ p₂) with swap-plus (p₁ , p₂)
    help (T-Succ t₁ p₁) (P-Succ p₂) | proj₁ , proj₂ , proj₃
      = T-Succ (commutativity-times (T-Succ (commutativity-times t₁) proj₂)) (P-Succ proj₃)

-- theorem 2.10
n+Sm=Sn+m : ∀ {n₁ n₂ n₃} → n₁ plus S n₂ is n₃ → S n₁ plus n₂ is n₃
n+Sm=Sn+m P-Zero = P-Succ P-Zero
n+Sm=Sn+m (P-Succ p) = P-Succ (n+Sm=Sn+m p)
Sn+m=n+Sm : ∀ {n₁ n₂ n₃} → S n₁ plus n₂ is n₃ → n₁ plus S n₂ is n₃
Sn+m=n+Sm (P-Succ p) = commutativity-plus (P-Succ (commutativity-plus p))

associativity-plus-rev : ∀ {n₁ n₂ n₃ n₄ n₅} → (n₂ plus n₃ is n₄) × (n₁ plus n₄ is n₅) →
                     ∃ λ n₆ → (n₁ plus n₂ is n₆) × (n₆ plus n₃ is n₅)
associativity-plus-rev (P-Zero , P-Zero) = Z , P-Zero , P-Zero
associativity-plus-rev {S n₁} (P-Zero , P-Succ p) = (S n₁) , P-Succ (right-identity-plus n₁) , P-Succ p
associativity-plus-rev {Z} {S n₂} (P-Succ p₁ , P-Zero) = (S n₂) , (P-Zero , (P-Succ p₁))
associativity-plus-rev {S n₁} {S n₂} {n₃} (P-Succ p₁ , P-Succ p₂) with n+Sm=Sn+m p₂
... | prf₁ with associativity-plus-rev (p₁ , prf₁)
... | proj₁ , proj₂ , proj₃ = (S proj₁) , (commutativity-plus (P-Succ (commutativity-plus proj₂)) , P-Succ proj₃)

distributivity-right : ∀ {n₁ n₂ n₃ n₄ n₅} → (n₁ plus n₂ is n₄) × (n₄ times n₃ is n₅) →
                     ∃ λ n₆ → ∃ λ n₇ → (n₁ times n₃ is n₆) × (n₂ times n₃ is n₇) × (n₆ plus n₇ is n₅)
distributivity-right {n₅ = n₅} (P-Zero , proj₂) = Z , n₅ , T-Zero , proj₂ , P-Zero
distributivity-right {S n₁} {n₂} {n₃} (P-Succ p₁ , T-Succ t₂ p₂) with distributivity-right (p₁ , t₂)
... | proj₁ , proj₂ , proj₃ , proj₄ , proj₅ with associativity-plus-rev (proj₅ , p₂)
... | proj₆ , proj₇ , proj₈ = proj₆ , (proj₂ , T-Succ proj₃ proj₇ , proj₄ , proj₈)


associativity-times : ∀ {n₁ n₂ n₃ n₄ n₅} → (n₁ times n₂ is n₄) × (n₄ times n₃ is n₅) →
                      ∃ λ n₆ → (n₂ times n₃ is n₆) × (n₁ times n₆ is n₅)
associativity-times {n₂ = n₂} {n₃ = n₃} (T-Zero , T-Zero) with closure-times n₂ n₃
... | proj₁ , proj₂ = proj₁ , proj₂ , T-Zero
associativity-times (T-Succ t₁ P-Zero , T-Zero) = Z , (T-Zero , T-Succ t₁ P-Zero)
associativity-times {S n₁} (T-Succ t₁ p₁ , t₂) with distributivity-right (p₁ , t₂)
... | proj₁ , proj₂ , proj₃ , proj₄ , proj₅ with associativity-times (t₁ , proj₄)
... | proj₆ , proj₇ , proj₈ with uniqueness-times (proj₃ , proj₇)
associativity-times {S n₁} (T-Succ t₁ p₁ , t₂)
    | proj₁ , proj₂ , proj₃ , proj₄ , proj₅
    | .proj₁ , proj₇ , proj₈
    | refl = proj₁ , proj₃ , T-Succ proj₈ proj₅
