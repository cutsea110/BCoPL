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

-- theorem 2.11 (1)
open import BCoPL.CompareNat1 renaming (_is-less-than_ to _is-less-than1_)

Z-smallest1 : (n : ℕ) → Z is-less-than1 S n
Z-smallest1 Z = L-Succ
Z-smallest1 (S n) = L-Trans (Z-smallest1 n) L-Succ

-- theorem 2.11 (2)
open import BCoPL.CompareNat2 renaming (_is-less-than_ to _is-less-than2_)

Z-smallest2 : (n : ℕ) → Z is-less-than2 S n
Z-smallest2 n = L-Zero

-- theorem 2.11 (3)
open import BCoPL.CompareNat3 renaming (_is-less-than_ to _is-less-than3_)

Z-smallest3 : (n : ℕ) → Z is-less-than3 S n
Z-smallest3 Z = L-Succ
Z-smallest3 (S n) = L-SuccR (Z-smallest3 n)

-- theorem 2.12 (1)
n₁<n₂→Sn₁<Sn₂ : ∀ {n₁ n₂} → n₁ is-less-than1 n₂ → S n₁ is-less-than1 S n₂
n₁<n₂→Sn₁<Sn₂ L-Succ = L-Succ
n₁<n₂→Sn₁<Sn₂ (L-Trans p p₁) = L-Trans (n₁<n₂→Sn₁<Sn₂ p) (n₁<n₂→Sn₁<Sn₂ p₁)

n₁<n₂→n₂<n₃→Sn₁<n₃ : ∀ {n₁ n₂ n₃} → n₁ is-less-than1 n₂ → n₂ is-less-than1 n₃ → S n₁ is-less-than1 n₃
n₁<n₂→n₂<n₃→Sn₁<n₃ L-Succ p₂ = p₂
n₁<n₂→n₂<n₃→Sn₁<n₃ (L-Trans p₁ p₂) p₃ with n₁<n₂→Sn₁<Sn₂ p₁ | n₁<n₂→n₂<n₃→Sn₁<n₃ p₂ p₃
... | prf₁ | prf₂ = L-Trans prf₁ prf₂

n₁<n₂→n₂<Sn₃→n₁<n₃ : ∀ {n₁ n₂ n₃} → n₁ is-less-than1 n₂ → n₂ is-less-than1 S n₃ → n₁ is-less-than1 n₃
n₁<n₂→n₂<Sn₃→n₁<n₃ L-Succ L-Succ = L-Succ
n₁<n₂→n₂<Sn₃→n₁<n₃ L-Succ (L-Trans p₂ p₃) = L-Trans L-Succ (n₁<n₂→n₂<Sn₃→n₁<n₃ p₂ p₃)
n₁<n₂→n₂<Sn₃→n₁<n₃ (L-Trans p₁ p₂) p₃ = L-Trans p₁ (n₁<n₂→n₂<Sn₃→n₁<n₃ p₂ p₃)

S-keeps-order1 : ∀ {n₁ n₂} → S n₁ is-less-than1 S n₂ → n₁ is-less-than1 n₂
S-keeps-order1 L-Succ = L-Succ
S-keeps-order1 (L-Trans p₁ p₂) with n₁<n₂→n₂<n₃→Sn₁<n₃ p₁ p₂
S-keeps-order1 (L-Trans p₁ p₂) | L-Succ = L-Trans L-Succ L-Succ
S-keeps-order1 (L-Trans p₁ p₂) | L-Trans prf₁ prf₂ with n₁<n₂→n₂<Sn₃→n₁<n₃ prf₁ prf₂
... | prf = L-Trans L-Succ (L-Trans L-Succ prf)

-- theorem 2.12 (2)
S-keeps-order2 : ∀ {n₁ n₂} → S n₁ is-less-than2 S n₂ → n₁ is-less-than2 n₂
S-keeps-order2 (L-SuccSucc p) = p

-- theorem 2.12 (3)
S-keeps-order3 : ∀ {n₁ n₂} → S n₁ is-less-than3 S n₂ → n₁ is-less-than3 n₂
S-keeps-order3 {n₂ = Z} (L-SuccR ())
S-keeps-order3 {Z} {S n₂} p = Z-smallest3 n₂
S-keeps-order3 {S n₁} {S .(S n₁)} L-Succ = L-Succ
S-keeps-order3 {S n₁} {S n₂} (L-SuccR p) = L-SuccR (S-keeps-order3 p)

-- theorem 2.13 (1)
transitivity-less-than1 : ∀ {n₁ n₂ n₃} → n₁ is-less-than1 n₂ → n₂ is-less-than1 n₃ → n₁ is-less-than1 n₃
transitivity-less-than1 p₁ p₂ = L-Trans p₁ p₂

-- theorem 2.13 (2)
transitivity-less-than2 : ∀ {n₁ n₂ n₃} → n₁ is-less-than2 n₂ → n₂ is-less-than2 n₃ → n₁ is-less-than2 n₃
transitivity-less-than2 L-Zero (L-SuccSucc p₂) = L-Zero
transitivity-less-than2 (L-SuccSucc p₁) (L-SuccSucc p₂)
  = L-SuccSucc (transitivity-less-than2 p₁ p₂)

-- theorem 2.13 (3)
transitivity-less-than3 : ∀ {n₁ n₂ n₃} → n₁ is-less-than3 n₂ → n₂ is-less-than3 n₃ → n₁ is-less-than3 n₃
transitivity-less-than3 L-Succ L-Succ = L-SuccR L-Succ
transitivity-less-than3 {n₁} {S .n₁} L-Succ (L-SuccR p₂) = L-SuccR (transitivity-less-than3 L-Succ p₂)
transitivity-less-than3 {n₂ = S n₂} (L-SuccR p₁) L-Succ = L-SuccR (L-SuccR p₁)
transitivity-less-than3 {n₂ = S n₂} (L-SuccR p₁) (L-SuccR p₂)
  = L-SuccR (transitivity-less-than3 (L-SuccR p₁) p₂)

-- theorem 2.14
equality-comparenat-1→2 : ∀ {n₁ n₂} → n₁ is-less-than1 n₂ → n₁ is-less-than2 n₂
equality-comparenat-1→2 {Z} {S .0} L-Succ = L-Zero
equality-comparenat-1→2 {S n₁} {S .(S n₁)} L-Succ = L-SuccSucc (equality-comparenat-1→2 L-Succ)
equality-comparenat-1→2 (L-Trans p₁ p₂) with equality-comparenat-1→2 p₁ | equality-comparenat-1→2 p₂
... | prf₁ | prf₂ = help prf₁ prf₂
  where
    help : ∀ {n₁ n₂ n₃} → n₁ is-less-than2 n₃ → n₃ is-less-than2 n₂ → n₁ is-less-than2 n₂
    help L-Zero (L-SuccSucc p₃) = L-Zero
    help (L-SuccSucc p₃) (L-SuccSucc p₄) = L-SuccSucc (help p₃ p₄)

equality-comparenat-2→1 : ∀ {n₁ n₂} → n₁ is-less-than2 n₂ → n₁ is-less-than1 n₂
equality-comparenat-2→1 {n₂ = S n₂} L-Zero = Z-smallest1 n₂
equality-comparenat-2→1 (L-SuccSucc p) with equality-comparenat-2→1 p
... | prf = help prf
  where
    help : ∀ {n₁ n₂} → n₁ is-less-than1 n₂ → S n₁ is-less-than1 S n₂
    help L-Succ = L-Succ
    help (L-Trans p₁ p₂) = L-Trans (help p₁) (help p₂)

equality-comparenat-2→3 : ∀ {n₁ n₂} → n₁ is-less-than2 n₂ → n₁ is-less-than3 n₂
equality-comparenat-2→3 {n₂ = S n₂} L-Zero = Z-smallest3 n₂
equality-comparenat-2→3 (L-SuccSucc p) with equality-comparenat-2→3 p
... | prf = help prf
  where
    help : ∀ {n₁ n₂} → n₁ is-less-than3 n₂ → S n₁ is-less-than3 S n₂
    help L-Succ = L-Succ
    help (L-SuccR p₁) = L-SuccR (help p₁)

equality-comparenat-3→2 : ∀ {n₁ n₂} → n₁ is-less-than3 n₂ → n₁ is-less-than2 n₂
equality-comparenat-3→2 {Z} {S .0} L-Succ = L-Zero
equality-comparenat-3→2 {S n₁} {S .(S n₁)} L-Succ = L-SuccSucc (equality-comparenat-3→2 L-Succ)
equality-comparenat-3→2 (L-SuccR p) with equality-comparenat-3→2 p
... | prf = help prf
  where
    help : ∀ {n₁ n₂} → n₁ is-less-than2 n₂ → n₁ is-less-than2 S n₂
    help L-Zero = L-Zero
    help (L-SuccSucc p₁) = L-SuccSucc (help p₁)

equality-comparenat-3→1 : ∀ {n₁ n₂} → n₁ is-less-than3 n₂ → n₁ is-less-than1 n₂
equality-comparenat-3→1 L-Succ = L-Succ
equality-comparenat-3→1 (L-SuccR p) with equality-comparenat-3→1 p
... | prf = L-Trans prf L-Succ

equality-comparenat-1→3 : ∀ {n₁ n₂} → n₁ is-less-than1 n₂ → n₁ is-less-than3 n₂
equality-comparenat-1→3 L-Succ = L-Succ
equality-comparenat-1→3 (L-Trans p₁ p₂) with equality-comparenat-1→3 p₁ | equality-comparenat-1→3 p₂
... | prf₁ | prf₂ = help prf₁ prf₂
  where
    help : ∀ {n₁ n₂ n₃} → n₁ is-less-than3 n₃ → n₃ is-less-than3 n₂ → n₁ is-less-than3 n₂
    help L-Succ L-Succ = L-SuccR L-Succ
    help L-Succ (L-SuccR p₃) = L-SuccR (help L-Succ p₃)
    help (L-SuccR p₃) L-Succ = L-SuccR (L-SuccR p₃)
    help (L-SuccR p₃) (L-SuccR p₄) = L-SuccR (help (L-SuccR p₃) p₄)

-- theorem 2.15
open import BCoPL.EvalNatExp

eval-plus : ∀ n₁ n₂ → n₁ plus n₂ is (n₁ + n₂)
eval-plus Z n₂ = P-Zero
eval-plus (S n₁) n₂ = P-Succ (eval-plus n₁ n₂)

eval-times : ∀ n₁ n₂ → n₁ times n₂ is (n₁ * n₂)
eval-times Z n₂ = T-Zero
eval-times (S n₁) n₂ = T-Succ (eval-times n₁ n₂) (eval-plus n₂ (n₁ * n₂))

totality-⇓ : (e : Exp) → ∃ λ n → e ⇓ n
totality-⇓ (Nat n) = n , E-Const
totality-⇓ (e₁ ⊕ e₂) with totality-⇓ e₁ | totality-⇓ e₂
totality-⇓ (e₁ ⊕ e₂) | v₁ , prf₁ | v₂ , prf₂ = v₁ + v₂ , E-Plus prf₁ prf₂ (eval-plus v₁ v₂)
totality-⇓ (e₁ ⊛ e₂) with totality-⇓ e₁ | totality-⇓ e₂
totality-⇓ (e₁ ⊛ e₂) | v₁ , prf₁ | v₂ , prf₂ = (v₁ * v₂) , E-Times prf₁ prf₂ (eval-times v₁ v₂)

-- theorem 2.16
uniqueness-⇓ : ∀ {n₁ n₂ e} → e ⇓ n₁ × e ⇓ n₂ → n₁ ≡ n₂
uniqueness-⇓ (E-Const , E-Const) = refl
uniqueness-⇓ (E-Plus s₁ s₂ p₁ , E-Plus s₃ s₄ p₂)
  rewrite uniqueness-⇓ (s₁ , s₃) | uniqueness-⇓ (s₂ , s₄) | uniqueness-plus (p₁ , p₂) = refl
uniqueness-⇓ (E-Times s₁ s₂ t₁ , E-Times s₃ s₄ t₂)
  rewrite uniqueness-⇓ (s₁ , s₃) | uniqueness-⇓ (s₂ , s₄) | uniqueness-times (t₁ , t₂) = refl

-- theorem 2.17
commutativity-⊕ : ∀ {e₁ e₂ n} → e₁ ⊕ e₂ ⇓ n → e₂ ⊕ e₁ ⇓ n
commutativity-⊕ (E-Plus s₁ s₂ p) with commutativity-plus p
... | prf = E-Plus s₂ s₁ prf

-- theorem 2.18
associativity-⊕ : ∀ {e₁ e₂ e₃ n} → (e₁ ⊕ e₂) ⊕ e₃ ⇓ n → e₁ ⊕ (e₂ ⊕ e₃) ⇓ n
associativity-⊕ (E-Plus (E-Plus s₁ s₂ p₁) s₃ p₂) with associativity-plus (p₁ , p₂)
associativity-⊕ (E-Plus (E-Plus s₁ s₂ p₁) s₃ p₂) | proj₁ , proj₂ , proj₃
  = E-Plus s₁ (E-Plus s₂ s₃ proj₂) proj₃

-- theorem 2.19
commutativity-⊛ : ∀ {e₁ e₂ n} → e₁ ⊛ e₂ ⇓ n → e₂ ⊛ e₁ ⇓ n
commutativity-⊛ (E-Times s₁ s₂ t) with commutativity-times t
... | prf = E-Times s₂ s₁ prf

-- theorem 2.20
associativity-⊛ : ∀ {e₁ e₂ e₃ n} → (e₁ ⊛ e₂) ⊛ e₃ ⇓ n → e₁ ⊛ (e₂ ⊛ e₃) ⇓ n
associativity-⊛ (E-Times (E-Times s₁ s₂ t₁) s₃ t₂) with associativity-times (t₁ , t₂)
associativity-⊛ (E-Times (E-Times s₁ s₂ t₁) s₃ t₂) | proj₁ , proj₂ , proj₃
  = E-Times s₁ (E-Times s₂ s₃ proj₂) proj₃

-- theorem 2.21
open import BCoPL.ReduceNatExp
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary.Core using (¬_)

notPeano : (e : Exp) → Set
notPeano (Nat n) = ⊥
notPeano (e₁ ⊕ e₂) = ⊤
notPeano (e₁ ⊛ e₂) = ⊤

reduceability-⟶ : (e : Exp) → notPeano e → ∃ λ e′ → e ⟶ e′
reduceability-⟶ (Nat n) ()
reduceability-⟶ (Nat n₁ ⊕ Nat n₂) tt = Nat (n₁ + n₂) , R-Plus (eval-plus n₁ n₂)
reduceability-⟶ (Nat n₁ ⊕ (e₂ ⊕ e₃)) tt with reduceability-⟶ (e₂ ⊕ e₃) tt
... | proj₁ , proj₂ = (Nat n₁ ⊕ proj₁) , R-PlusR proj₂
reduceability-⟶ (Nat n₁ ⊕ (e₂ ⊛ e₃)) tt with reduceability-⟶ (e₂ ⊛ e₃) tt
... | proj₁ , proj₂ = (Nat n₁ ⊕ proj₁) , R-PlusR proj₂
reduceability-⟶ ((e₁ ⊕ e₂) ⊕ e₃) tt with reduceability-⟶ (e₁ ⊕ e₂) tt
... | proj₁ , proj₂ = (proj₁ ⊕ e₃) , R-PlusL proj₂
reduceability-⟶ ((e₁ ⊛ e₂) ⊕ e₃) tt with reduceability-⟶ (e₁ ⊛ e₂) tt
... | proj₁ , proj₂ = (proj₁ ⊕ e₃) , R-PlusL proj₂
reduceability-⟶ (Nat n₁ ⊛ Nat n₂) tt = (Nat (n₁ * n₂)) , (R-Times (eval-times n₁ n₂))
reduceability-⟶ (Nat n₁ ⊛ (e₂ ⊕ e₃)) tt with reduceability-⟶ (e₂ ⊕ e₃) tt
... | proj₁ , proj₂ = Nat n₁ ⊛ proj₁ , R-TimesR proj₂
reduceability-⟶ (Nat n₁ ⊛ (e₂ ⊛ e₃)) tt with reduceability-⟶ (e₂ ⊛ e₃) tt
... | proj₁ , proj₂ = Nat n₁ ⊛ proj₁ , R-TimesR proj₂
reduceability-⟶ ((e₁ ⊕ e₂) ⊛ e₃) tt with reduceability-⟶ (e₁ ⊕ e₂) tt
... | proj₁ , proj₂ = proj₁ ⊛ e₃ , R-TimesL proj₂
reduceability-⟶ ((e₁ ⊛ e₂) ⊛ e₃) tt with reduceability-⟶ (e₁ ⊛ e₂) tt
... | proj₁ , proj₂ = proj₁ ⊛ e₃ , R-TimesL proj₂

-- theorem 2.22
reduce-same-exp : ∀ {e₁ e₂ e₃} → e₁ ⟶ e₂ × e₁ ⟶ e₃ → ∃ λ e₄ → e₂ ⟶ e₄ × e₃ ⟶ e₄
reduce-same-exp {Nat n} (() , x₂)
reduce-same-exp {._ ⊕ ._} {Nat n₁} {Nat n₂} (R-Plus x₁ , R-Plus x₂) = {!!}
reduce-same-exp {._ ⊕ ._} {Nat n₁} {e₃ ⊕ ._} (R-Plus x₁ , R-PlusL ())
reduce-same-exp {._ ⊕ ._} {Nat n₁} {._ ⊕ e₄} (R-Plus x₁ , R-PlusR ())
reduce-same-exp {._ ⊕ ._} {Nat n₁} {e₃ ⊛ e₄} (R-Plus x₁ , ())
reduce-same-exp {._ ⊕ ._} {e₃ ⊕ ._} {Nat n₂} (R-PlusL () , R-Plus x₂)
reduce-same-exp {._ ⊕ ._} {._ ⊕ e₄} {Nat n₂} (R-PlusR () , R-Plus x₂)
reduce-same-exp {e₁ ⊕ e₂} {e₃ ⊕ .e₂} {e₅ ⊕ .e₂} (R-PlusL x₁ , R-PlusL x₂) with reduce-same-exp (x₁ , x₂)
... | proj₁ , proj₂ , proj₃ = (proj₁ ⊕ e₂) , R-PlusL proj₂ , R-PlusL proj₃
reduce-same-exp {e₁ ⊕ e₂} {e₃ ⊕ .e₂} {.e₁ ⊕ e₆} (R-PlusL x₁ , R-PlusR x₂)
  = (e₃ ⊕ e₆) , R-PlusR x₂ , R-PlusL x₁
reduce-same-exp {e₁ ⊕ e₂} {.e₁ ⊕ e₄} {e₅ ⊕ .e₂} (R-PlusR x₁ , R-PlusL x₂)
  = (e₅ ⊕ e₄) , R-PlusL x₂ , R-PlusR x₁
reduce-same-exp {e₁ ⊕ e₂} {.e₁ ⊕ e₄} {.e₁ ⊕ e₆} (R-PlusR x₁ , R-PlusR x₂) with reduce-same-exp (x₁ , x₂)
... | proj₁ , proj₂ , proj₃ = (e₁ ⊕ proj₁) , R-PlusR proj₂ , R-PlusR proj₃
reduce-same-exp {e₁ ⊕ e₂} {e₃ ⊕ e₄} {e₅ ⊛ e₆} (x₁ , ())
reduce-same-exp {e₁ ⊕ e₂} {e₃ ⊛ e₄} (() , x₂)
reduce-same-exp {._ ⊛ ._} {Nat n₁} {Nat n₂} (R-Times x₁ , R-Times x₂) = {!!}
reduce-same-exp {e₁ ⊛ e₂} {Nat n₁} {e₃ ⊕ e₄} (x₁ , ())
reduce-same-exp {._ ⊛ ._} {Nat n₁} {e₃ ⊛ ._} (R-Times x₁ , R-TimesL ())
reduce-same-exp {._ ⊛ ._} {Nat n₁} {._ ⊛ e₄} (R-Times x₁ , R-TimesR ())
reduce-same-exp {e₁ ⊛ e₂} {e₃ ⊕ e₄} (() , x₂)
reduce-same-exp {._ ⊛ ._} {e₃ ⊛ ._} {Nat n₂} (R-TimesL () , R-Times x₂)
reduce-same-exp {._ ⊛ ._} {._ ⊛ e₄} {Nat n₂} (R-TimesR () , R-Times x₂)
reduce-same-exp {e₁ ⊛ e₂} {e₃ ⊛ e₄} {e₅ ⊕ e₆} (x₁ , ())
reduce-same-exp {e₁ ⊛ e₂} {e₃ ⊛ .e₂} {e₅ ⊛ .e₂} (R-TimesL x₁ , R-TimesL x₂) with reduce-same-exp (x₁ , x₂)
... | proj₁ , proj₂ , proj₃ = proj₁ ⊛ e₂ , R-TimesL proj₂ , R-TimesL proj₃
reduce-same-exp {e₁ ⊛ e₂} {e₃ ⊛ .e₂} {.e₁ ⊛ e₆} (R-TimesL x₁ , R-TimesR x₂)
  = (e₃ ⊛ e₆) , R-TimesR x₂ , R-TimesL x₁
reduce-same-exp {e₁ ⊛ e₂} {.e₁ ⊛ e₄} {e₅ ⊛ .e₂} (R-TimesR x₁ , R-TimesL x₂)
  = (e₅ ⊛ e₄) , R-TimesL x₂ , R-TimesR x₁
reduce-same-exp {e₁ ⊛ e₂} {.e₁ ⊛ e₄} {.e₁ ⊛ e₆} (R-TimesR x₁ , R-TimesR x₂) with reduce-same-exp (x₁ , x₂)
... | proj₁ , proj₂ , proj₃ = e₁ ⊛ proj₁ , R-TimesR proj₂ , R-TimesR proj₃

-- theorem 2.23
uniqueness--d-> : ∀ {e e′ e″} → e -d-> e′ × e -d-> e″ → e′ ≡ e″
uniqueness--d-> (DR-Plus x₁ , DR-Plus x₂) rewrite uniqueness-plus (x₁ , x₂) = refl
uniqueness--d-> (DR-Plus x₁ , DR-PlusL ())
uniqueness--d-> (DR-Plus x₁ , DR-PlusR ())
uniqueness--d-> (DR-Times x₁ , DR-Times x₂) rewrite uniqueness-times (x₁ , x₂) = refl
uniqueness--d-> (DR-Times x₁ , DR-TimesL ())
uniqueness--d-> (DR-Times x₁ , DR-TimesR ())
uniqueness--d-> (DR-PlusL () , DR-Plus x₂)
uniqueness--d-> (DR-PlusL x₁ , DR-PlusL x₂) rewrite uniqueness--d-> (x₁ , x₂) = refl
uniqueness--d-> (DR-PlusL () , DR-PlusR x₂)
uniqueness--d-> (DR-PlusR () , DR-Plus x₂)
uniqueness--d-> (DR-PlusR x₁ , DR-PlusL ())
uniqueness--d-> (DR-PlusR x₁ , DR-PlusR x₂) rewrite uniqueness--d-> (x₁ , x₂) = refl
uniqueness--d-> (DR-TimesL () , DR-Times x₂)
uniqueness--d-> (DR-TimesL x₁ , DR-TimesL x₂) rewrite uniqueness--d-> (x₁ , x₂) = refl
uniqueness--d-> (DR-TimesL () , DR-TimesR x₂)
uniqueness--d-> (DR-TimesR () , DR-Times x₂)
uniqueness--d-> (DR-TimesR x₁ , DR-TimesL ())
uniqueness--d-> (DR-TimesR x₁ , DR-TimesR x₂) rewrite uniqueness--d-> (x₁ , x₂) = refl

-- theorem 2.24
-d->→⟶ : ∀ {e e′} → e -d-> e′ → e ⟶ e′
-d->→⟶ (DR-Plus x) = R-Plus x
-d->→⟶ (DR-Times x) = R-Times x
-d->→⟶ (DR-PlusL p) with -d->→⟶ p
... | prf = R-PlusL prf
-d->→⟶ (DR-PlusR p) with -d->→⟶ p
... | prf = R-PlusR prf
-d->→⟶ (DR-TimesL p) with -d->→⟶ p
... | prf = R-TimesL prf
-d->→⟶ (DR-TimesR p) with -d->→⟶ p
... | prf = R-TimesR prf

-- theorem 2.25
weak-normalization : (e : Exp) → ∃ λ n → e -*-> n
weak-normalization (Nat n) = (Nat n) , MR-Zero
weak-normalization (e₁ ⊕ e₂) with weak-normalization e₁ | weak-normalization e₂
... | prf₁ | prf₂ = (e₁ ⊕ e₂) , MR-Zero
weak-normalization (e₁ ⊛ e₂) with weak-normalization e₁ | weak-normalization e₂
... | prf₁ | prf₂ = e₁ ⊛ e₂ , MR-Zero

-- theorem 2.27
left-reduction-⊕ : ∀ {e₁ e₁′ e₂} → e₁ -*-> e₁′ → e₁ ⊕ e₂ -*-> e₁′ ⊕ e₂
left-reduction-⊕ MR-Zero = MR-Zero
left-reduction-⊕ (MR-One x) = MR-One (R-PlusL x)
left-reduction-⊕ (MR-Multi x x₁) = MR-Multi (left-reduction-⊕ x) (left-reduction-⊕ x₁)

right-reduction-⊕ : ∀ {e₁ e₂ e₂′} → e₂ -*-> e₂′ → e₁ ⊕ e₂ -*-> e₁ ⊕ e₂′
right-reduction-⊕ MR-Zero = MR-Zero
right-reduction-⊕ (MR-One x) = MR-One (R-PlusR x)
right-reduction-⊕ (MR-Multi p p₁) = MR-Multi (right-reduction-⊕ p) (right-reduction-⊕ p₁)

both-reduction-⊕ : ∀ {e₁ e₂ n₁ n₂} → e₁ -*-> Nat n₁ → e₂ -*-> Nat n₂ → e₁ ⊕ e₂ -*-> Nat n₁ ⊕ Nat n₂
both-reduction-⊕ p q = MR-Multi (left-reduction-⊕ p) (right-reduction-⊕ q)

left-reduction-⊛ : ∀ {e₁ e₁′ e₂} → e₁ -*-> e₁′ → e₁ ⊛ e₂ -*-> e₁′ ⊛ e₂
left-reduction-⊛ MR-Zero = MR-Zero
left-reduction-⊛ (MR-One x) = MR-One (R-TimesL x)
left-reduction-⊛ (MR-Multi p p₁) = MR-Multi (left-reduction-⊛ p) (left-reduction-⊛ p₁)

right-reduction-⊛ : ∀ {e₁ e₂ e₂′} → e₂ -*-> e₂′ → e₁ ⊛ e₂ -*-> e₁ ⊛ e₂′
right-reduction-⊛ MR-Zero = MR-Zero
right-reduction-⊛ (MR-One x) = MR-One (R-TimesR x)
right-reduction-⊛ (MR-Multi p p₁) = MR-Multi (right-reduction-⊛ p) (right-reduction-⊛ p₁)

both-reduction-⊛ : ∀ {e₁ e₂ n₁ n₂} → e₁ -*-> Nat n₁ → e₂ -*-> Nat n₂ → e₁ ⊛ e₂ -*-> Nat n₁ ⊛ Nat n₂
both-reduction-⊛ p q = MR-Multi (left-reduction-⊛ p) (right-reduction-⊛ q)

⇓→-*-> : ∀ {e n} → e ⇓ n → e -*-> Nat n
⇓→-*-> E-Const = MR-Zero
⇓→-*-> (E-Plus e₁ e₂ p) with ⇓→-*-> e₁ | ⇓→-*-> e₂
... | MR-Zero | MR-Zero
  = MR-One (R-Plus p)
... | MR-Zero | MR-One x
  = MR-Multi (MR-One (R-PlusR x)) (MR-One (R-Plus p))
... | MR-Zero | MR-Multi prf₂ prf₃
  = MR-Multi (right-reduction-⊕ (MR-Multi prf₂ prf₃)) (MR-One (R-Plus p))
... | MR-One x | MR-Zero
  = MR-Multi (MR-One (R-PlusL x)) (MR-One (R-Plus p))
... | MR-One x | MR-One x₁
  = MR-Multi (MR-One (R-PlusL x)) (MR-Multi (MR-One (R-PlusR x₁)) (MR-One (R-Plus p)))
... | MR-One x | MR-Multi prf₂ prf₃
  = MR-Multi (both-reduction-⊕ (MR-One x) (MR-Multi prf₂ prf₃)) (MR-One (R-Plus p))
... | MR-Multi prf₁ prf₂ | MR-Zero
  = MR-Multi (left-reduction-⊕ (MR-Multi prf₁ prf₂)) (MR-One (R-Plus p))
... | MR-Multi prf₁ prf₂ | MR-One x
  = MR-Multi (both-reduction-⊕ (MR-Multi prf₁ prf₂) (MR-One x)) (MR-One (R-Plus p))
... | MR-Multi prf₁ prf₂ | MR-Multi prf₃ prf₄
  = MR-Multi (both-reduction-⊕ (MR-Multi prf₁ prf₂) (MR-Multi prf₃ prf₄)) (MR-One (R-Plus p))
⇓→-*-> (E-Times e₁ e₂ t) with ⇓→-*-> e₁ | ⇓→-*-> e₂
... | MR-Zero | MR-Zero
  = MR-One (R-Times t)
... | MR-Zero | MR-One x
  = MR-Multi (MR-One (R-TimesR x)) (MR-One (R-Times t))
... | MR-Zero | MR-Multi prf₂ prf₃
  = MR-Multi (right-reduction-⊛ (MR-Multi prf₂ prf₃)) (MR-One (R-Times t))
... | MR-One x | MR-Zero
  = MR-Multi (MR-One (R-TimesL x)) (MR-One (R-Times t))
... | MR-One x | MR-One x₁
  = MR-Multi (MR-Multi (MR-One (R-TimesL x)) (MR-One (R-TimesR x₁))) (MR-One (R-Times t))
... | MR-One x | MR-Multi prf₂ prf₃
  = MR-Multi (both-reduction-⊛ (MR-One x) (MR-Multi prf₂ prf₃)) (MR-One (R-Times t))
... | MR-Multi prf₁ prf₂ | MR-Zero
  = MR-Multi (left-reduction-⊛ (MR-Multi prf₁ prf₂)) (MR-One (R-Times t))
... | MR-Multi prf₁ prf₂ | MR-One x
  = MR-Multi (both-reduction-⊛ (MR-Multi prf₁ prf₂) (MR-One x)) (MR-One (R-Times t))
... | MR-Multi prf₁ prf₂ | MR-Multi prf₃ prf₄
  = MR-Multi (both-reduction-⊛ (MR-Multi prf₁ prf₂) (MR-Multi prf₃ prf₄)) (MR-One (R-Times t))

-- theorem 2.28
n-*->e→e≡n : ∀ {e n} → Nat n -*-> e → e ≡ Nat n
n-*->e→e≡n MR-Zero = refl
n-*->e→e≡n (MR-One ())
n-*->e→e≡n (MR-Multi p₁ p₂) rewrite n-*->e→e≡n p₁ | n-*->e→e≡n p₂ = refl

left-⇓-⊕ : ∀ {e₁ e₂ n₁ n} → e₁ ⇓ n₁ → e₁ ⊕ e₂ ⇓ n → Nat n₁ ⊕ e₂ ⇓ n
left-⇓-⊕ {e₁} {e₂} {n₁} {n} p (E-Plus q₁ q₂ x) rewrite uniqueness-⇓ (p , q₁) = E-Plus E-Const q₂ x

right-⇓-⊕ : ∀ {e₁ e₂ n₂ n} → e₂ ⇓ n₂ → e₁ ⊕ e₂ ⇓ n → e₁ ⊕ Nat n₂ ⇓ n
right-⇓-⊕ {e₁} {e₂} {n₂} {n} p (E-Plus q₁ q₂ x) rewrite uniqueness-⇓ (p , q₂) = E-Plus q₁ E-Const x

left-⇓-⊛ : ∀ {e₁ e₂ n₁ n} → e₁ ⇓ n₁ → e₁ ⊛ e₂ ⇓ n → Nat n₁ ⊛ e₂ ⇓ n
left-⇓-⊛ {e₁} {e₂} {n₁} {n} p (E-Times q₁ q₂ x) rewrite uniqueness-⇓ (p , q₁) = E-Times E-Const q₂ x

right-⇓-⊛ : ∀ {e₁ e₂ n₂ n} → e₂ ⇓ n₂ → e₁ ⊛ e₂ ⇓ n → e₁ ⊛ Nat n₂ ⇓ n
right-⇓-⊛ {e₁} {e₂} {n₂} {n} p (E-Times q₁ q₂ x) rewrite uniqueness-⇓ (p , q₂) = E-Times q₁ E-Const x

⇓-ability-⊕ : ∀ {e₁ e₂ n} → e₁ ⊕ e₂ ⇓ n → ∃ λ n₁ → ∃ λ n₂ → e₁ ⇓ n₁ × e₂ ⇓ n₂ × n₁ plus n₂ is n
⇓-ability-⊕ {e₁} {e₂} {n} (E-Plus p₁ p₂ x) with totality-⇓ e₁ | totality-⇓ e₂
... | n₁ , proj₂ | n₂ , proj₄ with uniqueness-⇓ (p₁ , proj₂) | uniqueness-⇓ (p₂ , proj₄)
... | refl | refl = n₁ , n₂ , p₁ , p₂ , x

⇓-ability-⊛ : ∀ {e₁ e₂ n} → e₁ ⊛ e₂ ⇓ n → ∃ λ n₁ → ∃ λ n₂ → e₁ ⇓ n₁ × e₂ ⇓ n₂ × n₁ times n₂ is n
⇓-ability-⊛ {e₁} {e₂} {n} (E-Times p₁ p₂ x) with totality-⇓ e₁ | totality-⇓ e₂
... | n₁ , proj₂ | n₂ , proj₄ with uniqueness-⇓ (p₁ , proj₂) | uniqueness-⇓ (p₂ , proj₄)
... | refl | refl = n₁ , n₂ , p₁ , p₂ , x

-*->→⇓ : ∀ {e n} → e -*-> Nat n → e ⇓ n
-*->→⇓ MR-Zero = E-Const
-*->→⇓ (MR-One (R-Plus x)) = E-Plus E-Const E-Const x
-*->→⇓ (MR-One (R-Times x)) = E-Times E-Const E-Const x
-*->→⇓ (MR-Multi p₁ p₂) = {!!}
{--
-*->→⇓ {Nat n} MR-Zero = E-Const
-*->→⇓ {Nat n} (MR-One ())
-*->→⇓ {Nat n} (MR-Multi p₁ p₂) with n-*->e→e≡n p₁
... | refl with n-*->e→e≡n p₂
... | refl = E-Const
-*->→⇓ {._ ⊕ ._} (MR-One (R-Plus x)) = E-Plus E-Const E-Const x
-*->→⇓ {e₁ ⊕ e₂} (MR-Multi p₁ p₂) = {!!}
-*->→⇓ {._ ⊛ ._} (MR-One (R-Times x)) = E-Times E-Const E-Const x
-*->→⇓ {e₁ ⊛ e₂} (MR-Multi p₁ p₂) = {!!}
--}
