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
