module BCoPL.CompareNat.Properties where

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

