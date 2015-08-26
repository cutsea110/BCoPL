module ex2 where

open import Data.Nat renaming (suc to S; zero to Z)
open import Data.Product hiding (Σ)
open import Relation.Binary.PropositionalEquality as PropEq

-- principal 2.29
open import BCoPL.Induction using (inductionℕ; cov-inductionℕ)
open import Data.Nat.Properties.Simple

-- ex-2-2-0
Σ : ℕ → ℕ
Σ Z = Z
Σ (S n) = S n + Σ n

data Parity : ℕ → Set where
  even : (k : ℕ) → Parity (k * 2)
  odd : (k : ℕ) → Parity (1 + k * 2)

parity : (n : ℕ) → Parity n
parity Z = even Z
parity (S n) with parity n
parity (S .(k * 2)) | even k = odd k
parity (S .(S (k * 2))) | odd k = even (S k)

_/2 : ℕ → ℕ
n /2 with parity n
.(k * 2) /2 | even k = k
.(S (k * 2)) /2 | odd k = k

S[n/2]≡SSn/2 : (n : ℕ) → S (n /2) ≡ S (S n) /2
S[n/2]≡SSn/2 = inductionℕ (refl , help)
  where
    help : (n : ℕ) → S (n /2) ≡ S (S n) /2 → S (S n /2) ≡ S (S (S n)) /2
    help n prf with parity n
    help .(k * 2) prf | even k = refl
    help .(S (k * 2)) prf | odd k = refl

x+y/2≡[x*2+y]/2 : (x y : ℕ) → x + y /2 ≡ (x * 2 + y) /2
x+y/2≡[x*2+y]/2 Z y = refl
x+y/2≡[x*2+y]/2 (S x) y rewrite x+y/2≡[x*2+y]/2 x y = S[n/2]≡SSn/2 (x * S (S Z) + y)

Σ≡n*Sn/2 : (n : ℕ) → Σ n ≡ (n * S n) /2
Σ≡n*Sn/2 = inductionℕ (refl , help)
  where
    x*y+x*z≡x*[y+z] : (x y z : ℕ) → x * y + x * z ≡ x * (y + z)
    x*y+x*z≡x*[y+z] x y z rewrite *-comm x y | *-comm x z | *-comm x (y + z) = sym (distribʳ-*-+ x y z)
    n*2+n*Sn≡n+n*SSn : (n : ℕ) → n * 2 + n * S n ≡ n + n * S (S n)
    n*2+n*Sn≡n+n*SSn n rewrite sym (+-*-suc n (S (S n))) | x*y+x*z≡x*[y+z] n 2 (S n) = refl
    [Sn+[n*Sn]/2]≡[SSn+n*SSn]/2 : (n : ℕ) → S n + ((n * S n) /2) ≡ S (S (n + n * S (S n))) /2
    [Sn+[n*Sn]/2]≡[SSn+n*SSn]/2 n rewrite x+y/2≡[x*2+y]/2 (S n) (n * S n)
      = cong (λ x → S (S x) /2) (n*2+n*Sn≡n+n*SSn n)
    help : (n : ℕ) → Σ n ≡ (n * S n) /2 → S (n + Σ n) ≡ S (S (n + n * S (S n))) /2
    help n prf rewrite prf = [Sn+[n*Sn]/2]≡[SSn+n*SSn]/2 n

-- ex-2-31
open import Data.Fin hiding (_+_; _≤_)
open import Data.Fin.Properties using (inject≤-lemma; to-from; toℕ-injective)
open import Data.Nat using (z≤n; s≤s)
open import Data.Nat.Properties using (m≤m+n)

data StampSheet : ℕ → Set where
  tip : StampSheet 1
  cut : {j k n : ℕ} → (p : j + k ≡ n) → StampSheet (S j) → StampSheet (S k) → StampSheet (S (S n))

count-of-cut : {n : ℕ} → StampSheet n → ℕ
count-of-cut tip = Z
count-of-cut (cut p sj sk) = 1 + count-of-cut sj + count-of-cut sk

x+y≡k→x≤k : ∀ {x y k} → x + y ≡ k → x ≤ k
x+y≡k→x≤k p with sym p
x+y≡k→x≤k {x} {y} p | refl = m≤m+n x y

count-of-cut-stampsheetSn≡n : (n : ℕ) → (s : StampSheet (S n)) → count-of-cut s ≡ n
count-of-cut-stampsheetSn≡n = cov-inductionℕ help
  where
    help₂ : {k : ℕ} →
        ((j : Fin (S k)) (s : StampSheet (S (toℕ j))) → count-of-cut s ≡ toℕ j) →
        ∀ x y → x + y ≡ k →
        (sj : StampSheet (S x)) (sk : StampSheet (S y)) →
        count-of-cut sj + count-of-cut sk ≡ k
    help₂ prf x y p sj sk with (fromℕ x) | (x+y≡k→x≤k (cong S p))
    ... | j′ | x≤k with inject≤ j′ x≤k | inject≤-lemma j′ x≤k
    ... | j″ | lemmaⱼ = {!!}
    help : (k : ℕ) → ((j : Fin k) (s : StampSheet (S (toℕ j))) → count-of-cut s ≡ toℕ j) →
       (s : StampSheet (S k)) → count-of-cut s ≡ k
    help Z prf tip = refl
    help (S k) prf (cut {x} {y} p sj sk) = cong S (help₂ prf x y p sj sk)

-- definition 2.34
plus : ℕ × ℕ → ℕ
plus (Z , y) = y
plus (S x , y) = S (plus (x , y))

-- definition 2.35
open import Data.Nat renaming (_⊔_ to max)
open import BCoPL.EvalNatExp

size : Exp → ℕ
size (Nat Z) = 1
size (Nat (S n)) = size (Nat n) + 1
size (e₁ ⊕ e₂) = size e₁ + size e₂
size (e₁ ⊛ e₂) = size e₁ + size e₂

height : Exp → ℕ
height (Nat Z) = 1
height (Nat (S n)) = height (Nat n) + 1
height (e₁ ⊕ e₂) = max (height e₁) (height e₂) + 1
height (e₁ ⊛ e₂) = max (height e₁) (height e₂) + 1

