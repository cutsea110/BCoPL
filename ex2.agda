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

count-of-cut-stampsheetSn≡n : (n : ℕ) → (s : StampSheet (S n)) → count-of-cut s ≡ n
count-of-cut-stampsheetSn≡n Z tip = refl
count-of-cut-stampsheetSn≡n (S n) (cut {j} {k} .{n} p sj sk) = cong S (help j k n p sj sk)
  where
    help : ∀ j k n →
       j + k ≡ n →
       (sj : StampSheet (S j)) (sk : StampSheet (S k)) →
       count-of-cut sj + count-of-cut sk ≡ n
    help j k n p sj sk rewrite count-of-cut-stampsheetSn≡n j sj | count-of-cut-stampsheetSn≡n k sk = p

x+y≡k→x≤k : ∀ {x y k} → x + y ≡ k → x ≤ k
x+y≡k→x≤k p with sym p
x+y≡k→x≤k {x} {y} p | refl = m≤m+n x y

x+y≡k→y≤k : ∀ {x y k} → x + y ≡ k → y ≤ k
x+y≡k→y≤k {x} {y} {k} p rewrite +-comm x y = x+y≡k→x≤k p

to-from-identity : ∀ j n → (j≤n : j ≤ n) → toℕ (inject≤ (fromℕ j) (s≤s j≤n)) ≡ j
to-from-identity Z k p = refl
to-from-identity (S j) Z ()
to-from-identity (S j) (S k) (s≤s p) = cong S (to-from-identity j k p)

convert : (j n : ℕ) → (j≤n : j ≤ n) → (s : StampSheet (S j)) → ∃ λ (j′ : Fin (S n)) → j ≡ toℕ j′
convert j n j≤n s = inject≤ (fromℕ j) (s≤s j≤n) , sym (to-from-identity j n j≤n)

count-of-cut-stampsheetSn≡n′ : (n : ℕ) → (s : StampSheet (S n)) → count-of-cut s ≡ n
count-of-cut-stampsheetSn≡n′ = cov-inductionℕ help
  where
    help₂ : {n : ℕ} →
        ((j′ : Fin (S n)) → (s : StampSheet (S (toℕ j′))) → count-of-cut s ≡ toℕ j′) →
        ∀ j k → j + k ≡ n →
        (sj : StampSheet (S j)) (sk : StampSheet (S k)) →
        count-of-cut sj + count-of-cut sk ≡ n
    help₂ {n} prf j k p sj sk with x+y≡k→x≤k {j} {k} {n} p
    ... | j≤n with inject≤ (fromℕ j) (s≤s j≤n)
    ... | j′ with convert j n j≤n sj
    help₂ {n} prf .(toℕ j″) k p sj sk | j≤n | j′ | j″ , refl with x+y≡k→y≤k {toℕ j″} {k} {n} p
    ... | k≤n with inject≤ (fromℕ k) (s≤s k≤n)
    ... | k′ with convert k n k≤n sk
    help₂ prf .(toℕ j″) .(toℕ k″) p sj sk | j≤n | j′ | j″ , refl | k≤n | k′ | k″ , refl rewrite prf j″ sj | prf k″ sk = p
    help : (k : ℕ) → ((j : Fin k) (s : StampSheet (S (toℕ j))) → count-of-cut s ≡ toℕ j) →
       (s : StampSheet (S k)) → count-of-cut s ≡ k
    help Z prf tip = refl
    help (S n) prf (cut {j} {k} .{n} p sj sk) = cong S (help₂ {n} prf j k p sj sk)


-- definition 2.34
plus : ℕ × ℕ → ℕ
plus (Z , y) = y
plus (S x , y) = S (plus (x , y))

-- definition 2.35
open import Data.Nat renaming (_⊔_ to max)
open import BCoPL.EvalNatExp

size : Exp → ℕ
size (Nat Z) = 1
size (Nat (S n)) = 1 + size (Nat n)
size (e₁ ⊕ e₂) = size e₁ + size e₂
size (e₁ ⊛ e₂) = size e₁ + size e₂

height : Exp → ℕ
height (Nat Z) = 1
height (Nat (S n)) = 1 + height (Nat n)
height (e₁ ⊕ e₂) = 1 + max (height e₁) (height e₂)
height (e₁ ⊛ e₂) = 1 + max (height e₁) (height e₂)

-- exercise 2.5
uniqueness-plus : ∀ {n₁ n₂ n₃ n₄} → plus (n₁ , n₂) ≡ n₃ × plus (n₁ , n₂) ≡ n₄ → n₃ ≡ n₄
uniqueness-plus (refl , refl) = refl

closure-plus : (n₁ n₂ : ℕ) → ∃ λ n₃ → plus (n₁ , n₂) ≡ n₃
closure-plus Z n₂ = n₂ , refl
closure-plus (S n₁) n₂ = S (plus (n₁ , n₂)) , refl

-- excercise 2.6
open import Data.Nat.Properties using (≤-steps; m≤m⊔n)
open import Relation.Binary
open DecTotalOrder decTotalOrder using () renaming (trans to ≤-trans; refl to ≤-refl)
open import Relation.Binary.PreorderReasoning using (begin_; _∎; _≈⟨_⟩_; _∼⟨_⟩_)

open import BCoPL.Induction using (induction-Exp)

_^_ : ℕ → ℕ → ℕ
Z ^ Z = 1
Z ^ n = Z
x ^ Z = 1
x ^ S y = x * (x ^ y)

size≥1 : ∀ e → 1 ≤ size e
size≥1 = induction-Exp help-nat help-plus help-times
  where
    help-nat : ∀ n → 1 ≤ size (Nat n)
    help-nat Z = s≤s z≤n
    help-nat (S n) = s≤s z≤n
    help-plus : ∀ e₁ e₂ → (1 ≤ size e₁) × (1 ≤ size e₂) → 1 ≤ size e₁ + size e₂
    help-plus e₁ e₂ (1≤size₁ , 1≤size₂) = ≤-steps (size e₁) 1≤size₂
    help-times : ∀ e₁ e₂ → (1 ≤ size e₁) × (1 ≤ size e₂) → 1 ≤ size e₁ + size e₂
    help-times e₁ e₂ (1≤size₁ , 1≤size₂) = ≤-steps (size e₁) 1≤size₂

height≥1 : ∀ e → 1 ≤ height e
height≥1 = induction-Exp help-nat help-plus help-times
  where
    help-nat : ∀ n → 1 ≤ height (Nat n)
    help-nat Z = s≤s z≤n
    help-nat (S n) = m≤m+n (S Z) (height (Nat n))
    help-plus : ∀ e₁ e₂ → (1 ≤ height e₁) × (1 ≤ height e₂) → 1 ≤ 1 + max (height e₁) (height e₂)
    help-plus e₁ e₂ prf = m≤m+n (S Z) (max (height e₁) (height e₂))
    help-times : ∀ e₁ e₂ → (1 ≤ height e₁) × (1 ≤ height e₂) → 1 ≤ 1 + max (height e₁) (height e₂)
    help-times e₁ e₂ prf = m≤m+n (S Z) (max (height e₁) (height e₂))

a≤b→c≤d→a+c≤b+d : ∀ {a b c d} → a ≤ b → c ≤ d → a + c ≤ b + d
a≤b→c≤d→a+c≤b+d {b = b} z≤n c≤d = ≤-steps b c≤d
a≤b→c≤d→a+c≤b+d (s≤s a≤b) c≤d = s≤s (a≤b→c≤d→a+c≤b+d a≤b c≤d)

Sx≤x+1 : ∀ x → S x ≤ x + 1
Sx≤x+1 Z = s≤s z≤n
Sx≤x+1 (S x) = s≤s (Sx≤x+1 x)

1≤2^heightN : ∀ n → 1 ≤ 2 ^ height (Nat n)
1≤2^heightN Z = s≤s z≤n
1≤2^heightN (S n) = ≤-trans (1≤2^heightN n) (m≤m+n (S (S Z) ^ height (Nat n)) (S (S Z) ^ height (Nat n) + Z))

1≤2^heightN+0 : ∀ n → 1 ≤ 2 ^ height (Nat n) + 0
1≤2^heightN+0 n = a≤b→c≤d→a+c≤b+d (1≤2^heightN n) z≤n

n≤n+m : ∀ n m → n ≤ n + m
n≤n+m Z m = z≤n
n≤n+m (S n) m = s≤s (n≤n+m n m)

1≤2^n : ∀ n → 1 ≤ 2 ^ n
1≤2^n Z = s≤s z≤n
1≤2^n (S n) = a≤b→c≤d→a+c≤b+d (1≤2^n n) z≤n

n≤m→2ⁿ≤2ᵐ : (n m : ℕ) → n ≤ m → 2 ^ n ≤ 2 ^ m
n≤m→2ⁿ≤2ᵐ Z Z z≤n = s≤s z≤n
n≤m→2ⁿ≤2ᵐ Z (S m) z≤n = a≤b→c≤d→a+c≤b+d (1≤2^n m) z≤n
n≤m→2ⁿ≤2ᵐ (S n) Z ()
n≤m→2ⁿ≤2ᵐ (S n) (S m) (s≤s p) = a≤b→c≤d→a+c≤b+d (n≤m→2ⁿ≤2ᵐ n m p) (a≤b→c≤d→a+c≤b+d (n≤m→2ⁿ≤2ᵐ n m p) z≤n)

m≤n⊔m : ∀ m n → m ≤ n ⊔ m
m≤n⊔m Z n = z≤n
m≤n⊔m (S m) Z = s≤s (m≤n⊔m m Z)
m≤n⊔m (S m) (S n) = s≤s (m≤n⊔m m n)

ex-2-6 : (e : Exp) → (size e) + 1 ≤ 2 ^ height e
ex-2-6 = induction-Exp help-nat help help
  where
    help-nat₂ : ∀ n → size (Nat n) + 1 ≤ 2 ^ height (Nat n) →
              S (size (Nat n) + 1) ≤ 2 ^ height (Nat n) + (2 ^ height (Nat n) + 0)
    help-nat₂ n prf = ≤-trans (Sx≤x+1 (size (Nat n) + 1)) (a≤b→c≤d→a+c≤b+d prf (1≤2^heightN+0 n))
    help-nat : ∀ n → size (Nat n) + 1 ≤ 2 ^ height (Nat n)
    help-nat = inductionℕ ((s≤s (s≤s z≤n)) , help-nat₂)
    help : ∀ e₁ e₂ → (size e₁ + 1 ≤ 2 ^ height e₁) × (size e₂ + 1 ≤ 2 ^ height e₂) →
            size e₁ + size e₂ + 1 ≤ 2 ^ (height e₁ ⊔ height e₂) + (2 ^ (height e₁ ⊔ height e₂) + 0)
    help e₁ e₂ (p₁ , p₂) = 
      ≤-trans ([a+b]+c≤a+[b+c] (size e₁) (size e₂) 1)
      (≤-trans (a+b≤a+1+b (size e₁) (size e₂ + 1))
      (≤-trans (a≤b→c≤d→a+c≤b+d p₁ p₂)
               (a≤b→c≤d→a+c≤b+d
                 (2^x≤2^x⊔y (height e₁) (height e₂))
                 (≤-trans (2^y≤2^x⊔y (height e₁) (height e₂)) (n≤n+m (S (S Z) ^ (height e₁ ⊔ height e₂)) 0)))))
      where
        [a+b]+c≤a+[b+c] : ∀ a b c → (a + b) + c ≤ a + (b + c)
        [a+b]+c≤a+[b+c] Z b c = ≤-refl
        [a+b]+c≤a+[b+c] (S a) b c = s≤s ([a+b]+c≤a+[b+c] a b c)
        a+b≤a+1+b : ∀ a b → a + b ≤ a + 1 + b
        a+b≤a+1+b Z b = ≤-steps (S Z) ≤-refl
        a+b≤a+1+b (S a) b = s≤s (a+b≤a+1+b a b)
        2^x≤2^x⊔y : ∀ x y → 2 ^ x ≤ 2 ^ (x ⊔ y)
        2^x≤2^x⊔y x y = n≤m→2ⁿ≤2ᵐ x (x ⊔ y) (m≤m⊔n x y)
        2^y≤2^x⊔y : ∀ x y → 2 ^ y ≤ 2 ^ (x ⊔ y)
        2^y≤2^x⊔y x y = n≤m→2ⁿ≤2ᵐ y (x ⊔ y) (m≤n⊔m y x)
