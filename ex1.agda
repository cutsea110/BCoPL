module ex1 where

open import Data.Nat renaming (ℕ to ℕ; zero to Z; suc to S)

data _plus_is_ : ℕ → ℕ → ℕ → Set where
  P-Zero : ∀ {n} → Z plus n is n
  P-Succ : ∀ {n₁ n₂ n₃} → n₁ plus n₂ is n₃ → S n₁ plus n₂ is S n₃

data _times_is_ : ℕ → ℕ → ℕ → Set where
  T-Zero : ∀ {n} → Z times n is Z
  T-Succ : ∀ {n₁ n₂ n₃ n₄} → n₁ times n₂ is n₃ → n₂ plus n₃ is n₄ → S n₁ times n₂ is n₄

ex-plus-0 : S (S Z) plus S (S (S Z)) is S (S (S (S (S Z))))
ex-plus-0 = P-Succ (P-Succ P-Zero)

ex-times-0 : S (S Z) times S (S Z) is S (S (S (S Z)))
ex-times-0 = T-Succ (T-Succ T-Zero (P-Succ (P-Succ P-Zero))) (P-Succ (P-Succ P-Zero))

ex-1-1 : S (S Z) times S (S Z) is S (S (S (S Z)))
-- step1
-- ex-1-1 = T-Succ (T-Succ {!!} (P-Succ (P-Succ P-Zero))) (P-Succ (P-Succ P-Zero)) -- Goal: 0 times S (S Z) is 0
-- step2
-- ex-1-1 = T-Succ (T-Succ T-Zero (P-Succ (P-Succ {!!}))) (P-Succ (P-Succ P-Zero)) -- Goal: 0 plus Z is 0
-- step3
-- ex-1-1 = T-Succ (T-Succ T-Zero (P-Succ {!!})) (P-Succ (P-Succ P-Zero)) -- Goal: 1 plus Z is 1
-- step4
-- ex-1-1 = T-Succ (T-Succ T-Zero {!!}) (P-Succ (P-Succ P-Zero)) -- Goal: S (S Z) plus Z is 2
-- step5
-- ex-1-1 = T-Succ {!!} (P-Succ (P-Succ P-Zero)) -- Goal: 1 times S (S Z) is 2
-- step6
-- ex-1-1 = T-Succ (T-Succ T-Zero (P-Succ (P-Succ P-Zero))) (P-Succ (P-Succ {!!})) -- Goal: 0 plus S (S Z) is 2
-- step7
-- ex-1-1 = T-Succ (T-Succ T-Zero (P-Succ (P-Succ P-Zero))) (P-Succ {!!}) -- Goal: 1 plus S (S Z) is 3
-- step8
-- ex-1-1 = T-Succ (T-Succ T-Zero (P-Succ (P-Succ P-Zero))) {!!} -- Goal: S (S Z) plus S (S Z) is S (S (S (S Z)))
-- step9
-- ex-1-1 = {!!} -- Goal: S (S Z) times S (S Z) is S (S (S (S Z)))
-- C-cC-a
ex-1-1 = T-Succ (T-Succ T-Zero (P-Succ (P-Succ P-Zero))) (P-Succ (P-Succ P-Zero))

ex-1-2-1 : S (S (S Z)) plus S Z is S (S (S (S Z)))
ex-1-2-1 = P-Succ (P-Succ (P-Succ P-Zero))

ex-1-2-2 : S Z plus S (S (S Z)) is S (S (S (S Z)))
ex-1-2-2 = P-Succ P-Zero

ex-1-2-3 : S (S (S Z)) times Z is Z
ex-1-2-3 = T-Succ (T-Succ (T-Succ T-Zero P-Zero) P-Zero) P-Zero


steps-plus : ∀ {n₁ n₂ n₃} → n₁ plus n₂ is n₃ → ℕ
steps-plus P-Zero = 1
steps-plus (P-Succ p) = 1 + steps-plus p

steps-times : ∀ {n₁ n₂ n₃} → n₁ times n₂ is n₃ → ℕ
steps-times T-Zero = 1
steps-times (T-Succ p q) = 1 + steps-plus q + steps-times p

open import Relation.Binary.PropositionalEquality as PropEq

ex-1-3-1 : ∀ {n₁ n₂ n₃} → (p : n₁ plus n₂ is n₃) → steps-plus p ≡ 1 + n₁
ex-1-3-1 P-Zero = refl
ex-1-3-1 (P-Succ p) = cong S (ex-1-3-1 p)

ex-1-3-2 : ∀ {n₁ n₂ n₃} → (p : n₁ times n₂ is n₃) → steps-times p ≡ 1 + n₁ * (n₂ + 2)
ex-1-3-2 T-Zero = refl
ex-1-3-2 (T-Succ t p) = cong S (plus+times≡n₂+2+n₁[n₂+2] t p)
  where
    S[a+Sb]≡a+2+b : (a b : ℕ) → S (a + S b) ≡ a + 2 + b
    S[a+Sb]≡a+2+b Z b = refl
    S[a+Sb]≡a+2+b (S a) b = cong S (S[a+Sb]≡a+2+b a b)
    plus+times≡n₂+2+n₁[n₂+2] : ∀ {n₁ n₂ n₃ n₄}
                             (t : n₁ times n₂ is n₄) → (p : n₂ plus n₄ is n₃) →
                             steps-plus p + steps-times t ≡ n₂ + 2 + n₁ * (n₂ + 2)
    plus+times≡n₂+2+n₁[n₂+2] {n₁} {n₂} {n₃} {n₄} t p rewrite
      ex-1-3-1 p | ex-1-3-2 t | S[a+Sb]≡a+2+b n₂ (n₁ * (n₂ + 2)) = refl
