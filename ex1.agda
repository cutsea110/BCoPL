module ex1 where

open import Data.Nat renaming (ℕ to ℕ; zero to Z; suc to S)

-- Nat
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

ex-1-4-1 : S (S (S Z)) plus S Z is S (S (S (S Z)))
ex-1-4-1 = P-Succ (P-Succ (P-Succ P-Zero))

ex-1-4-2 : S Z plus S (S (S Z)) is S (S (S (S Z)))
ex-1-4-2 = P-Succ P-Zero

ex-1-4-3 : S (S (S Z)) times Z is Z
ex-1-4-3 = T-Succ (T-Succ (T-Succ T-Zero P-Zero) P-Zero) P-Zero


data _is-less-than1_ : ℕ → ℕ → Set where
  L-Succ : ∀ {n} → n is-less-than1 S n
  L-Trans : ∀ {n₁ n₂ n₃} → n₁ is-less-than1 n₂ → n₂ is-less-than1 n₃ → n₁ is-less-than1 n₃

data _is-less-than2_ : ℕ → ℕ → Set where
  L-Zero : ∀ {n} → Z is-less-than2 S n
  L-SuccSucc : ∀ {n₁ n₂} → n₁ is-less-than2 n₂ → S n₁ is-less-than2 S n₂

data _is-less-than3_ : ℕ → ℕ → Set where
  L-Succ : ∀ {n} → n is-less-than3 S n
  L-SuccR : ∀ {n₁ n₂} → n₁ is-less-than3 n₂ → n₁ is-less-than3 S n₂

data Exp : Set where
  Nat : ℕ → Exp
  _⊕_ : Exp → Exp → Exp
  _⊛_ : Exp → Exp → Exp

infixl 5 _⊛_
infixl 4 _⊕_

-- EvalNatExp
infix 3 _⇓_
data _⇓_ : Exp → ℕ → Set where
  E-Const : ∀ {n} → Nat n ⇓ n
  E-Plus : ∀ {e₁ n₁ e₂ n₂ n} → e₁ ⇓ n₁ → e₂ ⇓ n₂ → n₁ plus n₂ is n → e₁ ⊕ e₂ ⇓ n
  E-Times : ∀ {e₁ n₁ e₂ n₂ n} → e₁ ⇓ n₁ → e₂ ⇓ n₂ → n₁ times n₂ is n → e₁ ⊛ e₂ ⇓ n

ex-1-8-1 : Nat Z ⊕ Nat (S (S Z)) ⇓ S (S Z)
ex-1-8-1 = E-Plus E-Const E-Const P-Zero

ex-1-8-2 : Nat (S (S Z)) ⊕ Nat Z ⇓ S (S Z)
ex-1-8-2 = E-Plus E-Const E-Const (P-Succ (P-Succ P-Zero))

ex-1-8-3 : Nat (S Z) ⊕ Nat (S Z) ⊕ Nat (S Z) ⇓ S (S (S Z))
ex-1-8-3 = E-Plus (E-Plus E-Const E-Const (P-Succ P-Zero)) E-Const
             (P-Succ (P-Succ P-Zero))

ex-1-8-4 : Nat (S (S (S Z))) ⊕ Nat (S (S Z)) ⊛ Nat (S Z) ⇓ S (S (S (S (S Z))))
ex-1-8-4 = E-Plus E-Const
             (E-Times E-Const E-Const
              (T-Succ (T-Succ T-Zero (P-Succ P-Zero)) (P-Succ P-Zero)))
             (P-Succ (P-Succ (P-Succ P-Zero)))

ex-1-8-5 : (Nat (S (S Z)) ⊕ Nat (S (S Z))) ⊛ Nat Z ⇓ Z
ex-1-8-5 = E-Times (E-Plus E-Const E-Const (P-Succ (P-Succ P-Zero))) E-Const
             (T-Succ (T-Succ (T-Succ (T-Succ T-Zero P-Zero) P-Zero) P-Zero)
              P-Zero)

ex-1-8-6 : Nat Z ⊛ (Nat (S (S Z)) ⊕ Nat (S (S Z))) ⇓ Z
ex-1-8-6 = E-Times E-Const (E-Plus E-Const E-Const (P-Succ (P-Succ P-Zero)))
             T-Zero

--- ReduceNatExp
infixr 3 _⟶_
data _⟶_ : Exp → Exp → Set where
  R-Plus : ∀ {n₁ n₂ n₃} → n₁ plus n₂ is n₃ → Nat n₁ ⊕ Nat n₂ ⟶ Nat n₃
  R-Times : ∀ {n₁ n₂ n₃} → n₁ times n₂ is n₃ → Nat n₁ ⊛ Nat n₂ ⟶ Nat n₃
  R-PlusL : ∀ {e₁ e₁′ e₂} → e₁ ⟶ e₁′ → e₁ ⊕ e₂ ⟶ e₁′ ⊕ e₂
  R-PlusR : ∀ {e₁ e₂ e₂′} → e₂ ⟶ e₂′ → e₁ ⊕ e₂ ⟶ e₁ ⊕ e₂′
  R-TimesL : ∀ {e₁ e₁′ e₂} → e₁ ⟶ e₁′ → e₁ ⊛ e₂ ⟶ e₁′ ⊛ e₂
  R-TimesR : ∀ {e₁ e₂ e₂′} → e₂ ⟶ e₂′ → e₁ ⊛ e₂ ⟶ e₁ ⊛ e₂′

infixr 3 _-*->_
data _-*->_ : Exp → Exp → Set where
  MR-Zero : ∀ {e} → e -*-> e
  MR-One : ∀ {e e′} → e ⟶ e′ → e -*-> e′
  MR-Multi : ∀ {e e′ e″} → e -*-> e′ → e′ -*-> e″ → e -*-> e″

infixr 3 _-d->_
data _-d->_ : Exp → Exp → Set where
  DR-Plus : ∀ {n₁ n₂ n₃} → n₁ plus n₂ is n₃ → Nat n₁ ⊕ Nat n₂ -d-> Nat n₃
  DR-Times : ∀ {n₁ n₂ n₃} → n₁ times n₂ is n₃ → Nat n₁ ⊛ Nat n₂ -d-> Nat n₃
  DR-PlusL : ∀ {e₁ e₁′ e₂} → e₁ -d-> e₁′ → e₁ ⊕ e₂ -d-> e₁′ ⊕ e₂
  DR-PlusR : ∀ {n₁ e₂ e₂′} → e₂ -d-> e₂′ → Nat n₁ ⊕ e₂ -d-> Nat n₁ ⊕ e₂′
  DR-TimesL : ∀ {e₁ e₁′ e₂} → e₁ -d-> e₁′ → e₁ ⊛ e₂ -d-> e₁′ ⊛ e₂
  DR-TimesR : ∀ {n₁ e₂ e₂′} → e₂ -d-> e₂′ → Nat n₁ ⊛ e₂ -d-> Nat n₁ ⊛ e₂′

ex-1-9-1 : Nat Z ⊕ Nat (S (S Z)) -*-> Nat (S (S Z))
ex-1-9-1 = MR-One (R-Plus P-Zero)

ex-1-9-2 : Nat (S Z) ⊛ Nat (S Z) ⊕ Nat (S Z) ⊛ Nat (S Z) -d-> Nat (S Z) ⊕ Nat (S Z) ⊛ Nat (S Z)
ex-1-9-2 = DR-PlusL (DR-Times (T-Succ T-Zero (P-Succ P-Zero)))

ex-1-9-3 : Nat (S Z) ⊛ Nat (S Z) ⊕ Nat (S Z) ⊛ Nat (S Z) ⟶ Nat (S Z) ⊛ Nat (S Z) ⊕ Nat (S Z)
ex-1-9-3 = R-PlusR (R-Times (T-Succ T-Zero (P-Succ P-Zero)))

sub-ex-1-9-4-1 : Nat (S Z) ⊛ Nat (S Z) -*-> Nat (S Z)
sub-ex-1-9-4-1 = MR-One (R-Times (T-Succ T-Zero (P-Succ P-Zero)))

sub-ex-1-9-4-2 : Nat (S Z) ⊕ Nat (S Z) -*-> Nat (S (S Z))
sub-ex-1-9-4-2 = MR-One (R-Plus (P-Succ P-Zero))

ex-1-9-4 : (Nat (S Z) ⊛ Nat (S Z)) ⊕ (Nat (S Z) ⊛ Nat (S Z)) -*-> Nat (S (S Z))
ex-1-9-4 = MR-Multi (MR-One (R-PlusL (R-Times (T-Succ T-Zero (P-Succ P-Zero)))))
                    (MR-Multi (MR-One (R-PlusR (R-Times (T-Succ T-Zero (P-Succ P-Zero)))))
                              (MR-One (R-Plus (P-Succ P-Zero))))
{--
S(Z) * S(Z) + S(Z) * S(Z) -*-> S(S(Z)) by MR-Multi {
  S(Z) * S(Z) + S(Z) * S(Z) -*-> S(Z) + S(Z) * S(Z) by MR-One {
    S(Z) * S(Z) + S(Z) * S(Z) ---> S(Z) + S(Z) * S(Z) by R-PlusL {
      S(Z) * S(Z) ---> S(Z) by R-Times {
        S(Z) times S(Z) is S(Z) by T-Succ {
          Z times S(Z) is Z by T-Zero {};
          S(Z) plus Z is S(Z) by P-Succ {
            Z plus Z is Z by P-Zero {}
          }
        }
      }
    }
  };
  S(Z) + S(Z) * S(Z) -*-> S(S(Z)) by MR-Multi {
    S(Z) + S(Z) * S(Z) -*-> S(Z) + S(Z) by MR-One {
      S(Z) + S(Z) * S(Z) ---> S(Z) + S(Z) by R-PlusR {
        S(Z) * S(Z) ---> S(Z) by R-Times {
          S(Z) times S(Z) is S(Z) by T-Succ {
            Z times S(Z) is Z by T-Zero {};
            S(Z) plus Z is S(Z) by P-Succ {
              Z plus Z is Z by P-Zero {}
            }
          }
        }
      }
    };
    S(Z) + S(Z) -*-> S(S(Z)) by MR-One {
      S(Z) + S(Z) ---> S(S(Z)) by R-Plus {
        S(Z) plus S(Z) is S(S(Z)) by P-Succ {
          Z plus S(Z) is S(Z) by P-Zero {}
        }
      }
    }
  }
}
--}

infixr 3 _-d+>_
data _-d+>_ : Exp → Exp → Set where
  DR-Plus : ∀ {n₁ n₂ n₃} → n₁ plus n₂ is n₃ → Nat n₁ ⊕ Nat n₂ -d+> Nat n₃
  DR-Times : ∀ {n₁ n₂ n₃} → n₁ times n₂ is n₃ → Nat n₁ ⊛ Nat n₂ -d+> Nat n₃
  DR-PlusL : ∀ {e₁ e₂ e₂′} → e₂ -d-> e₂′ → e₁ ⊕ e₂ -d+> e₁ ⊕ e₂′
  DR-PlusR : ∀ {e₁ e₁′ n₂} → e₁ -d+> e₁′ → e₁ ⊕ Nat n₂ -d+> e₁′ ⊕ Nat n₂
  DR-TimesL : ∀ {e₁ e₂ e₂′} → e₂ -d+> e₂′ → e₁ ⊛ e₂ -d+> e₁ ⊛ e₂′
  DR-TimesR : ∀ {e₁ e₁′ n₂} → e₁ -d+> e₁′ → e₁ ⊛ Nat n₂ -d+> e₁′ ⊛ Nat n₂

ex-1-10-1 : Nat (S Z) ⊛ Nat (S Z) ⊕ Nat (S Z) ⊛ Nat (S Z) -d+> Nat (S Z) ⊛ Nat (S Z) ⊕ Nat (S Z)
ex-1-10-1 = DR-PlusL (DR-Times (T-Succ T-Zero (P-Succ P-Zero)))

ex-1-10-2 : Nat (S Z) ⊛ Nat (S Z) ⊕ Nat (S Z) -d+> Nat (S Z) ⊕ Nat (S Z)
ex-1-10-2 = DR-PlusR (DR-Times (T-Succ T-Zero (P-Succ P-Zero)))
