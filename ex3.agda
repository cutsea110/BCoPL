module ex3 where

open import Data.Integer
open import Data.Bool
open import Data.Nat hiding (_<_; _+_; _*_) renaming (suc to S; zero to Z)
open import Relation.Binary.PropositionalEquality as PropEq

data Value : Set where
  i : ℤ → Value
  b : Bool → Value

data Exp : Set where
  i : ℤ → Exp
  b : Bool → Exp
  _⊕_ : Exp → Exp → Exp
  _⊝_ : Exp → Exp → Exp
  _⊛_ : Exp → Exp → Exp
  _≺_ : Exp → Exp → Exp
  If_Then_Else_ : Exp → Exp → Exp → Exp

infixl 9 _⊛_
infixl 8 _⊕_ _⊝_
infix 7 _≺_ _<ℕ_ _<_
infix 6 If_Then_Else_
infixl 5 _⇓_

_<ℕ_ : ℕ → ℕ → Bool
Z <ℕ Z = false
Z <ℕ S n = true
S m <ℕ Z = false
S m <ℕ S n = m <ℕ n

_<_ : ℤ → ℤ → Bool
-[1+ m ] < -[1+ n ] = n <ℕ m
-[1+ m ] < + n = true
+ m < -[1+ n ] = false
+ m < + n = m <ℕ n

data _plus_is_ : Value → Value → Value → Set where
  B-PLUS : ∀ {i₁ i₂ i₃} → i₁ + i₂ ≡ i₃ → i i₁ plus i i₂ is i i₃

data _minus_is_ : Value → Value → Value → Set where
  B-MINUS : ∀ {i₁ i₂ i₃} → i₁ - i₂ ≡ i₃ → i i₁ minus i i₂ is i i₃

data _times_is_ : Value → Value → Value → Set where
  B-TIMES : ∀ {i₁ i₂ i₃} → i₁ * i₂ ≡ i₃ → i i₁ times i i₂ is i i₃

data _less-than_is_ : Value → Value → Value → Set where
  B-LT : ∀ {i₁ i₂ v} → i₁ < i₂ ≡ v → i i₁ less-than i i₂ is b v

data _⇓_ : Exp → Value → Set where
  E-INT : ∀ {z} → i z ⇓ i z
  E-BOOL : ∀ {v} → b v ⇓ b v
  E-IFT : ∀ {e₁ e₂ e₃ v} → e₁ ⇓ b true → e₂ ⇓ v → If e₁ Then e₂ Else e₃ ⇓ v
  E-IFF : ∀ {e₁ e₂ e₃ v} → e₁ ⇓ b false → e₃ ⇓ v → If e₁ Then e₂ Else e₃ ⇓ v
  E-PLUS : ∀ {e₁ i₁ e₂ i₂ i₃} → e₁ ⇓ i₁ → e₂ ⇓ i₂ → i₁ plus i₂ is i₃ → e₁ ⊕ e₂ ⇓ i₃
  E-MINUS : ∀ {e₁ i₁ e₂ i₂ i₃} → e₁ ⇓ i₁ → e₂ ⇓ i₂ → i₁ minus i₂ is i₃ → e₁ ⊝ e₂ ⇓ i₃
  E-TIMES : ∀ {e₁ i₁ e₂ i₂ i₃} → e₁ ⇓ i₁ → e₂ ⇓ i₂ → i₁ times i₂ is i₃ → e₁ ⊛ e₂ ⇓ i₃
  E-LT : ∀ {e₁ i₁ e₂ i₂ b₃} → e₁ ⇓ i₁ → e₂ ⇓ i₂ → i₁ less-than i₂ is b₃ → e₁ ≺ e₂ ⇓ b₃

-- excercise 3.1
ex-3-1-1 : i (+ 3) ⊕ i (+ 5) ⇓ i (+ 8)
ex-3-1-1 = E-PLUS E-INT E-INT (B-PLUS refl)

ex-3-1-2 : i (+ 8) ⊝ i (+ 2) ⊝ i (+ 3) ⇓ i (+ 3)
ex-3-1-2 = E-MINUS (E-MINUS E-INT E-INT (B-MINUS refl)) E-INT (B-MINUS refl)

ex-3-1-3 : (i (+ 4) ⊕ i (+ 5)) ⊛ (i (+ 1) ⊝ i (+ 10)) ⇓ i (-[1+ 80 ])
ex-3-1-3 = E-TIMES (E-PLUS E-INT E-INT (B-PLUS refl)) (E-MINUS E-INT E-INT (B-MINUS refl)) (B-TIMES refl)

ex-3-1-4 : If i (+ 4) ≺ i (+ 5) Then i (+ 2) ⊕ i (+ 3) Else i (+ 8) ⊛ i (+ 8) ⇓ i (+ 5)
ex-3-1-4 = E-IFT (E-LT E-INT E-INT (B-LT refl)) (E-PLUS E-INT E-INT (B-PLUS refl))

ex-3-1-5 : i (+ 3) ⊕ (If i (-[1+ 22 ]) ≺ i (-[1+ 1 ]) ⊛ i (+ 8) Then i (+ 8) Else i (+ 2) ⊕ i (+ 4)) ⇓ i (+ 11)
ex-3-1-5 = E-PLUS E-INT (E-IFT (E-LT E-INT (E-TIMES E-INT E-INT (B-TIMES refl)) (B-LT refl)) E-INT) (B-PLUS refl)

ex-3-1-6 : i (+ 3) ⊕ (If i (-[1+ 22 ]) ≺ i (-[1+ 1 ]) ⊛ i (+ 8) Then i (+ 8) Else i (+ 2)) ⊕ i (+ 4) ⇓ i (+ 15)
ex-3-1-6 = E-PLUS (E-PLUS E-INT (E-IFT (E-LT E-INT (E-TIMES E-INT E-INT (B-TIMES refl)) (B-LT refl)) E-INT) (B-PLUS refl)) E-INT (B-PLUS refl)
