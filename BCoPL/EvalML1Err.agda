module BCoPL.EvalML1Err where

open import Data.Integer public
open import Data.Bool using (Bool; true; false) public
open import Data.Nat hiding (_<_; _+_; _*_) renaming (suc to S; zero to Z)
open import Relation.Binary.PropositionalEquality using (refl;_≡_) public
open import Data.Sum renaming (_⊎_ to _∨_; inj₁ to left; inj₂ to right) public
open import Data.Product using (_×_; _,_) public

data Val : Set where
  i : ℤ → Val
  b : Bool → Val

data Error : Set where
  error? : Error
  error+ : Error
  error- : Error
  error* : Error
  error< : Error

Value = Error ∨ Val

data Prim : Set where
  prim⊕ : Prim
  prim⊝ : Prim
  prim⊛ : Prim
  prim≺ : Prim

data Exp : Set where
  i : ℤ → Exp
  b : Bool → Exp
  op : Prim → Exp → Exp → Exp
  if_then_else_ : Exp → Exp → Exp → Exp

_⊕_ = op prim⊕
_⊝_ = op prim⊝
_⊛_ = op prim⊛
_≺_ = op prim≺

infixl 9 _⊛_
infixl 8 _⊕_ _⊝_
infix 7 _≺_
infix 6 if_then_else_
infixl 5 _⇓_


private
  _<ℕ_ : ℕ → ℕ → Bool
  Z <ℕ Z = false
  Z <ℕ S n = true
  S m <ℕ Z = false
  S m <ℕ S n = m <ℕ n

  infix 7 _<ℕ_ _<_

  _<_ : ℤ → ℤ → Bool
  -[1+ m ] < -[1+ n ] = n <ℕ m
  -[1+ m ] < + n = true
  + m < -[1+ n ] = false
  + m < + n = m <ℕ n

data _plus_is_ : Value → Value → Value → Set where
  B-Plus : ∀ {i₁ i₂ i₃} → i₁ + i₂ ≡ i₃ → right (i i₁) plus right (i i₂) is right (i i₃)

data _minus_is_ : Value → Value → Value → Set where
  B-Minus : ∀ {i₁ i₂ i₃} → i₁ - i₂ ≡ i₃ → right (i i₁) minus right (i i₂) is right (i i₃)

data _times_is_ : Value → Value → Value → Set where
  B-Times : ∀ {i₁ i₂ i₃} → i₁ * i₂ ≡ i₃ → right (i i₁) times right (i i₂) is right (i i₃)

data _less-than_is_ : Value → Value → Value → Set where
  B-Lt : ∀ {i₁ i₂ v} → i₁ < i₂ ≡ v → right (i i₁) less-than right (i i₂) is right (b v)

data _⇓_ : Exp → Value → Set where
  E-Int : ∀ {z} → i z ⇓ right (i z)
  E-Bool : ∀ {v} → b v ⇓ right (b v)
  E-IfT : ∀ {e₁ e₂ e₃ v} → e₁ ⇓ right (b true) → e₂ ⇓ right v → if e₁ then e₂ else e₃ ⇓ right v
  E-IfF : ∀ {e₁ e₂ e₃ v} → e₁ ⇓ right (b false) → e₃ ⇓ right v → if e₁ then e₂ else e₃ ⇓ right v
  E-Plus : ∀ {e₁ i₁ e₂ i₂ i₃} → e₁ ⇓ right i₁ → e₂ ⇓ right i₂ → right i₁ plus right i₂ is right i₃ → e₁ ⊕ e₂ ⇓ right i₃
  E-Minus : ∀ {e₁ i₁ e₂ i₂ i₃} → e₁ ⇓ right i₁ → e₂ ⇓ right i₂ → right i₁ minus right i₂ is right i₃ → e₁ ⊝ e₂ ⇓ right i₃
  E-Times : ∀ {e₁ i₁ e₂ i₂ i₃} → e₁ ⇓ right i₁ → e₂ ⇓ right i₂ → right i₁ times right i₂ is right i₃ → e₁ ⊛ e₂ ⇓ right i₃
  E-Lt : ∀ {e₁ i₁ e₂ i₂ b₃} → e₁ ⇓ right i₁ → e₂ ⇓ right i₂ → right i₁ less-than right i₂ is right b₃ → e₁ ≺ e₂ ⇓ right b₃

  E-IfInt : ∀ {e₁ e₂ e₃ z} → e₁ ⇓ right (i z) → if e₁ then e₂ else e₃ ⇓ left error?
  E-PlusBoolL : ∀ {e₁ e₂ v} → e₁ ⇓ right (b v) → e₁ ⊕ e₂ ⇓ left error+
  E-PlusBoolR : ∀ {e₁ e₂ v} → e₂ ⇓ right (b v) → e₁ ⊕ e₂ ⇓ left error+
  E-MinusBoolL : ∀ {e₁ e₂ v} → e₁ ⇓ right (b v) → e₁ ⊝ e₂ ⇓ left error-
  E-MinusBoolR : ∀ {e₁ e₂ v} → e₂ ⇓ right (b v) → e₁ ⊝ e₂ ⇓ left error-
  E-TimesBoolL : ∀ {e₁ e₂ v} → e₁ ⇓ right (b v) → e₁ ⊛ e₂ ⇓ left error*
  E-TimesBoolR : ∀ {e₁ e₂ v} → e₂ ⇓ right (b v) → e₁ ⊛ e₂ ⇓ left error*
  E-LtBoolL : ∀ {e₁ e₂ v} → e₁ ⇓ right (b v) → e₁ ≺ e₂ ⇓ left error<
  E-LtBoolR : ∀ {e₁ e₂ v} → e₂ ⇓ right (b v) → e₁ ≺ e₂ ⇓ left error<

  E-IfError : ∀ {e₁ e₂ e₃ ε} → e₁ ⇓ left ε → if e₁ then e₂ else e₃ ⇓ left ε
  E-IfTError : ∀ {e₁ e₂ e₃ ε} → e₁ ⇓ right (b true) × e₂ ⇓ left ε → if e₁ then e₂ else e₃ ⇓ left ε
  E-IfFError : ∀ {e₁ e₂ e₃ ε} → e₁ ⇓ right (b false) × e₃ ⇓ left ε → if e₁ then e₂ else e₃ ⇓ left ε
  E-PlusErrorL : ∀ {e₁ e₂ ε} → e₁ ⇓ left ε → e₁ ⊕ e₂ ⇓ left ε
  E-PlusErrorR : ∀ {e₁ e₂ ε} → e₂ ⇓ left ε → e₁ ⊕ e₂ ⇓ left ε
  E-MinusErrorL : ∀ {e₁ e₂ ε} → e₁ ⇓ left ε → e₁ ⊝ e₂ ⇓ left ε
  E-MinusErrorR : ∀ {e₁ e₂ ε} → e₂ ⇓ left ε → e₁ ⊝ e₂ ⇓ left ε
  E-TimesErrorL : ∀ {e₁ e₂ ε} → e₁ ⇓ left ε → e₁ ⊛ e₂ ⇓ left ε
  E-TimesErrorR : ∀ {e₁ e₂ ε} → e₂ ⇓ left ε → e₁ ⊛ e₂ ⇓ left ε
  E-LtErrorL : ∀ {e₁ e₂ ε} → e₁ ⇓ left ε → e₁ ≺ e₂ ⇓ left ε
  E-LtErrorR : ∀ {e₁ e₂ ε} → e₂ ⇓ left ε → e₁ ≺ e₂ ⇓ left ε
