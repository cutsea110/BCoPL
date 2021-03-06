module BCoPL.EvalML1 where

open import Data.Integer hiding (_<_) public
open import Data.Bool using (Bool; true; false) public
open import Data.Nat hiding (_<_; _+_; _*_) renaming (suc to S; zero to Z)
open import Relation.Binary.PropositionalEquality using (refl;_≡_) public

data Value : Set where
  i : ℤ → Value
  b : Bool → Value

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
  B-Plus : ∀ {i₁ i₂ i₃} → i₁ + i₂ ≡ i₃ → i i₁ plus i i₂ is i i₃

data _minus_is_ : Value → Value → Value → Set where
  B-Minus : ∀ {i₁ i₂ i₃} → i₁ - i₂ ≡ i₃ → i i₁ minus i i₂ is i i₃

data _times_is_ : Value → Value → Value → Set where
  B-Times : ∀ {i₁ i₂ i₃} → i₁ * i₂ ≡ i₃ → i i₁ times i i₂ is i i₃

data _less-than_is_ : Value → Value → Value → Set where
  B-Lt : ∀ {i₁ i₂ v} → i₁ < i₂ ≡ v → i i₁ less-than i i₂ is b v

data _⇓_ : Exp → Value → Set where
  E-Int : ∀ {z} → i z ⇓ i z
  E-Bool : ∀ {v} → b v ⇓ b v
  E-IfT : ∀ {e₁ e₂ e₃ v} → e₁ ⇓ b true → e₂ ⇓ v → if e₁ then e₂ else e₃ ⇓ v
  E-IfF : ∀ {e₁ e₂ e₃ v} → e₁ ⇓ b false → e₃ ⇓ v → if e₁ then e₂ else e₃ ⇓ v
  E-Plus : ∀ {e₁ i₁ e₂ i₂ i₃} → e₁ ⇓ i₁ → e₂ ⇓ i₂ → i₁ plus i₂ is i₃ → e₁ ⊕ e₂ ⇓ i₃
  E-Minus : ∀ {e₁ i₁ e₂ i₂ i₃} → e₁ ⇓ i₁ → e₂ ⇓ i₂ → i₁ minus i₂ is i₃ → e₁ ⊝ e₂ ⇓ i₃
  E-Times : ∀ {e₁ i₁ e₂ i₂ i₃} → e₁ ⇓ i₁ → e₂ ⇓ i₂ → i₁ times i₂ is i₃ → e₁ ⊛ e₂ ⇓ i₃
  E-Lt : ∀ {e₁ i₁ e₂ i₂ b₃} → e₁ ⇓ i₁ → e₂ ⇓ i₂ → i₁ less-than i₂ is b₃ → e₁ ≺ e₂ ⇓ b₃
