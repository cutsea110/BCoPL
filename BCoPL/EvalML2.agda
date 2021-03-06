module BCoPL.EvalML2 where

open import Data.Bool using (Bool; true; false) public
open import Data.Integer hiding (_<_) public
open import Data.Nat hiding (_<_; _+_; _*_) renaming (suc to S; zero to Z)
open import Data.Product using (_×_;_,_) public
open import Data.String using (String) public

open import Relation.Binary.Core public
open import Relation.Binary.PropositionalEquality using (refl;_≡_; _≢_) public

data Value : Set where
  i : ℤ → Value
  b : Bool → Value

Var = String

BindedValue = Var × Value

data Env : Set where
  ● : Env
  _⊱_ : Env → BindedValue → Env

data Prim : Set where
  prim⊕ : Prim
  prim⊝ : Prim
  prim⊛ : Prim
  prim≺ : Prim

data Exp : Set where
  i : ℤ → Exp
  b : Bool → Exp
  var : Var → Exp
  op : Prim → Exp → Exp → Exp
  if_then_else_ : Exp → Exp → Exp → Exp
  ℓet_≔_ιn_ : Var → Exp → Exp → Exp

_⊕_ = op prim⊕
_⊝_ = op prim⊝
_⊛_ = op prim⊛
_≺_ = op prim≺

infixl 20 _⊱_

infixl 9 _⊛_
infixl 8 _⊕_ _⊝_
infix 7 _≺_
infix 6 if_then_else_ ℓet_≔_ιn_
infixl 5 _⊢_⇓_


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

data _⊢_⇓_ : Env → Exp → Value → Set where
  E-Int : ∀ {ε z} → ε ⊢ i z ⇓ i z
  E-Bool : ∀ {ε v} → ε ⊢ b v ⇓ b v
  E-Var1 : ∀ {ε x v} → ε ⊱ (x , v) ⊢ var x ⇓ v
  E-Var2 : ∀ {ε x y v₁ v₂} → (p : x ≢ y) → ε ⊢ var x ⇓ v₂ → ε ⊱ (y , v₁) ⊢ var x ⇓ v₂
  E-Plus : ∀ {ε e₁ i₁ e₂ i₂ i₃} → ε ⊢ e₁ ⇓ i₁ → ε ⊢ e₂ ⇓ i₂ → i₁ plus i₂ is i₃ → ε ⊢ e₁ ⊕ e₂ ⇓ i₃
  E-Minus : ∀ {ε e₁ i₁ e₂ i₂ i₃} → ε ⊢ e₁ ⇓ i₁ → ε ⊢ e₂ ⇓ i₂ → i₁ minus i₂ is i₃ → ε ⊢ e₁ ⊝ e₂ ⇓ i₃
  E-Times : ∀ {ε e₁ i₁ e₂ i₂ i₃} → ε ⊢ e₁ ⇓ i₁ → ε ⊢ e₂ ⇓ i₂ → i₁ times i₂ is i₃ → ε ⊢ e₁ ⊛ e₂ ⇓ i₃
  E-Lt : ∀ {ε e₁ i₁ e₂ i₂ b₃} → ε ⊢ e₁ ⇓ i₁ → ε ⊢ e₂ ⇓ i₂ → i₁ less-than i₂ is b₃ → ε ⊢ e₁ ≺ e₂ ⇓ b₃
  E-IfT : ∀ {ε e₁ e₂ e₃ v} → ε ⊢ e₁ ⇓ b true → ε ⊢ e₂ ⇓ v → ε ⊢ if e₁ then e₂ else e₃ ⇓ v
  E-IfF : ∀ {ε e₁ e₂ e₃ v} → ε ⊢ e₁ ⇓ b false → ε ⊢ e₃ ⇓ v → ε ⊢ if e₁ then e₂ else e₃ ⇓ v
  E-Let : ∀ {ε x e₁ e₂ v v₁} → ε ⊢ e₁ ⇓ v₁ → ε ⊱ (x , v₁) ⊢ e₂ ⇓ v → ε ⊢ ℓet x ≔ e₁ ιn e₂ ⇓ v
