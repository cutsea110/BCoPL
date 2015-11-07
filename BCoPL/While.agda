module BCoPL.While where

open import Data.Integer public
open import Data.Bool using (Bool; true; false) public
open import Data.Nat hiding (_<_; _+_; _*_) renaming (suc to S; zero to Z)
open import Data.Product using (_×_) public
open import Data.String using (String) public
open import Relation.Binary.PropositionalEquality using (refl;_≡_) public

Var = String
data Store : Set
data IValue : Set
data BValue : Set
data Prim : Set
data LOp : Set
data Comp : Set
BindedValue = Var × IValue

data IValue where
  i : ℤ → IValue

data BValue where
  b : Bool → BValue

data Store where
  ● : Store
  _⊱_ : Store → BindedValue → Store

data AExp : Set where
  i : ℤ → AExp
  var : Var → AExp
  aop : Prim → AExp → AExp → AExp

data Prim where
  prim⊕ : Prim
  prim⊝ : Prim
  prim⊛ : Prim

data BExp : Set where
  b : Bool → BExp
  ! : BExp → BExp
  lop : LOp → BExp → BExp → BExp
  comp : Comp → AExp → AExp → BExp

data LOp where
  prim&& : LOp
  prim|| : LOp

data Comp where
  prim≺ : Comp
  prim≈ : Comp
  prim≼ : Comp

data Com : Set where
  skip : Com
  _≔_ : Var → AExp → Com
  _>>_ : Com → Com → Com
  if_then_else_ : BExp → Com → Com → Com
  while_do_ : BExp → Com → Com

_⊕_ = aop prim⊕
_⊝_ = aop prim⊝
_⊛_ = aop prim⊛
_≺_ = comp prim≺
_≈_ = comp prim≈
_≼_ = comp prim≼
_&&_ = lop prim&&
_||_ = lop prim||

infixl 9 _⊛_
infixl 8 _⊕_ _⊝_
infix 7 _≺_ _≈_ _≼_
infixl 7 _&&_ _≔_
infixl 6 _||_
infix 6 if_then_else_
infixr 5 _>>_


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

data _plus_is_ : IValue → IValue → IValue → Set where
  B-Plus : ∀ {i₁ i₂ i₃} → i₁ + i₂ ≡ i₃ → i i₁ plus i i₂ is i i₃

data _minus_is_ : IValue → IValue → IValue → Set where
  B-Minus : ∀ {i₁ i₂ i₃} → i₁ - i₂ ≡ i₃ → i i₁ minus i i₂ is i i₃

data _times_is_ : IValue → IValue → IValue → Set where
  B-Times : ∀ {i₁ i₂ i₃} → i₁ * i₂ ≡ i₃ → i i₁ times i i₂ is i i₃

data _less-than_is_ : IValue → IValue → BValue → Set where
  B-Lt : ∀ {i₁ i₂ v} → i₁ < i₂ ≡ v → i i₁ less-than i i₂ is b v

