module BCoPL.NamelessML3 where

open import Data.Bool using (Bool; true; false) public
open import Data.Integer public
open import Data.Nat hiding (_<_; _+_; _*_) renaming (suc to S; zero to Z)
open import Data.Product using (_×_;_,_) public
open import Data.String using (String) public

open import Relation.Binary.Core public
open import Relation.Binary.PropositionalEquality using (refl;_≡_) public

Var = String
data Value : Set
BindedValue = Var × Value

data Prim : Set where
  prim⊕ : Prim
  prim⊝ : Prim
  prim⊛ : Prim
  prim≺ : Prim

data Env : Set where
  ● : Env
  _⊱_ : Env → BindedValue → Env

data Exp : Set where
  i : ℤ → Exp
  b : Bool → Exp
  var : Var → Exp
  op : Prim → Exp → Exp → Exp
  if_then_else_ : Exp → Exp → Exp → Exp
  ℓet_≔_ιn_ : Var → Exp → Exp → Exp
  ℓetrec_≔fun_⇒_ιn_ : Var → Var → Exp → Exp → Exp
  fun_⇒_ : Var → Exp → Exp
  app : Exp → Exp → Exp

data DBExp : Set where
  i : ℤ → DBExp
  b : Bool → DBExp
  # : ℕ → DBExp
  op : Prim → DBExp → DBExp → DBExp
  if_then_else_ : DBExp → DBExp → DBExp → DBExp
  ℓeṭ≔_ιn_ : DBExp → DBExp → DBExp
  ℓetrec̣≔fuṇ⇒_ιn_ : DBExp → DBExp → DBExp
  fuṇ⇒_ : DBExp → DBExp
  app : DBExp → DBExp → DBExp

data VarList : Set where
  ● : VarList
  _⊱_ : VarList → Var → VarList

data Value where
  i : ℤ → Value
  b : Bool → Value
  ⟨_⟩[fun_⇒_] : Env → Var → Exp → Value
  ⟨_⟩[rec_≔fun_⇒_] : Env → Var → Var → Exp → Value

_⊕_ : Exp → Exp → Exp
_⊕_ = op prim⊕
_⊝_ : Exp → Exp → Exp
_⊝_ = op prim⊝
_⊛_ : Exp → Exp → Exp
_⊛_ = op prim⊛
_≺_ : Exp → Exp → Exp
_≺_ = op prim≺

_⊕̂_ : DBExp → DBExp → DBExp
_⊕̂_ = op prim⊕
_⊝̂_ : DBExp → DBExp → DBExp
_⊝̂_ = op prim⊝
_⊛̂_ : DBExp → DBExp → DBExp
_⊛̂_ = op prim⊛
_≺̂_ : DBExp → DBExp → DBExp
_≺̂_ = op prim≺

infixl 20 _⊱_

infixl 9 _⊛_
infixl 8 _⊕_ _⊝_
infix 7 _≺_
infix 6 if_then_else_ ℓet_≔_ιn_ ℓetrec_≔fun_⇒_ιn_ fun_⇒_ ℓeṭ≔_ιn_ ℓetrec̣≔fuṇ⇒_ιn_ fuṇ⇒_
infixl 5 _⊢_⟾_

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

data _⊢_⟾_ : VarList → Exp → DBExp → Set where
  TR-Int : ∀ {χ n}
           → χ ⊢ i n ⟾ i n
  TR-Bool : ∀ {χ v}
            → χ ⊢ b v ⟾ b v
  TR-If : ∀ {χ e₁ e₂ e₃ d₁ d₂ d₃}
          → χ ⊢ e₁ ⟾ d₁
          → χ ⊢ e₂ ⟾ d₂
          → χ ⊢ e₃ ⟾ d₃
          → χ ⊢ if e₁ then e₂ else e₃ ⟾ if d₁ then d₂ else d₃
  TR-Plus : ∀ {χ e₁ e₂ d₁ d₂}
          → χ ⊢ e₁ ⟾ d₁
          → χ ⊢ e₂ ⟾ d₂
          → χ ⊢ e₁ ⊕ e₂ ⟾ d₁ ⊕̂ d₂
  TR-Minus : ∀ {χ e₁ e₂ d₁ d₂}
           → χ ⊢ e₁ ⟾ d₁
           → χ ⊢ e₂ ⟾ d₂
           → χ ⊢ e₁ ⊝ e₂ ⟾ d₁ ⊝̂ d₂
  TR-Times : ∀ {χ e₁ e₂ d₁ d₂}
           → χ ⊢ e₁ ⟾ d₁
           → χ ⊢ e₂ ⟾ d₂
           → χ ⊢ e₁ ⊛ e₂ ⟾ d₁ ⊛̂ d₂
  TR-Lt : ∀ {χ e₁ e₂ d₁ d₂}
          → χ ⊢ e₁ ⟾ d₁
          → χ ⊢ e₂ ⟾ d₂
          → χ ⊢ e₁ ≺ e₂ ⟾ d₁ ≺̂ d₂
  TR-Var1 : ∀ {χ x n}
            → n ≡ 1
            → χ ⊱ x ⊢ var x ⟾ # n
  TR-Var2 : ∀ {χ x y n₁}
            → y ≢ x
            → χ ⊢ var x ⟾ # n₁
            → χ ⊱ y ⊢ var x ⟾ # (S n₁)
  TR-Let : ∀ {χ e₁ e₂ d₁ d₂ x}
           → χ ⊢ e₁ ⟾ d₁
           → χ ⊱ x ⊢ e₂ ⟾ d₂
           → χ ⊢ ℓet x ≔ e₁ ιn e₂ ⟾ ℓeṭ≔ d₁ ιn d₂
  TR-Fun : ∀ {χ x e d}
           → χ ⊱ x ⊢ e ⟾ d
           → χ ⊢ fun x ⇒ e ⟾ fuṇ⇒ d
  TR-App : ∀ {χ e₁ e₂ d₁ d₂}
           → χ ⊢ e₁ ⟾ d₁
           → χ ⊢ e₂ ⟾ d₂
           → χ ⊢ app e₁ e₂ ⟾ app d₁ d₂
  TR-LetRec : ∀ {χ x y e₁ e₂ d₁ d₂}
              → χ ⊱ x ⊱ y ⊢ e₁ ⟾ d₁
              → χ ⊱ x ⊢ e₂ ⟾ d₂
              → χ ⊢ ℓetrec x ≔fun y ⇒ e₁ ιn e₂ ⟾ ℓetrec̣≔fuṇ⇒ d₁ ιn d₂
