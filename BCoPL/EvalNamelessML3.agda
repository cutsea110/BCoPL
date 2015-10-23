module BCoPL.EvalNamelessML3 where

open import Data.Bool using (Bool; true; false) public
open import Data.Integer public
open import Data.Nat hiding (_<_; _+_; _*_) renaming (suc to S; zero to Z)
open import Data.Product using (_×_;_,_) public
open import Data.String using (String) public

open import Relation.Binary.Core public
open import Relation.Binary.PropositionalEquality using (refl;_≡_) public

Var = String
data DBValue : Set
BindedValue = Var × DBValue

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

data DBValueList : Set where
  ● : DBValueList
  _⊱_ : DBValueList → DBValue → DBValueList

data DBValue where
  error : DBValue
  i : ℤ → DBValue
  b : Bool → DBValue
  ⟨_⟩[fuṇ⇒_] : DBValueList → DBExp → DBValue
  ⟨_⟩[rec̣≔fuṇ⇒_] : DBValueList → DBExp → DBValue

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

data _plus_is_ : DBValue → DBValue → DBValue → Set where
  B-Plus : ∀ {i₁ i₂ i₃} → i₁ + i₂ ≡ i₃ → i i₁ plus i i₂ is i i₃

data _minus_is_ : DBValue → DBValue → DBValue → Set where
  B-Minus : ∀ {i₁ i₂ i₃} → i₁ - i₂ ≡ i₃ → i i₁ minus i i₂ is i i₃

data _times_is_ : DBValue → DBValue → DBValue → Set where
  B-Times : ∀ {i₁ i₂ i₃} → i₁ * i₂ ≡ i₃ → i i₁ times i i₂ is i i₃

data _less-than_is_ : DBValue → DBValue → DBValue → Set where
  B-Lt : ∀ {i₁ i₂ v} → i₁ < i₂ ≡ v → i i₁ less-than i i₂ is b v

_⟦_⟧ : DBValueList → ℕ → DBValue
● ⟦ Z ⟧ = error
● ⟦ S n ⟧ = error
(ν ⊱ x) ⟦ Z ⟧ = x
(ν ⊱ x) ⟦ S n ⟧ = ν ⟦ n ⟧

data _⊢_⇓_ : DBValueList → DBExp → DBValue → Set where
  E-Int : ∀ {ν n}
          → ν ⊢ i n ⇓ i n
  E-Bool : ∀ {ν v}
           → ν ⊢ b v ⇓ b v
  E-IfT : ∀ {ν d₁ d₂ d₃ w}
          → ν ⊢ d₁ ⇓ b true
          → ν ⊢ d₂ ⇓ w
          → ν ⊢ if d₁ then d₂ else d₃ ⇓ w
  E-IfF : ∀ {ν d₁ d₂ d₃ w}
          → ν ⊢ d₁ ⇓ b false
          → ν ⊢ d₃ ⇓ w
          → ν ⊢ if d₁ then d₂ else d₃ ⇓ w
  E-Plus : ∀ {ν d₁ d₂ i₁ i₂ i₃}
           → ν ⊢ d₁ ⇓ i₁
           → ν ⊢ d₂ ⇓ i₂
           → i₁ plus i₂ is i₃
           → ν ⊢ d₁ ⊕̂ d₂ ⇓ i₃
  E-Minus : ∀ {ν d₁ d₂ i₁ i₂ i₃}
            → ν ⊢ d₁ ⇓ i₁
            → ν ⊢ d₂ ⇓ i₂
            → i₁ minus i₂ is i₃
            → ν ⊢ d₁ ⊝̂ d₂ ⇓ i₃
  E-Times : ∀ {ν d₁ d₂ i₁ i₂ i₃}
            → ν ⊢ d₁ ⇓ i₁
            → ν ⊢ d₂ ⇓ i₂
            → i₁ times i₂ is i₃
            → ν ⊢ d₁ ⊛̂ d₂ ⇓ i₃
  E-Lt : ∀ {ν d₁ d₂ i₁ i₂ i₃}
         → ν ⊢ d₁ ⇓ i₁
         → ν ⊢ d₂ ⇓ i₂
         → i₁ less-than i₂ is i₃
         → ν ⊢ d₁ ≺̂ d₂ ⇓ i₃
  E-Var : ∀ {ν n}
          → ν ⊢ # n ⇓ ν ⟦ n ⟧
  E-Let : ∀ {ν d₁ d₂ w₁ w}
          → ν ⊢ d₁ ⇓ w₁
          → ν ⊱ w₁ ⊢ d₂ ⇓ w
          → ν ⊢ ℓeṭ≔ d₁ ιn d₂ ⇓ w
  E-Fun : ∀ {ν d}
          → ν ⊢ fuṇ⇒ d ⇓ ⟨ ν ⟩[fuṇ⇒ d ]
  E-App : ∀ {ν ν₂ d₀ d₁ d₂ w w₂}
          → ν ⊢ d₁ ⇓ ⟨ ν₂ ⟩[fuṇ⇒ d₀ ]
          → ν ⊢ d₂ ⇓ w₂
          → ν₂ ⊱ w₂ ⊢ d₀ ⇓ w
          → ν ⊢ app d₁ d₂ ⇓ w
  E-LetRec : ∀ {ν d₁ d₂ w}
             → ν ⊱ ⟨ ν ⟩[rec̣≔fuṇ⇒ d₁ ] ⊢ d₂ ⇓ w
             → ν ⊢ ℓetrec̣≔fuṇ⇒ d₁ ιn d₂ ⇓ w
  E-AppRec : ∀ {ν ν₂ d₀ d₁ d₂ w w₂}
           → ν ⊢ d₁ ⇓ ⟨ ν₂ ⟩[rec̣≔fuṇ⇒ d₀ ]
           → ν ⊢ d₂ ⇓ w₂
           → ν₂ ⊱ ⟨ ν₂ ⟩[rec̣≔fuṇ⇒ d₀ ] ⊱ w₂ ⊢ d₀ ⇓ w
           → ν ⊢ app d₁ d₂ ⇓ w
