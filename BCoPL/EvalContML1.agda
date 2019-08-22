module BCoPL.EvalContML1 where

open import Data.Integer hiding (_<_) public
open import Data.Bool using (Bool; true; false) public
open import Data.Nat hiding (_<_; _+_; _*_) renaming (suc to S; zero to Z)
open import Relation.Binary.PropositionalEquality using (refl;_≡_; _≢_) public

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

data Section : Set where
  _<$_ : Prim → Exp → Section
  _$>_ : Value → Prim → Section
  if⋆then_else_ : Exp → Exp → Section

⋆⊕_ : Exp → Section
⋆⊕ e = prim⊕ <$ e
_⊕⋆ : Value → Section
v ⊕⋆ = v $> prim⊕
⋆⊝_ : Exp → Section
⋆⊝ e = prim⊝ <$ e
_⊝⋆ : Value → Section
v ⊝⋆ = v $> prim⊝
⋆⊛_ : Exp → Section
⋆⊛ e = prim⊛ <$ e
_⊛⋆ : Value → Section
v ⊛⋆ = v $> prim⊛
⋆≺_ : Exp → Section
⋆≺ e = prim≺ <$ e
_≺⋆ : Value → Section
v ≺⋆ = v $> prim≺

data Cont : Set where
  ⋆ : Cont
  ⟦_⟧≫_ : Section → Cont → Cont

_⊕_ = op prim⊕
_⊝_ = op prim⊝
_⊛_ = op prim⊛
_≺_ = op prim≺

infixl 9 _⊛_
infixl 8 _⊕_ _⊝_
infix 7 _≺_
infix 6 if_then_else_ if⋆then_else_
infixr 6 ⟦_⟧≫_
infixl 5 _≫_⇓_ _⇒_⇓_


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

data _≫_⇓_ : Exp → Cont → Value → Set
data _⇒_⇓_ : Value → Cont → Value → Set

data _⇒_⇓_ where
  C-Ret : ∀ {v} → v ⇒ ⋆ ⇓ v
  C-EvalR : ∀ {e v₁ v₂ k ⊗} → e ≫ ⟦ v₁ $> ⊗ ⟧≫ k ⇓ v₂ → v₁ ⇒ ⟦ ⊗ <$ e ⟧≫ k ⇓ v₂
  C-Plus : ∀ {i₁ i₂ i₃ k v} → i₁ plus i₂ is i₃ → i₃ ⇒ k ⇓ v → i₂ ⇒ ⟦ i₁ ⊕⋆ ⟧≫ k ⇓ v
  C-Minus : ∀ {i₁ i₂ i₃ k v} → i₁ minus i₂ is i₃ → i₃ ⇒ k ⇓ v → i₂ ⇒ ⟦ i₁ ⊝⋆ ⟧≫ k ⇓ v
  C-Times : ∀ {i₁ i₂ i₃ k v} → i₁ times i₂ is i₃ → i₃ ⇒ k ⇓ v → i₂ ⇒ ⟦ i₁ ⊛⋆ ⟧≫ k ⇓ v
  C-Lt : ∀ {i₁ i₂ i₃ k v} → i₁ less-than i₂ is i₃ → i₃ ⇒ k ⇓ v → i₂ ⇒ ⟦ i₁ ≺⋆ ⟧≫ k ⇓ v
  C-IfT : ∀ {e₁ e₂ k v} → e₁ ≫ k ⇓ v → b true ⇒ ⟦ if⋆then e₁ else e₂ ⟧≫ k ⇓ v
  C-IfF : ∀ {e₁ e₂ k v} → e₂ ≫ k ⇓ v → b false ⇒ ⟦ if⋆then e₁ else e₂ ⟧≫ k ⇓ v

data _≫_⇓_ where
  E-Int : ∀ {n k v} → i n ⇒ k ⇓ v → i n ≫ k ⇓ v
  E-Bool : ∀ {x k v} → b x ⇒ k ⇓ v → b x ≫ k ⇓ v
  E-BinOp : ∀ {e₁ e₂ k v ⊗} → e₁ ≫ ⟦ ⊗ <$ e₂ ⟧≫ k ⇓ v → op ⊗ e₁ e₂ ≫ k ⇓ v
  E-If : ∀ {e₁ e₂ e₃ k v} → e₁ ≫ ⟦ if⋆then e₂ else e₃ ⟧≫ k ⇓ v → if e₁ then e₂ else e₃ ≫ k ⇓ v
