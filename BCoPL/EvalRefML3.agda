module BCoPL.EvalRefML3 where

open import Data.Bool using (Bool; true; false; not) renaming (if_then_else_ to _¿_∶_) public
open import Data.Integer public
open import Data.List public
open import Data.Nat hiding (_<_; _+_; _*_) renaming (suc to S; zero to Z)
open import Data.Product using (_×_;_,_;proj₁) public
open import Data.String using (String; _==_) public

open import Relation.Binary.Core public
open import Relation.Binary.PropositionalEquality using (refl;_≡_) public

Var = String
Loc = String
data Value : Set
BindedValue = Var × Value
StoredValue = Loc × Value

data Prim : Set where
  prim⊕ : Prim
  prim⊝ : Prim
  prim⊛ : Prim
  prim≺ : Prim

data Env : Set where
  ● : Env
  _⊱_ : Env → BindedValue → Env

data Store : Set where
  ● : Store
  _⊱_ : Store → StoredValue → Store

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
  ref : Exp → Exp
  ! : Exp → Exp
  _≔_ : Exp → Exp → Exp

data Value where
  error : Value
  i : ℤ → Value
  b : Bool → Value
  ℓ : Loc → Value
  ⟨_⟩[fun_⇒_] : Env → Var → Exp → Value
  ⟨_⟩[rec_≔fun_⇒_] : Env → Var → Var → Exp → Value

_⊕_ = op prim⊕
_⊝_ = op prim⊝
_⊛_ = op prim⊛
_≺_ = op prim≺

infixl 20 _⊱_

infixl 9 _⊛_
infixl 8 _⊕_ _⊝_
infix 7 _≺_
infix 6 if_then_else_ ℓet_≔_ιn_ fun_⇒_ ℓetrec_≔fun_⇒_ιn_
infixl 5 _╱_⊢_⇓_╱_
infixr 4 _≔_

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

_⟦_⟧ : Env → Var → Value
● ⟦ x ⟧ = error
(ε ⊱ (x , v)) ⟦ y ⟧ = x == y ¿ v ∶ ε ⟦ y ⟧

_〖_〗 : Store → Loc → Value
● 〖 x 〗 = error
(s ⊱ (x , v)) 〖 y 〗 = x == y ¿ v ∶ s 〖 y 〗

dom : Store → List Loc
dom ● = []
dom (s ⊱ (x , v)) = dom s ∷ʳ x

_∈_ : Var → List Var → Bool
x ∈ [] = false
x ∈ (y ∷ ys) = x == y ¿ true ∶ x ∈ ys

_⟪_⇐_⟫ : Store → Loc → Value → Store
● ⟪ l' ⇐ v' ⟫ = ● ⊱ (l' , v')
(s ⊱ (l , v)) ⟪ l' ⇐ v' ⟫ = l == l' ¿ s ⊱ (l , v') ∶ (s ⟪ l' ⇐ v' ⟫) ⊱ (l , v)

data _plus_is_ : Value → Value → Value → Set where
  B-Plus : ∀ {i₁ i₂ i₃} → i₁ + i₂ ≡ i₃ → i i₁ plus i i₂ is i i₃

data _minus_is_ : Value → Value → Value → Set where
  B-Minus : ∀ {i₁ i₂ i₃} → i₁ - i₂ ≡ i₃ → i i₁ minus i i₂ is i i₃

data _times_is_ : Value → Value → Value → Set where
  B-Times : ∀ {i₁ i₂ i₃} → i₁ * i₂ ≡ i₃ → i i₁ times i i₂ is i i₃

data _less-than_is_ : Value → Value → Value → Set where
  B-Lt : ∀ {i₁ i₂ v} → i₁ < i₂ ≡ v → i i₁ less-than i i₂ is b v

data _╱_⊢_⇓_╱_ : Store → Env → Exp → Value → Store → Set where
  E-Int : ∀ {S ε n}
          → S ╱ ε ⊢ i n ⇓ i n ╱ S
  E-Bool : ∀ {S ε x}
           → S ╱ ε ⊢ b x ⇓ b x ╱ S
  E-IfT : ∀ {S₁ S₂ S₃ ε e₁ e₂ e₃ v}
          → S₁ ╱ ε ⊢ e₁ ⇓ b true ╱ S₂
          → S₂ ╱ ε ⊢ e₂ ⇓ v ╱ S₃
          → S₁ ╱ ε ⊢ if e₁ then e₂ else e₃ ⇓ v ╱ S₃
  E-IfF : ∀ {S₁ S₂ S₃ ε e₁ e₂ e₃ v}
          → S₁ ╱ ε ⊢ e₁ ⇓ b false ╱ S₂
          → S₂ ╱ ε ⊢ e₃ ⇓ v ╱ S₃
          → S₁ ╱ ε ⊢ if e₁ then e₂ else e₃ ⇓ v ╱ S₃
  E-Plus : ∀ {S₁ S₂ S₃ ε i₁ i₂ i₃ e₁ e₂}
           → S₁ ╱ ε ⊢ e₁ ⇓ i₁ ╱ S₂
           → S₂ ╱ ε ⊢ e₂ ⇓ i₂ ╱ S₃
           → i₁ plus i₂ is i₃
           → S₁ ╱ ε ⊢ e₁ ⊕ e₂ ⇓ i₃ ╱ S₃
  E-Minus : ∀ {S₁ S₂ S₃ ε i₁ i₂ i₃ e₁ e₂}
            → S₁ ╱ ε ⊢ e₁ ⇓ i₁ ╱ S₂
            → S₂ ╱ ε ⊢ e₂ ⇓ i₂ ╱ S₃
            → i₁ minus i₂ is i₃
            → S₁ ╱ ε ⊢ e₁ ⊝ e₂ ⇓ i₃ ╱ S₃
  E-Mult : ∀ {S₁ S₂ S₃ ε i₁ i₂ i₃ e₁ e₂}
           → S₁ ╱ ε ⊢ e₁ ⇓ i₁ ╱ S₂
           → S₂ ╱ ε ⊢ e₂ ⇓ i₂ ╱ S₃
           → i₁ times i₂ is i₃
           → S₁ ╱ ε ⊢ e₁ ⊛ e₂ ⇓ i₃ ╱ S₃
  E-Lt : ∀ {S₁ S₂ S₃ ε i₁ i₂ i₃ e₁ e₂}
         → S₁ ╱ ε ⊢ e₁ ⇓ i₁ ╱ S₂
         → S₂ ╱ ε ⊢ e₂ ⇓ i₂ ╱ S₃
         → i₁ less-than i₂ is i₃
         → S₁ ╱ ε ⊢ e₁ ≺ e₂ ⇓ i₃ ╱ S₃
  E-Var : ∀ {S ε x v}
          → ε ⟦ x ⟧ ≡ v
          → S ╱ ε ⊢ var x ⇓ v ╱ S
  E-Let : ∀ {S₁ S₂ S₃ ε e₁ e₂ x v₁ v}
          → S₁ ╱ ε ⊢ e₁ ⇓ v₁ ╱ S₂
          → S₂ ╱ ε ⊱ (x , v₁) ⊢ e₂ ⇓ v ╱ S₃
          → S₁ ╱ ε ⊢ ℓet x ≔ e₁ ιn e₂ ⇓ v ╱ S₃
  E-Fun : ∀ {S ε x e}
          → S ╱ ε ⊢ fun x ⇒ e ⇓ ⟨ ε ⟩[fun x ⇒ e ] ╱ S
  E-App : ∀ {S₁ S₂ S₃ S₄ ε ε₂ x e₀ e₁ e₂ v v₂}
          → S₁ ╱ ε ⊢ e₁ ⇓ ⟨ ε₂ ⟩[fun x ⇒ e₀ ] ╱ S₂
          → S₂ ╱ ε ⊢ e₂ ⇓ v₂ ╱ S₃
          → S₃ ╱ ε₂ ⊱ (x , v₂) ⊢ e₀ ⇓ v ╱ S₄
          → S₁ ╱ ε ⊢ app e₁ e₂ ⇓ v ╱ S₄
  E-LetRec : ∀ {S₁ S₂ ε x y e₁ e₂ v}
             → S₁ ╱ ε ⊱ (x , ⟨ ε ⟩[rec x ≔fun y ⇒ e₁ ]) ⊢ e₂ ⇓ v ╱ S₂
             → S₁ ╱ ε ⊢ ℓetrec x ≔fun y ⇒ e₁ ιn e₂ ⇓ v ╱ S₂
  E-AppRec : ∀ {S₁ S₂ S₃ S₄ ε ε₂ x y v v₂ e₀ e₁ e₂}
             → S₁ ╱ ε ⊢ e₁ ⇓ ⟨ ε₂ ⟩[rec x ≔fun y ⇒ e₀ ] ╱ S₂
             → S₂ ╱ ε ⊢ e₂ ⇓ v₂ ╱ S₃
             → S₃ ╱ ε₂ ⊱ (x , ⟨ ε₂ ⟩[rec x ≔fun y ⇒ e₀ ]) ⊱ (y , v₂) ⊢ e₀ ⇓ v ╱ S₄
             → S₁ ╱ ε ⊢ app e₁ e₂ ⇓ v ╱ S₄
  E-Ref : ∀ {S₁ S₂ ε e v l}
          → S₁ ╱ ε ⊢ e ⇓ v ╱ S₂
          → l ∈ dom S₂ ≡ false
          → S₁ ╱ ε ⊢ ref e ⇓ ℓ l ╱ S₂ ⊱ (l , v)
  E-Deref : ∀ {S₁ S₂ ε e l v}
            → S₁ ╱ ε ⊢ e ⇓ ℓ l ╱ S₂
            → S₂ 〖 l 〗 ≡ v
            → S₁ ╱ ε ⊢ ! e ⇓ v ╱ S₂
  E-Assign : ∀ {S₁ S₂ S₃ S₄ ε e₁ e₂ l v}
             → S₁ ╱ ε ⊢ e₁ ⇓ ℓ l ╱ S₂
             → S₂ ╱ ε ⊢ e₂ ⇓ v ╱ S₃
             → S₄ ≡ S₃ ⟪ l ⇐ v ⟫
             → S₁ ╱ ε ⊢ e₁ ≔ e₂ ⇓ v ╱ S₄
