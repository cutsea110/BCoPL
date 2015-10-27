module BCoPL.EvalML5 where

open import Data.Bool using (Bool; true; false) renaming (if_then_else_ to _¿_∶_) public
open import Data.Integer public
open import Data.Nat hiding (_<_; _+_; _*_) renaming (suc to S; zero to Z)
open import Data.Product using (_×_;_,_) public
open import Data.String using (String; _==_) public

open import Relation.Binary.Core public
open import Relation.Binary.PropositionalEquality using (refl;_≡_) public

Var = String
data Value : Set
BindedValue = Var × Value
data Exp : Set

data Prim : Set where
  prim⊕ : Prim
  prim⊝ : Prim
  prim⊛ : Prim
  prim≺ : Prim

data Env : Set where
  ● : Env
  _⊱_ : Env → BindedValue → Env

data Pat : Set where
  var : Var → Pat
  [] : Pat
  _∷_ : Pat → Pat → Pat
  ̱ : Pat

data Clauses : Set where
  _↦_ : Pat → Exp → Clauses
  _↦_∣_ : Pat → Exp → Clauses → Clauses

data Exp where
  i : ℤ → Exp
  b : Bool → Exp
  var : Var → Exp
  op : Prim → Exp → Exp → Exp
  if_then_else_ : Exp → Exp → Exp → Exp
  ℓet_≔_ιn_ : Var → Exp → Exp → Exp
  ℓetrec_≔fun_⇒_ιn_ : Var → Var → Exp → Exp → Exp
  fun_⇒_ : Var → Exp → Exp
  app : Exp → Exp → Exp
  [] : Exp
  _∷_ : Exp → Exp → Exp
  match_ωith_ : Exp → Clauses → Exp

data Value where
  error : Value
  i : ℤ → Value
  b : Bool → Value
  ⟨_⟩[fun_⇒_] : Env → Var → Exp → Value
  ⟨_⟩[rec_≔fun_⇒_] : Env → Var → Var → Exp → Value
  [] : Value
  _∷_ : Value → Value → Value

_⊕_ = op prim⊕
_⊝_ = op prim⊝
_⊛_ = op prim⊛
_≺_ = op prim≺

infixl 21 _⨄_
infixl 20 _⊱_

infixl 10 _⊛_
infixl 9 _⊕_ _⊝_
infix 8 _≺_
infixr 7 _∷_
infix 6 if_then_else_ ℓet_≔_ιn_ fun_⇒_ ℓetrec_≔fun_⇒_ιn_ match_ωith_ _matches_when⟨_⟩ _doesn't-match_
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

_⨄_ : Env → Env → Env
ε₁ ⨄ ● = ε₁
ε₁ ⨄ (ε₂ ⊱ x) = ε₁ ⨄ ε₂ ⊱ x

data _matches_when⟨_⟩ : Pat → Value → Env → Set where
  M-Var : ∀ {x v} → var x matches v when⟨ ● ⊱ (x , v) ⟩
  M-Nil : [] matches [] when⟨ ● ⟩
  M-Cons : ∀ {ε ε₁ ε₂ p₁ p₂ v₁ v₂}
           → p₁ matches v₁ when⟨ ε₁ ⟩
           → p₂ matches v₂ when⟨ ε₂ ⟩
           → ε ≡ ε₁ ⨄ ε₂
           → p₁ ∷ p₂ matches v₁ ∷ v₂ when⟨ ε ⟩
  M-Wild : ∀ {v} → ̱ matches v when⟨ ● ⟩

data _doesn't-match_ : Pat → Value → Set where
  NM-ConsNil : ∀ {v₁ v₂} → [] doesn't-match v₁ ∷ v₂
  NM-NilCons : ∀ {p₁ p₂} → p₁ ∷ p₂ doesn't-match []
  NM-ConsConsL : ∀ {p₁ p₂ v₁ v₂} → p₁ doesn't-match v₁ → p₁ ∷ p₂ doesn't-match v₁ ∷ v₂
  NM-ConsConsR : ∀ {p₁ p₂ v₁ v₂} → p₂ doesn't-match v₂ → p₁ ∷ p₂ doesn't-match v₁ ∷ v₂

_⟦_⟧ : Env → Var → Value
● ⟦ x ⟧ = error
(ε ⊱ (x , v)) ⟦ y ⟧ = x == y ¿ v ∶ ε ⟦ y ⟧

data _⊢_⇓_ : Env → Exp → Value → Set where
  E-Int : ∀ {ε z}
          → ε ⊢ i z ⇓ i z
  E-Bool : ∀ {ε v}
           → ε ⊢ b v ⇓ b v
  E-Var : ∀ {ε x v}
          → ε ⟦ x ⟧ ≡ v → ε ⊢ var x ⇓ v
  E-Plus : ∀ {ε e₁ i₁ e₂ i₂ i₃}
           → ε ⊢ e₁ ⇓ i₁
           → ε ⊢ e₂ ⇓ i₂
           → i₁ plus i₂ is i₃
           → ε ⊢ e₁ ⊕ e₂ ⇓ i₃
  E-Minus : ∀ {ε e₁ i₁ e₂ i₂ i₃}
            → ε ⊢ e₁ ⇓ i₁
            → ε ⊢ e₂ ⇓ i₂
            → i₁ minus i₂ is i₃
            → ε ⊢ e₁ ⊝ e₂ ⇓ i₃
  E-Times : ∀ {ε e₁ i₁ e₂ i₂ i₃}
            → ε ⊢ e₁ ⇓ i₁
            → ε ⊢ e₂ ⇓ i₂
            → i₁ times i₂ is i₃
            → ε ⊢ e₁ ⊛ e₂ ⇓ i₃
  E-Lt : ∀ {ε e₁ i₁ e₂ i₂ b₃}
         → ε ⊢ e₁ ⇓ i₁
         → ε ⊢ e₂ ⇓ i₂
         → i₁ less-than i₂ is b₃
         → ε ⊢ e₁ ≺ e₂ ⇓ b₃
  E-IfT : ∀ {ε e₁ e₂ e₃ v}
          → ε ⊢ e₁ ⇓ b true
          → ε ⊢ e₂ ⇓ v
          → ε ⊢ if e₁ then e₂ else e₃ ⇓ v
  E-IfF : ∀ {ε e₁ e₂ e₃ v}
          → ε ⊢ e₁ ⇓ b false
          → ε ⊢ e₃ ⇓ v
          → ε ⊢ if e₁ then e₂ else e₃ ⇓ v
  E-Let : ∀ {ε x e₁ e₂ v v₁}
          → ε ⊢ e₁ ⇓ v₁
          → ε ⊱ (x , v₁) ⊢ e₂ ⇓ v
          → ε ⊢ ℓet x ≔ e₁ ιn e₂ ⇓ v
  E-LetRec : ∀ {ε x y e₁ e₂ v}
             → ε ⊱ (x , ⟨ ε ⟩[rec x ≔fun y ⇒ e₁ ]) ⊢ e₂ ⇓ v
             → ε ⊢ ℓetrec x ≔fun y ⇒ e₁ ιn e₂ ⇓ v
  E-Fun : ∀ {ε x e}
          → ε ⊢ fun x ⇒ e ⇓ ⟨ ε ⟩[fun x ⇒ e ]
  E-App : ∀ {ε ε₂ e₀ e₁ e₂ x v v₂}
          → ε ⊢ e₁ ⇓ ⟨ ε₂ ⟩[fun x ⇒ e₀ ]
          → ε ⊢ e₂ ⇓ v₂ → ε₂ ⊱ (x , v₂) ⊢ e₀ ⇓ v
          → ε ⊢ app e₁ e₂ ⇓ v
  E-AppRec : ∀ {ε ε₂ e₀ e₁ e₂ x y v v₂} →
             ε ⊢ e₁ ⇓ ⟨ ε₂ ⟩[rec x ≔fun y ⇒ e₀ ]
             → ε ⊢ e₂ ⇓ v₂
             → ε₂ ⊱ (x , ⟨ ε₂ ⟩[rec x ≔fun y ⇒ e₀ ]) ⊱ (y , v₂) ⊢ e₀ ⇓ v
             → ε ⊢ app e₁ e₂ ⇓ v

  E-Nil : ∀ {ε} → ε ⊢ [] ⇓ []
  E-Cons : ∀ {ε e₁ e₂ v₁ v₂}
           → ε ⊢ e₁ ⇓ v₁
           → ε ⊢ e₂ ⇓ v₂
           → ε ⊢ e₁ ∷ e₂ ⇓ v₁ ∷ v₂
  E-MatchM1 : ∀ {ε ε₁ ε₂ e e₀ e₁ p v v'}
              → ε ⊢ e₁ ⇓ v
              → p matches v when⟨ ε₁ ⟩
              → ε₂ ≡ ε ⨄ ε₁
              → ε₂ ⊢ e ⇓ v'
              → ε ⊢ match e₀ ωith p ↦ e ⇓ v'
  E-MatchM2 : ∀ {ε ε₁ ε₂ e e₀ p v v' c}
              → ε ⊢ e₀ ⇓ v
              → p matches v when⟨ ε₁ ⟩
              → ε₂ ≡ ε ⨄ ε₁
              → ε₂ ⊢ e ⇓ v'
              → ε ⊢ match e₀ ωith p ↦ e ∣ c ⇓ v'
  E-MatchN : ∀ {ε e e₀ p v v' c}
             → ε ⊢ e₀ ⇓ v
             → p doesn't-match v
             → ε ⊢ match e₀ ωith c ⇓ v'
             → ε ⊢ match e₀ ωith p ↦ e ∣ c ⇓ v'
