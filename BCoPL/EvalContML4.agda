module BCoPL.EvalContML4 where

open import Data.Bool using (Bool; true; false; not) renaming (if_then_else_ to _¿_∶_) public
open import Data.Integer hiding (_<_) public
open import Data.Nat hiding (_<_; _+_; _*_) renaming (suc to S; zero to Z)
open import Data.Product using (_×_;_,_) public
open import Data.String using (String; _==_) public

open import Relation.Binary.Core public
open import Relation.Binary.PropositionalEquality using (refl;_≡_) public

Var = String
data Value : Set
BindedValue = Var × Value
data Cont : Set

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
  [] : Exp
  _∷_ : Exp → Exp → Exp
  match_with[]⇒_∣_∷_⇒_ : Exp → Exp → Var → Var → Exp → Exp
  letcc_ιn_ : Var → Exp → Exp


data Value where
  error : Value
  i : ℤ → Value
  b : Bool → Value
  ⟨_⟩[fun_⇒_] : Env → Var → Exp → Value
  ⟨_⟩[rec_≔fun_⇒_] : Env → Var → Var → Exp → Value
  [] : Value
  _∷_ : Value → Value → Value
  ⟪_⟫ : Cont → Value

data Section : Set where
  _⊢_<$_ : Env → Prim → Exp → Section
  _$>_ : Value → Prim → Section
  _⊢if⋆then_else_ : Env → Exp → Exp → Section
  _⊢let_≔⋆in_ : Env → Var → Exp → Section
  _⊢app⋆_ : Env → Exp → Section
  _⋆ppa : Value → Section
  _⊢⋆∷_ : Env → Exp → Section
  _∷⋆ : Value → Section
  _⊢match⋆with[]⇒_∣_∷_⇒_ : Env → Exp → Var → Var → Exp → Section

_⊢⋆⊕_ : Env → Exp → Section
ε ⊢⋆⊕ e = ε ⊢ prim⊕ <$ e
_⊕⋆ : Value → Section
v ⊕⋆ = v $> prim⊕
_⊢⋆⊝_ : Env → Exp → Section
ε ⊢⋆⊝ e = ε ⊢ prim⊝ <$ e
_⊝⋆ : Value → Section
v ⊝⋆ = v $> prim⊝
_⊢⋆⊛_ : Env → Exp → Section
ε ⊢⋆⊛ e = ε ⊢ prim⊛ <$ e
_⊛⋆ : Value → Section
v ⊛⋆ = v $> prim⊛
_⊢⋆≺_ : Env → Exp → Section
ε ⊢⋆≺ e = ε ⊢ prim≺ <$ e
_≺⋆ : Value → Section
v ≺⋆ = v $> prim≺

_⊕_ = op prim⊕
_⊝_ = op prim⊝
_⊛_ = op prim⊛
_≺_ = op prim≺

data Cont where
  ⋆ : Cont
  ⟦_⟧≫_ : Section → Cont → Cont

infixl 20 _⊱_

infixl 10 _⊛_
infixl 9 _⊕_ _⊝_
infix 8 _≺_
infixr 7 _∷_
infix 6 if_then_else_ ℓet_≔_ιn_ fun_⇒_ ℓetrec_≔fun_⇒_ιn_ match_with[]⇒_∣_∷_⇒_
infixr 6 ⟦_⟧≫_
infix 6 _⊢_<$_ _$>_ _⊢if⋆then_else_ _⊢let_≔⋆in_ _⊢app⋆_ _⋆ppa _⊢⋆∷_ _∷⋆ _⊢match⋆with[]⇒_∣_∷_⇒_
infixl 5 _⇒_⇓_ _⊢_≫_⇓_

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

_⟦_⟧ : Env → Var → Value
● ⟦ x ⟧ = error
(ε ⊱ (x , v)) ⟦ y ⟧ = x == y ¿ v ∶ ε ⟦ y ⟧

data _⇒_⇓_ : Value → Cont → Value → Set
data _⊢_≫_⇓_ : Env → Exp → Cont → Value → Set

data _⇒_⇓_ where
  C-Ret : ∀ {v}
          → v ⇒ ⋆ ⇓ v
  C-EvalR : ∀ {ε e v₁ v₂ k ⊗}
            → ε ⊢ e ≫ ⟦ v₁ $> ⊗ ⟧≫ k ⇓ v₂
            → v₁ ⇒ ⟦ ε ⊢ ⊗ <$ e ⟧≫ k ⇓ v₂
  C-Plus : ∀ {i₁ i₂ i₃ k v}
           → i₁ plus i₂ is i₃
           → i₃ ⇒ k ⇓ v
           → i₂ ⇒ ⟦ i₁ ⊕⋆ ⟧≫ k ⇓ v
  C-Minus : ∀ {i₁ i₂ i₃ k v}
            → i₁ minus i₂ is i₃
            → i₃ ⇒ k ⇓ v
            → i₂ ⇒ ⟦ i₁ ⊝⋆ ⟧≫ k ⇓ v
  C-Times : ∀ {i₁ i₂ i₃ k v}
            → i₁ times i₂ is i₃
            → i₃ ⇒ k ⇓ v
            → i₂ ⇒ ⟦ i₁ ⊛⋆ ⟧≫ k ⇓ v
  C-Lt : ∀ {i₁ i₂ i₃ k v}
         → i₁ less-than i₂ is i₃
         → i₃ ⇒ k ⇓ v
         → i₂ ⇒ ⟦ i₁ ≺⋆ ⟧≫ k ⇓ v
  C-IfT : ∀ {ε e₁ e₂ k v}
          → ε ⊢ e₁ ≫ k ⇓ v
          → b true ⇒ ⟦ ε ⊢if⋆then e₁ else e₂ ⟧≫ k ⇓ v
  C-IfF : ∀ {ε e₁ e₂ k v}
          → ε ⊢ e₂ ≫ k ⇓ v
          → b false ⇒ ⟦ ε ⊢if⋆then e₁ else e₂ ⟧≫ k ⇓ v
  C-LetBody : ∀ {ε x v₁ v₂ e k}
              → ε ⊱ (x , v₁) ⊢ e ≫ k ⇓ v₂
              → v₁ ⇒ ⟦ ε ⊢let x ≔⋆in e ⟧≫ k ⇓ v₂
  C-EvalArg : ∀ {ε e k v v₁}
              → ε ⊢ e ≫ ⟦ v₁ ⋆ppa ⟧≫ k ⇓ v
              → v₁ ⇒ ⟦ ε ⊢app⋆ e ⟧≫ k ⇓ v
  C-EvalFun : ∀ {ε x e v₁ v₂ k}
              → ε ⊱ (x , v₁) ⊢ e ≫ k ⇓ v₂
              → v₁ ⇒ ⟦ ⟨ ε ⟩[fun x ⇒ e ] ⋆ppa ⟧≫ k ⇓ v₂
  C-EvalFunR : ∀ {ε x y v₁ v₂ e k}
               → ε ⊱ (x , ⟨ ε ⟩[rec x ≔fun y ⇒ e ]) ⊱ (y , v₁) ⊢ e ≫ k ⇓ v₂
               → v₁ ⇒ ⟦ ⟨ ε ⟩[rec x ≔fun y ⇒ e ] ⋆ppa ⟧≫ k ⇓ v₂
  C-EvalConsR : ∀ {ε v₁ v₂ e k}
                → ε ⊢ e ≫ ⟦ v₁ ∷⋆ ⟧≫ k ⇓ v₂
                → v₁ ⇒ ⟦ ε ⊢⋆∷ e ⟧≫ k ⇓ v₂
  C-Cons : ∀ {v₁ v₂ v₃ k}
           → v₁ ∷ v₂ ⇒ k ⇓ v₃
           → v₂ ⇒ ⟦ v₁ ∷⋆ ⟧≫ k ⇓ v₃
  C-MatchNil : ∀ {ε x y e₁ e₂ k v}
               → ε ⊢ e₁ ≫ k ⇓ v
               → [] ⇒ ⟦ ε ⊢match⋆with[]⇒ e₁ ∣ x ∷ y ⇒ e₂ ⟧≫ k ⇓ v
  C-MatchCons : ∀ {ε x y v₁ v₂ e₁ e₂ k v}
                → ε ⊱ (x , v₁) ⊱ (y , v₂) ⊢ e₂ ≫ k ⇓ v
                → v₁ ∷ v₂ ⇒ ⟦ ε ⊢match⋆with[]⇒ e₁ ∣ x ∷ y ⇒ e₂ ⟧≫ k ⇓ v
  C-EvalFunC : ∀ {v₁ v₂ k₁ k₂}
               → v₁ ⇒ k₁ ⇓ v₂
               → v₁ ⇒ ⟦ ⟪ k₁ ⟫ ⋆ppa ⟧≫ k₂ ⇓ v₂

data _⊢_≫_⇓_ where
  E-Int : ∀ {n k v ε}
          → i n ⇒ k ⇓ v
          → ε ⊢ i n ≫ k ⇓ v
  E-Bool : ∀ {x k v ε}
           → b x ⇒ k ⇓ v
           → ε ⊢ b x ≫ k ⇓ v
  E-If : ∀ {ε e₁ e₂ e₃ k v}
         → ε ⊢ e₁ ≫ ⟦ ε ⊢if⋆then e₂ else e₃ ⟧≫ k ⇓ v
         → ε ⊢ if e₁ then e₂ else e₃ ≫ k ⇓ v
  E-BinOp : ∀ {ε e₁ e₂ k v ⊗}
            → ε ⊢ e₁ ≫ ⟦ ε ⊢ ⊗ <$ e₂ ⟧≫ k ⇓ v
            → ε ⊢ op ⊗ e₁ e₂ ≫ k ⇓ v
  E-Var : ∀ {ε x v₁ v₂ k}
          → ε ⟦ x ⟧ ≡ v₁
          → v₁ ⇒ k ⇓ v₂
          → ε ⊢ var x ≫ k ⇓ v₂
  E-Let : ∀ {ε e₁ e₂ x k v}
          → ε ⊢ e₁ ≫ ⟦ ε ⊢let x ≔⋆in e₂ ⟧≫ k ⇓ v
          → ε ⊢ ℓet x ≔ e₁ ιn e₂ ≫ k ⇓ v
  E-Fun : ∀ {ε e x k v}
          → ⟨ ε ⟩[fun x ⇒ e ] ⇒ k ⇓ v
          → ε ⊢ fun x ⇒ e ≫ k ⇓ v
  E-App : ∀ {ε e₁ e₂ k v}
          → ε ⊢ e₁ ≫ ⟦ ε ⊢app⋆ e₂ ⟧≫ k ⇓ v
          → ε ⊢ app e₁ e₂ ≫ k ⇓ v
  E-LetRec : ∀ {ε x y e₁ e₂ k v}
             → ε ⊱ (x , ⟨ ε ⟩[rec x ≔fun y ⇒ e₁ ]) ⊢ e₂ ≫ k ⇓ v
             → ε ⊢ ℓetrec x ≔fun y ⇒ e₁ ιn e₂ ≫ k ⇓ v
  E-Nil : ∀ {ε k v}
          → [] ⇒ k ⇓ v
          → ε ⊢ [] ≫ k ⇓ v
  E-Cons : ∀ {ε e₁ e₂ k v}
           → ε ⊢ e₁ ≫ ⟦ ε ⊢⋆∷ e₂ ⟧≫ k ⇓ v
           → ε ⊢ e₁ ∷ e₂ ≫ k ⇓ v
  E-Match : ∀ {ε e₁ e₂ e₃ x y k v}
            → ε ⊢ e₁ ≫ ⟦ ε ⊢match⋆with[]⇒ e₂ ∣ x ∷ y ⇒ e₃ ⟧≫ k ⇓ v
            → ε ⊢ match e₁ with[]⇒ e₂ ∣ x ∷ y ⇒ e₃ ≫ k ⇓ v
  E-LetCc : ∀ {ε x e k v}
            → ε ⊱ (x , ⟪ k ⟫) ⊢ e ≫ k ⇓ v
            → ε ⊢ letcc x ιn e ≫ k ⇓ v
