module BCoPL.EvalML4Err where

open import Data.Bool using (Bool; true; false; not) renaming (if_then_else_ to _¿_∶_) public
open import Data.Integer hiding (_<_) public
open import Data.Nat hiding (_<_; _+_; _*_) renaming (suc to S; zero to Z)
open import Data.Product using (_×_;_,_) public
open import Data.String using (String; _==_) renaming (_≟_ to _=?=_) public
open import Data.Sum renaming (_⊎_ to _∨_; inj₁ to left; inj₂ to right) public
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)

open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.Core public
open import Relation.Binary.PropositionalEquality using (refl;_≡_) public

Var = String
data Val : Set
data Error : Set where
  error : Error
Value = Error ∨ Val
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
  [] : Exp
  _∷_ : Exp → Exp → Exp
  match_with[]⇒_∣_∷_⇒_ : Exp → Exp → Var → Var → Exp → Exp


data Val where
  i : ℤ → Val
  b : Bool → Val
  ⟨_⟩[fun_⇒_] : Env → Var → Exp → Val
  ⟨_⟩[rec_≔fun_⇒_] : Env → Var → Var → Exp → Val
  [] : Val
  _∷_ : Val → Val → Val

_⊕_ = op prim⊕
_⊝_ = op prim⊝
_⊛_ = op prim⊛
_≺_ = op prim≺

infixl 20 _⊱_

infixl 10 _⊛_
infixl 9 _⊕_ _⊝_
infix 8 _≺_
infixr 7 _∷_
infix 6 if_then_else_ ℓet_≔_ιn_ fun_⇒_ ℓetrec_≔fun_⇒_ιn_ match_with[]⇒_∣_∷_⇒_
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

_∈_ : Var → Env → Set
x ∈ ● = ⊥
x ∈ (ε ⊱ (y , v)) with x =?= y -- ¿ ⊤ ∶ x ∈ ε
x ∈ (ε ⊱ (.x , v)) | yes refl = ⊤
x ∈ (ε ⊱ (y , v)) | no ¬p = x ∈ ε

_∉_ : Var → Env → Set
x ∉ ε = ¬ x ∈ ε

isℤ : Val → Set
isℤ (i x) = ⊤
isℤ (b x) = ⊥
isℤ ⟨ x ⟩[fun x₁ ⇒ x₂ ] = ⊥
isℤ ⟨ x ⟩[rec x₁ ≔fun x₂ ⇒ x₃ ] = ⊥
isℤ [] = ⊥
isℤ (v ∷ v₁) = ⊥

isBool : Val → Set
isBool (i x) = ⊥
isBool (b x) = ⊤
isBool ⟨ x ⟩[fun x₁ ⇒ x₂ ] = ⊥
isBool ⟨ x ⟩[rec x₁ ≔fun x₂ ⇒ x₃ ] = ⊥
isBool [] = ⊥
isBool (v ∷ v₁) = ⊥

isClosure : Val → Set
isClosure (i x) = ⊥
isClosure (b x) = ⊥
isClosure ⟨ x ⟩[fun x₁ ⇒ x₂ ] = ⊤
isClosure ⟨ x ⟩[rec x₁ ≔fun x₂ ⇒ x₃ ] = ⊤
isClosure [] = ⊥
isClosure (v ∷ v₁) = ⊥

isList : Val → Set
isList (i x) = ⊥
isList (b x) = ⊥
isList ⟨ x ⟩[fun x₁ ⇒ x₂ ] = ⊥
isList ⟨ x ⟩[rec x₁ ≔fun x₂ ⇒ x₃ ] = ⊥
isList [] = ⊤
isList (v ∷ v₁) = ⊤

data _plus_is_ : Value → Value → Value → Set where
  B-Plus : ∀ {i₁ i₂ i₃} → i₁ + i₂ ≡ i₃ → right (i i₁) plus right (i i₂) is right (i i₃)

data _minus_is_ : Value → Value → Value → Set where
  B-Minus : ∀ {i₁ i₂ i₃} → i₁ - i₂ ≡ i₃ → right (i i₁) minus right (i i₂) is right (i i₃)

data _times_is_ : Value → Value → Value → Set where
  B-Times : ∀ {i₁ i₂ i₃} → i₁ * i₂ ≡ i₃ → right (i i₁) times right (i i₂) is right (i i₃)

data _less-than_is_ : Value → Value → Value → Set where
  B-Lt : ∀ {i₁ i₂ v} → i₁ < i₂ ≡ v → right (i i₁) less-than right (i i₂) is right (b v)

_⟦_⟧ : Env → Var → Value
● ⟦ x ⟧ = left error
(ε ⊱ (y , v)) ⟦ x ⟧ with y =?= x
(ε ⊱ (x , v)) ⟦ .x ⟧ | yes refl = v
(ε ⊱ (y , v)) ⟦ x ⟧ | no ¬p = ε ⟦ x ⟧

data _⊢_⇓_ : Env → Exp → Value → Set where
  E-Int : ∀ {ε z}
          → ε ⊢ i z ⇓ right (i z)
  E-Bool : ∀ {ε v}
           → ε ⊢ b v ⇓ right (b v)
  E-Var : ∀ {ε x v}
          → ε ⟦ x ⟧ ≡ right v → ε ⊢ var x ⇓ right v
  E-VarErr : ∀ {ε x}
             → {x∉ε : x ∉ ε}
             → ε ⊢ var x ⇓ left error
  E-Plus : ∀ {ε e₁ i₁ e₂ i₂ i₃}
           → ε ⊢ e₁ ⇓ right i₁
           → ε ⊢ e₂ ⇓ right i₂
           → right i₁ plus right i₂ is right i₃
           → ε ⊢ e₁ ⊕ e₂ ⇓ right i₃
  E-PlusErr1 : ∀ {ε e₁ e₂ r}
               → ε ⊢ e₁ ⇓ right r
               → {r≢ℤ :  ¬ isℤ r}
               → ε ⊢ e₁ ⊕ e₂ ⇓ left error
  E-PlusErr2 : ∀ {ε e₁ e₂ i₁ r}
               → ε ⊢ e₁ ⇓ right i₁
               → ε ⊢ e₂ ⇓ right r
               → {r≢ℤ : ¬ isℤ r}
               → ε ⊢ e₁ ⊕ e₂ ⇓ left error
  E-Minus : ∀ {ε e₁ i₁ e₂ i₂ i₃}
            → ε ⊢ e₁ ⇓ right i₁
            → ε ⊢ e₂ ⇓ right i₂
            → right i₁ minus right i₂ is right i₃
            → ε ⊢ e₁ ⊝ e₂ ⇓ right i₃
  E-MinusErr1 : ∀ {ε e₁ e₂ r}
                → ε ⊢ e₁ ⇓ right r
                → {r≢ℤ : ¬ isℤ r}
                → ε ⊢ e₁ ⊝ e₂ ⇓ left error
  E-MinusErr2 : ∀ {ε e₁ e₂ i₁ r}
                → ε ⊢ e₁ ⇓ right i₁
                → ε ⊢ e₂ ⇓ right r
                → {r≢ℤ : ¬ isℤ r}
                → ε ⊢ e₁ ⊝ e₂ ⇓ left error
  E-Times : ∀ {ε e₁ i₁ e₂ i₂ i₃}
            → ε ⊢ e₁ ⇓ right i₁
            → ε ⊢ e₂ ⇓ right i₂
            → right i₁ times right i₂ is right i₃
            → ε ⊢ e₁ ⊛ e₂ ⇓ right i₃
  E-TimesErr1 : ∀ {ε e₁ e₂ r}
                → ε ⊢ e₁ ⇓ right r
                → {r≢ℤ : ¬ isℤ r}
                → ε ⊢ e₁ ⊛ e₂ ⇓ left error
  E-TimesErr2 : ∀ {ε e₁ e₂ i₁ r}
                → ε ⊢ e₁ ⇓ right i₁
                → ε ⊢ e₂ ⇓ right r
                → {r≢ℤ : ¬ isℤ r}
                → ε ⊢ e₁ ⊛ e₂ ⇓ left error
  E-Lt : ∀ {ε e₁ i₁ e₂ i₂ b₃}
         → ε ⊢ e₁ ⇓ right i₁
         → ε ⊢ e₂ ⇓ right i₂
         → right i₁ less-than right i₂ is right b₃
         → ε ⊢ e₁ ≺ e₂ ⇓ right b₃
  E-LtErr1 : ∀ {ε e₁ e₂ r}
             → ε ⊢ e₁ ⇓ right r
             → {r≢ℤ : ¬ isℤ r}
             → ε ⊢ e₁ ≺ e₂ ⇓ left error
  E-LtErr2 : ∀ {ε e₁ e₂ i₁ r}
             → ε ⊢ e₁ ⇓ right i₁
             → ε ⊢ e₂ ⇓ right r
             → {r≢ℤ : ¬ isℤ r}
             → ε ⊢ e₁ ≺ e₂ ⇓ left error
  E-IfT : ∀ {ε e₁ e₂ e₃ v}
          → ε ⊢ e₁ ⇓ right (b true)
          → ε ⊢ e₂ ⇓ right v
          → ε ⊢ if e₁ then e₂ else e₃ ⇓ right v
  E-IfF : ∀ {ε e₁ e₂ e₃ v}
          → ε ⊢ e₁ ⇓ right (b false)
          → ε ⊢ e₃ ⇓ right v
          → ε ⊢ if e₁ then e₂ else e₃ ⇓ right v
  E-IfErr1 : ∀ {ε e₁ e₂ e₃ r}
             → ε ⊢ e₁ ⇓ right r
             → {r≢Bool : ¬ isBool r}
             → ε ⊢ if e₁ then e₂ else e₃ ⇓ left error
  E-IfErr2 : ∀ {ε e₁ e₂ e₃}
             → ε ⊢ e₁ ⇓ right (b true)
             → ε ⊢ e₂ ⇓ left error
             → ε ⊢ if e₁ then e₂ else e₃ ⇓ left error
  E-IfErr3 : ∀ {ε e₁ e₂ e₃}
             → ε ⊢ e₁ ⇓ right (b false)
             → ε ⊢ e₃ ⇓ left error
             → ε ⊢ if e₁ then e₂ else e₃ ⇓ left error
  E-Let : ∀ {ε x e₁ e₂ v v₁}
          → ε ⊢ e₁ ⇓ right v₁
          → ε ⊱ (x , right v₁) ⊢ e₂ ⇓ right v
          → ε ⊢ ℓet x ≔ e₁ ιn e₂ ⇓ right v
  E-LetErr1 : ∀ {ε x e₁ e₂}
              → ε ⊢ e₁ ⇓ left error
              → ε ⊢ ℓet x ≔ e₁ ιn e₂ ⇓ left error
  E-LetErr2 : ∀ {ε x e₁ e₂ v₁}
              → ε ⊢ e₁ ⇓ right v₁
              → ε ⊱ (x , right v₁) ⊢ e₂ ⇓ left error
              → ε ⊢ ℓet x ≔ e₁ ιn e₂ ⇓ left error
  E-LetRec : ∀ {ε x y e₁ e₂ v}
             → ε ⊱ (x , right (⟨ ε ⟩[rec x ≔fun y ⇒ e₁ ])) ⊢ e₂ ⇓ right v
             → ε ⊢ ℓetrec x ≔fun y ⇒ e₁ ιn e₂ ⇓ right v
  E-LetRecErr : ∀ {ε x y e₁ e₂}
                → ε ⊱ (x , right (⟨ ε ⟩[rec x ≔fun y ⇒ e₁ ])) ⊢ e₂ ⇓ left error
                → ε ⊢ ℓetrec x ≔fun y ⇒ e₁ ιn e₂ ⇓ left error
  E-Fun : ∀ {ε x e}
          → ε ⊢ fun x ⇒ e ⇓ right (⟨ ε ⟩[fun x ⇒ e ])
  E-App : ∀ {ε ε₂ e₀ e₁ e₂ x v v₂}
          → ε ⊢ e₁ ⇓ right (⟨ ε₂ ⟩[fun x ⇒ e₀ ])
          → ε ⊢ e₂ ⇓ right v₂
          → ε₂ ⊱ (x , right v₂) ⊢ e₀ ⇓ right v
          → ε ⊢ app e₁ e₂ ⇓ right v
  E-AppErr1 : ∀ {ε e₁ e₂ r}
              → ε ⊢ e₁ ⇓ right r
              → {r≢Closure : ¬ isClosure r}
              → ε ⊢ app e₁ e₂ ⇓ left error
  E-AppErr2 : ∀ {ε ε₂ x e₀ e₁ e₂}
              → ε ⊢ e₁ ⇓ right (⟨ ε₂ ⟩[fun x ⇒ e₀ ])
              → ε ⊢ e₂ ⇓ left error
              → ε ⊢ app e₁ e₂ ⇓ left error
  E-AppErr3 : ∀ {ε ε₂ x y e₀ e₁ e₂}
              → ε ⊢ e₁ ⇓ right (⟨ ε₂ ⟩[rec x ≔fun y ⇒ e₀ ])
              → ε ⊢ e₂ ⇓ left error
              → ε ⊢ app e₁ e₂ ⇓ left error
  E-AppErr4 : ∀ {ε ε₂ x e₀ e₁ e₂ v₂}
              → ε ⊢ e₁ ⇓ right (⟨ ε₂ ⟩[fun x ⇒ e₀ ])
              → ε ⊢ e₂ ⇓ right v₂
              → ε₂ ⊱ (x , right v₂) ⊢ e₀ ⇓ left error
              → ε ⊢ app e₁ e₂ ⇓ left error
  E-AppErr5 : ∀ {ε ε₂ x y e₀ e₁ e₂ v₂}
              → ε ⊢ e₁ ⇓ right ⟨ ε₂ ⟩[rec x ≔fun y ⇒ e₀ ]
              → ε ⊢ e₂ ⇓ right v₂
              → ε₂ ⊱ (x , right ⟨ ε₂ ⟩[rec x ≔fun y ⇒ e₀ ]) ⊱ (y , right v₂) ⊢ e₀ ⇓ left error
              → ε ⊢ app e₁ e₂ ⇓ left error
  E-AppRec : ∀ {ε ε₂ e₀ e₁ e₂ x y v v₂} →
             ε ⊢ e₁ ⇓ right (⟨ ε₂ ⟩[rec x ≔fun y ⇒ e₀ ])
             → ε ⊢ e₂ ⇓ right v₂
             → ε₂ ⊱ (x , right (⟨ ε₂ ⟩[rec x ≔fun y ⇒ e₀ ])) ⊱ (y , right v₂) ⊢ e₀ ⇓ right v
             → ε ⊢ app e₁ e₂ ⇓ right v

  E-Nil : ∀ {ε} → ε ⊢ [] ⇓ right []
  E-Cons : ∀ {ε e₁ e₂ v₁ v₂}
           → ε ⊢ e₁ ⇓ right v₁
           → ε ⊢ e₂ ⇓ right v₂
           → ε ⊢ e₁ ∷ e₂ ⇓ right (v₁ ∷ v₂)
  E-ConsErr1 : ∀ {ε e₁ e₂}
               → ε ⊢ e₁ ⇓ left error
               → ε ⊢ e₁ ∷ e₂ ⇓ left error
  E-ConsErr2 : ∀ {ε e₁ e₂ v₁}
               → ε ⊢ e₁ ⇓ right v₁
               → ε ⊢ e₂ ⇓ left error
               → ε ⊢ e₁ ∷ e₂ ⇓ left error
  E-MatchNil : ∀ {ε e₁ e₂ e₃ x y v}
               → ε ⊢ e₁ ⇓ right []
               → ε ⊢ e₂ ⇓ right v
               → ε ⊢ match e₁ with[]⇒ e₂ ∣ x ∷ y ⇒ e₃ ⇓ right v
  E-MatchCons : ∀ {ε e₁ e₂ e₃ x y v₁ v₂ v}
                → ε ⊢ e₁ ⇓ right (v₁ ∷ v₂)
                → ε ⊱ (x , right v₁) ⊱ (y , right v₂) ⊢ e₃ ⇓ right v
                → ε ⊢ match e₁ with[]⇒ e₂ ∣ x ∷ y ⇒ e₃ ⇓ right v
  E-MatchErr1 : ∀ {ε x y e₁ e₂ e₃ r}
                → ε ⊢ e₁ ⇓ right r
                → {r≢List :  ¬ isList r }
                → ε ⊢ match e₁ with[]⇒ e₂ ∣ x ∷ y ⇒ e₃ ⇓ left error
  E-MatchErr2 : ∀ {ε x y e₁ e₂ e₃}
                → ε ⊢ e₁ ⇓ right []
                → ε ⊢ e₂ ⇓ left error
                → ε ⊢ match e₁ with[]⇒ e₂ ∣ x ∷ y ⇒ e₃ ⇓ left error
  E-MatchErr3 : ∀ {ε x y e₁ e₂ e₃ v₁ v₂}
                → ε ⊢ e₁ ⇓ right (v₁ ∷ v₂)
                → ε ⊱ (x , right v₁) ⊱ (y , right v₂) ⊢ e₃ ⇓ left error
                → ε ⊢ match e₁ with[]⇒ e₂ ∣ x ∷ y ⇒ e₃ ⇓ left error
