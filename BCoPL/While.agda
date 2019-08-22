module BCoPL.While where

open import Data.Integer hiding (_<_) public
open import Data.Bool using (Bool; true; false) renaming (if_then_else_ to _¿_∶_) public
open import Data.Nat hiding (_<_; _+_; _*_) renaming (suc to S; zero to Z)
open import Data.Product using (_×_; _,_) public
open import Data.String using (String) renaming (_==_ to _==S_) public
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
  error : IValue
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
  while_𝑑𝑜_ : BExp → Com → Com

_⊕_ = aop prim⊕
_⊝_ = aop prim⊝
_⊛_ = aop prim⊛
_≺_ = comp prim≺
_≈_ = comp prim≈
_≼_ = comp prim≼
_&&_ = lop prim&&
_||_ = lop prim||

infixl 20 _⊱_

infixl 9 _⊛_
infixl 8 _⊕_ _⊝_
infix 7 _≺_ _≈_ _≼_
infixl 7 _&&_ _≔_
infixl 6 _||_
infix 6 if_then_else_
infixr 5 _>>_
infix 4 _⊢_⇓_ _⊢_↓_ _changes_to_

private
  _<ℕ_ : ℕ → ℕ → Bool
  Z <ℕ Z = false
  Z <ℕ S n = true
  S m <ℕ Z = false
  S m <ℕ S n = m <ℕ n

  _==ℕ_ : ℕ → ℕ → Bool
  Z ==ℕ Z = true
  Z ==ℕ S y = false
  S x ==ℕ Z = false
  S x ==ℕ S y = x ==ℕ y

  _<=ℕ_ : ℕ → ℕ → Bool
  Z <=ℕ Z = true
  Z <=ℕ S y = true
  S x <=ℕ Z = false
  S x <=ℕ S y = x <=ℕ y

  infix 7 _<ℕ_ _<_ _==ℕ_ _==_ _<=ℕ_ _<=_

  _<_ : ℤ → ℤ → Bool
  -[1+ m ] < -[1+ n ] = n <ℕ m
  -[1+ m ] < + n = true
  + m < -[1+ n ] = false
  + m < + n = m <ℕ n

  _==_ : ℤ → ℤ → Bool
  -[1+ m ] == -[1+ n ] = m ==ℕ n
  -[1+ m ] == (+ n) = false
  (+ m) == -[1+ n ] = false
  (+ m) == (+ n) = m ==ℕ n

  _<=_ : ℤ → ℤ → Bool
  -[1+ m ] <= -[1+ n ] = n <=ℕ m
  -[1+ m ] <= + n = true
  + m <= -[1+ n ] = false
  + m <= + n = m <=ℕ n

  _∧_ : Bool → Bool → Bool
  true ∧ x = x
  false ∧ _ = false

  _∨_ : Bool → Bool → Bool
  true ∨ _ = true
  false ∨ y = y

  ¬_ : Bool → Bool
  ¬ true = false
  ¬ false = true

_〖_〗 : Store → Var → IValue
● 〖 x 〗 = error
(σ ⊱ (y , v)) 〖 x 〗 = x ==S y ¿ v ∶ σ 〖 x 〗

_〖_╱_〗 : Store → IValue → Var → Store
● 〖 iv ╱ x 〗 = ● ⊱ (x , iv)
(σ ⊱ (x , v)) 〖 v' ╱ x' 〗 = x ==S x' ¿ σ ⊱ (x , v') ∶ (σ 〖 v' ╱ x' 〗) ⊱ (x , v)

data _plus_is_ : IValue → IValue → IValue → Set where
  B-Plus : ∀ {i₁ i₂ i₃} → i₁ + i₂ ≡ i₃ → i i₁ plus i i₂ is i i₃

data _minus_is_ : IValue → IValue → IValue → Set where
  B-Minus : ∀ {i₁ i₂ i₃} → i₁ - i₂ ≡ i₃ → i i₁ minus i i₂ is i i₃

data _times_is_ : IValue → IValue → IValue → Set where
  B-Times : ∀ {i₁ i₂ i₃} → i₁ * i₂ ≡ i₃ → i i₁ times i i₂ is i i₃

data _less-than_is_ : IValue → IValue → BValue → Set where
  B-Lt : ∀ {i₁ i₂ v} → i₁ < i₂ ≡ v → i i₁ less-than i i₂ is b v

data _⊢_⇓_ : Store → AExp → IValue → Set where
  A-Const : ∀ {σ n}
            → σ ⊢ i n ⇓ i n
  A-Var : ∀ {σ x i }
          → σ 〖 x 〗 ≡ i
          → σ ⊢ var x ⇓ i
  A-Plus : ∀ {σ a₁ a₂ i₁ i₂ i₃}
           → σ ⊢ a₁ ⇓ i i₁
           → σ ⊢ a₂ ⇓ i i₂
           → i₃ ≡ i₁ + i₂
           → σ ⊢ a₁ ⊕ a₂ ⇓ i i₃
  A-Minus : ∀ {σ a₁ a₂ i₁ i₂ i₃}
            → σ ⊢ a₁ ⇓ i i₁
            → σ ⊢ a₂ ⇓ i i₂
            → i₃ ≡ i₁ - i₂
            → σ ⊢ a₁ ⊝ a₂ ⇓ i i₃
  A-Times : ∀ {σ a₁ a₂ i₁ i₂ i₃}
            → σ ⊢ a₁ ⇓ i i₁
            → σ ⊢ a₂ ⇓ i i₂
            → i₃ ≡ i₁ * i₂
            → σ ⊢ a₁ ⊛ a₂ ⇓ i i₃

data _⊢_↓_ : Store → BExp → BValue → Set where
  B-Const : ∀ {σ v}
            → σ ⊢ b v ↓ b v
  B-Not : ∀ {σ b₁ bv₁ bv₂}
          → σ ⊢ b₁ ↓ b bv₁
          → bv₂ ≡ ¬ bv₁
          → σ ⊢ ! b₁ ↓ b bv₂
  B-And : ∀ {σ b₁ b₂ bv₁ bv₂ bv₃}
          → σ ⊢ b₁ ↓ b bv₁
          → σ ⊢ b₂ ↓ b bv₂
          → bv₃ ≡ bv₁ ∧ bv₂
          → σ ⊢ b₁ && b₂ ↓ b bv₃
  B-Or : ∀ {σ b₁ b₂ bv₁ bv₂ bv₃}
         → σ ⊢ b₁ ↓ b bv₁
         → σ ⊢ b₂ ↓ b bv₂
         → bv₃ ≡ bv₁ ∨ bv₂
         → σ ⊢ b₁ || b₂ ↓ b bv₃
  B-Lt : ∀ {σ a₁ a₂ i₁ i₂ bv}
         → σ ⊢ a₁ ⇓ i i₁
         → σ ⊢ a₂ ⇓ i i₂
         → bv ≡ i₁ < i₂
         → σ ⊢ a₁ ≺ a₂ ↓ b bv
  B-Eq : ∀ {σ a₁ a₂ i₁ i₂ bv}
         → σ ⊢ a₁ ⇓ i i₁
         → σ ⊢ a₂ ⇓ i i₂
         → bv ≡ i₁ == i₂
         → σ ⊢ a₁ ≈ a₂ ↓ b bv
  B-Le : ∀ {σ a₁ a₂ i₁ i₂ bv}
         → σ ⊢ a₁ ⇓ i i₁
         → σ ⊢ a₂ ⇓ i i₂
         → bv ≡ i₁ <= i₂
         → σ ⊢ a₁ ≼ a₂ ↓ b bv

data _changes_to_ : Com → Store → Store → Set where
  C-Skip : ∀ {σ}
           → skip changes σ to σ
  C-Assign : ∀ {σ₁ σ₂ a i₁ x}
             → σ₁ ⊢ a ⇓ i i₁
             → σ₂ ≡ σ₁ 〖 i i₁ ╱ x 〗
             → (x ≔ a) changes σ₁ to σ₂
  C-Seq : ∀ {c₁ c₂ σ₁ σ₂ σ₃}
          → c₁ changes σ₁ to σ₂
          → c₂ changes σ₂ to σ₃
          → (c₁ >> c₂) changes σ₁ to σ₃
  C-IfT : ∀ {σ₁ σ₂ b₁ c₁ c₂}
          → σ₁ ⊢ b₁ ↓ b true
          → c₁ changes σ₁ to σ₂
          → (if b₁ then c₁ else c₂) changes σ₁ to σ₂
  C-IfF : ∀ {σ₁ σ₂ b₁ c₁ c₂}
          → σ₁ ⊢ b₁ ↓ b false
          → c₂ changes σ₁ to σ₂
          → (if b₁ then c₁ else c₂) changes σ₁ to σ₂
  C-WhileT : ∀ {σ₁ σ₂ σ₃ b₁ c}
             → σ₁ ⊢ b₁ ↓ b true
             → c changes σ₁ to σ₂
             → (while b₁ 𝑑𝑜 c) changes σ₂ to σ₃
             → (while b₁ 𝑑𝑜 c) changes σ₁ to σ₃
  C-WhileF : ∀ {σ b₁ c}
             → σ ⊢ b₁ ↓ b false
             → (while b₁ 𝑑𝑜 c) changes σ to σ
