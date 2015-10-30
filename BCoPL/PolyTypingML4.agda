module BCoPL.PolyTypingML4 where

open import Data.Nat hiding (_<_; _+_; _*_) renaming (suc to S; zero to Z)
open import Data.List renaming ([] to ø; _∷_ to _◂_) public
open import Data.Product using (∃; proj₁) public

open import BCoPL.EvalML4 public

-- Types
TyParam = String

data Types : Set where
  type-error : Types
  ′ : TyParam → Types
  bool : Types
  int : Types
  _⇀_ : Types → Types → Types
  _list : Types → Types

data TyScheme : Set where
  t : Types → TyScheme
  _̣_ : List TyParam → Types → TyScheme

data TEnv : Set where
  ● : TEnv
  _⊱_ : TEnv → (Var × TyScheme) → TEnv

_〖_〗 : TEnv → Var → TyScheme
● 〖 x 〗 = t type-error
Γ ⊱ (y , e) 〖 x 〗 = y == x ¿ e ∶ Γ 〖 x 〗

private
  -- type substitution
  [_]⊲_ : List (Types × TyParam) → Types → Types
  [ τ/α ]⊲ type-error = type-error
  [ ø ]⊲ ′ α = ′ α
  [ (τi , αi) ◂ τ/α ]⊲ ′ α = αi == α ¿ τi ∶ [ τ/α ]⊲ ′ α
  [ τ/α ]⊲ bool = bool
  [ τ/α ]⊲ int = int
  [ τ/α ]⊲ (τ₁ ⇀ τ₂) = [ τ/α ]⊲ τ₁ ⇀ [ τ/α ]⊲ τ₂
  [ τ/α ]⊲ (τ list) = ([ τ/α ]⊲ τ) list

  _/=_ : TyParam → TyParam → Bool
  x /= y = not (x == y)

  elem : TyParam → List TyParam → Bool
  elem x ø = false
  elem x (y ◂ ys) = x == y ¿ true ∶ elem x ys

  _∩_ : List TyParam → List TyParam → List TyParam
  xs ∩ ø = ø
  xs ∩ (x ◂ ys) with elem x xs
  ... | true = x ◂ (filter (_/=_ x) xs ∩ ys)
  ... | false = xs ∩ ys

  _∪_ : List TyParam → List TyParam → List TyParam
  xs ∪ ø = xs
  xs ∪ x ◂ ys with elem x xs
  ... | true = xs ∪ ys
  ... | false = xs ++ [ x ] ∪ ys

  _╲_ : List TyParam → List TyParam → List TyParam
  xs ╲ ø = xs
  xs ╲ (y ◂ ys) with elem y xs
  ... | true = filter (_/=_ y) xs ╲ ys
  ... | false = xs ╲ ys

data _≽_ : TyScheme → Types → Set where
  raw : ∀ {τ} → t τ ≽ τ
  concretion : ∀ {τ τ₀ αs} → (∃ λ τs → [ zip τs αs ]⊲ τ₀ ≡ τ ) → αs ̣ τ₀ ≽ τ

FTVτ : Types → List TyParam
FTVτ type-error = ø
FTVτ (′ α) = [ α ]
FTVτ bool = ø
FTVτ int = ø
FTVτ (τ₁ ⇀ τ₂) = FTVτ τ₁ ∪ FTVτ τ₂
FTVτ (τ list) = FTVτ τ

FTVσ : TyScheme → List TyParam
FTVσ (t τ) = FTVτ τ
FTVσ (αs ̣ τ) = FTVτ τ ╲ αs

FTVΓ : TEnv → List TyParam
FTVΓ ● = ø
FTVΓ (Γ ⊱ (x , σ)) = FTVΓ Γ ∪ FTVσ σ

record ftv-proof : Set where
  -- p147 Definition 9.2
  ex1 : FTVτ (′ "a" ⇀ ′ "b" list) ≡ "a" ◂ [ "b" ]
  ex1 = refl
  ex2 : FTVσ ([ "a" ] ̣ ′ "a" ⇀ ′ "b" list) ≡ [ "b" ]
  ex2 = refl
  ex3 : FTVΓ (● ⊱ ("x" , [ "a" ] ̣ ′ "a" ⇀ ′ "b" list) ⊱ ("y" , t (′ "c" ⇀ ′ "c"))) ≡ "b" ◂ [ "c" ]
  ex3 = refl

record example-proof : Set where
  -- p147 Definition 9.1
  ex1 : [ "a" ] ̣ ′ "a" ⇀ ′ "a" ≽ int ⇀ int
  ex1 = concretion ([ int ] , refl)
  ex2 : [ "a" ] ̣ ′ "a" ⇀ ′ "a" ≽ bool list ⇀ bool list
  ex2 = concretion ([ bool list ] , refl)
  ex3 : [ "a" ] ̣ ′ "a" ⇀ ′ "a" ≽ (int ⇀ bool) ⇀ int ⇀ bool
  ex3 = concretion ([ int ⇀ bool ] , refl)
  ex4 : ("a" ◂ ("b" ◂ [ "c" ])) ̣ (′ "a" ⇀ ′ "b") ⇀ (′ "c" ⇀ ′ "a") ⇀ ′ "c" ⇀ ′ "b"
        ≽
        (int ⇀ bool) ⇀ (int list ⇀ int) ⇀ int list ⇀ bool
  ex4 = concretion (int ◂ (bool ◂ [ int list ]) , refl)


infixl 20 _⊱_

infix 10 _〖_〗
infix 9 _list
infixr 8 _⇀_
infix 7 _̣_
infix 6 _⊢_∶_ _≽_
infixl 4 _∪_

data _⊢_∶_ : TEnv → Exp → Types → Set where
  T-Int : ∀ {Γ n} → Γ ⊢ i n ∶ int
  T-Bool : ∀ {Γ v} → Γ ⊢ b v ∶ bool
  T-If : ∀ {Γ e₁ e₂ e₃ τ}
         → Γ ⊢ e₁ ∶ bool
         → Γ ⊢ e₂ ∶ τ
         → Γ ⊢ e₃ ∶ τ
         → Γ ⊢ if e₁ then e₂ else e₃ ∶ τ
  T-Plus : ∀ {Γ e₁ e₂}
           → Γ ⊢ e₁ ∶ int
           → Γ ⊢ e₂ ∶ int
           → Γ ⊢ e₁ ⊕ e₂ ∶ int
  T-Minus : ∀ {Γ e₁ e₂}
            → Γ ⊢ e₁ ∶ int
            → Γ ⊢ e₂ ∶ int
            → Γ ⊢ e₁ ⊝ e₂ ∶ int
  T-Times : ∀ {Γ e₁ e₂}
            → Γ ⊢ e₁ ∶ int
            → Γ ⊢ e₂ ∶ int
            → Γ ⊢ e₁ ⊛ e₂ ∶ int
  T-Lt : ∀ {Γ e₁ e₂}
         → Γ ⊢ e₁ ∶ int
         → Γ ⊢ e₂ ∶ int
         → Γ ⊢ e₁ ≺ e₂ ∶ bool
  T-Var : ∀ {Γ x σ τ}
          → Γ 〖 x 〗 ≡ σ
          → σ ≽ τ
          → Γ ⊢ var x ∶ τ
  T-Let : ∀ {Γ e₁ e₂ τ₁ τ₂ x σ αs}
          → Γ ⊢ e₁ ∶ τ₁
          → Γ ⊱ (x , σ) ⊢ e₂ ∶ τ₂
          → σ ≡ αs ̣ τ₁ × αs ∩ FTVΓ Γ ≡ ø
          → Γ ⊢ ℓet x ≔ e₁ ιn e₂ ∶ τ₂
  T-Abs : ∀ {Γ x τ₁ τ₂ e}
          → Γ ⊱ (x , t τ₁) ⊢ e ∶ τ₂
          → Γ ⊢ fun x ⇒ e ∶ τ₁ ⇀ τ₂
  T-App : ∀ {Γ e₁ e₂ τ₁ τ₂}
          → Γ ⊢ e₁ ∶ τ₁ ⇀ τ₂
          → Γ ⊢ e₂ ∶ τ₁
          → Γ ⊢ app e₁ e₂ ∶ τ₂
  T-LetRec : ∀ {Γ x y e₁ e₂ τ₁ τ₂ τ σ αs}
             → Γ ⊱ (x , t (τ₁ ⇀ τ₂)) ⊱ (y , t τ₁) ⊢ e₁ ∶ τ₂
             → Γ ⊱ (x , σ) ⊢ e₂ ∶ τ
             → σ ≡ αs ̣ τ₁ ⇀ τ₂ × αs ∩ FTVΓ Γ ≡ ø
             → Γ ⊢ ℓetrec x ≔fun y ⇒ e₁ ιn e₂ ∶ τ
  T-Nil : ∀ {Γ τ} → Γ ⊢ [] ∶ τ list
  T-Cons : ∀ {Γ τ e₁ e₂}
           → Γ ⊢ e₁ ∶ τ
           → Γ ⊢ e₂ ∶ τ list
           → Γ ⊢ e₁ ∷ e₂ ∶ τ list
  T-Match : ∀ {Γ e₁ e₂ e₃ τ τ' x y}
            → Γ ⊢ e₁ ∶ τ' list
            → Γ ⊢ e₂ ∶ τ
            → Γ ⊱ (x , t τ') ⊱ (y , t (τ' list)) ⊢ e₃ ∶ τ
            → Γ ⊢ match e₁ with[]⇒ e₂ ∣ x ∷ y ⇒ e₃ ∶ τ
