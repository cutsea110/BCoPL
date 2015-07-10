module BCoPL.ReduceNatExp where

open import BCoPL.EvalNatExp public

infixr 3 _⟶_
data _⟶_ : Exp → Exp → Set where
  R-Plus : ∀ {n₁ n₂ n₃} → n₁ plus n₂ is n₃ → Nat n₁ ⊕ Nat n₂ ⟶ Nat n₃
  R-Times : ∀ {n₁ n₂ n₃} → n₁ times n₂ is n₃ → Nat n₁ ⊛ Nat n₂ ⟶ Nat n₃
  R-PlusL : ∀ {e₁ e₁′ e₂} → e₁ ⟶ e₁′ → e₁ ⊕ e₂ ⟶ e₁′ ⊕ e₂
  R-PlusR : ∀ {e₁ e₂ e₂′} → e₂ ⟶ e₂′ → e₁ ⊕ e₂ ⟶ e₁ ⊕ e₂′
  R-TimesL : ∀ {e₁ e₁′ e₂} → e₁ ⟶ e₁′ → e₁ ⊛ e₂ ⟶ e₁′ ⊛ e₂
  R-TimesR : ∀ {e₁ e₂ e₂′} → e₂ ⟶ e₂′ → e₁ ⊛ e₂ ⟶ e₁ ⊛ e₂′

infixr 3 _-*->_
data _-*->_ : Exp → Exp → Set where
  MR-Zero : ∀ {e} → e -*-> e
  MR-One : ∀ {e e′} → e ⟶ e′ → e -*-> e′
  MR-Multi : ∀ {e e′ e″} → e -*-> e′ → e′ -*-> e″ → e -*-> e″

infixr 3 _-d->_
data _-d->_ : Exp → Exp → Set where
  DR-Plus : ∀ {n₁ n₂ n₃} → n₁ plus n₂ is n₃ → Nat n₁ ⊕ Nat n₂ -d-> Nat n₃
  DR-Times : ∀ {n₁ n₂ n₃} → n₁ times n₂ is n₃ → Nat n₁ ⊛ Nat n₂ -d-> Nat n₃
  DR-PlusL : ∀ {e₁ e₁′ e₂} → e₁ -d-> e₁′ → e₁ ⊕ e₂ -d-> e₁′ ⊕ e₂
  DR-PlusR : ∀ {n₁ e₂ e₂′} → e₂ -d-> e₂′ → Nat n₁ ⊕ e₂ -d-> Nat n₁ ⊕ e₂′
  DR-TimesL : ∀ {e₁ e₁′ e₂} → e₁ -d-> e₁′ → e₁ ⊛ e₂ -d-> e₁′ ⊛ e₂
  DR-TimesR : ∀ {n₁ e₂ e₂′} → e₂ -d-> e₂′ → Nat n₁ ⊛ e₂ -d-> Nat n₁ ⊛ e₂′
