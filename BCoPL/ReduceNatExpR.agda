module BCoPL.ReduceNatExpR where

open import BCoPL.EvalNatExp public

infixr 3 _-d->_
data _-d->_ : Exp → Exp → Set where
  DR-Plus : ∀ {n₁ n₂ n₃} → n₁ plus n₂ is n₃ → Nat n₁ ⊕ Nat n₂ -d-> Nat n₃
  DR-Times : ∀ {n₁ n₂ n₃} → n₁ times n₂ is n₃ → Nat n₁ ⊛ Nat n₂ -d-> Nat n₃
  DR-PlusL : ∀ {e₁ e₂ e₂′} → e₂ -d-> e₂′ → e₁ ⊕ e₂ -d-> e₁ ⊕ e₂′
  DR-PlusR : ∀ {e₁ e₁′ n₂} → e₁ -d-> e₁′ → e₁ ⊕ Nat n₂ -d-> e₁′ ⊕ Nat n₂
  DR-TimesL : ∀ {e₁ e₂ e₂′} → e₂ -d-> e₂′ → e₁ ⊛ e₂ -d-> e₁ ⊛ e₂′
  DR-TimesR : ∀ {e₁ e₁′ n₂} → e₁ -d-> e₁′ → e₁ ⊛ Nat n₂ -d-> e₁′ ⊛ Nat n₂
