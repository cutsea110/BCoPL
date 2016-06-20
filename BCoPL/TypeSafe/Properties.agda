module BCoPL.TypeSafe.Properties where

open import Data.Empty using (⊥)
open import Data.Unit using (⊤)
open import BCoPL.TypeSafe

type-safety : ∀ {e τ r v} →
              ● ⊢ e ∶ τ × ● ⊢ e ⇓ r →
              r ≡ v × (τ ≡ int → v isℤ) × {!!} × {!!} × {!!}
type-safety = {!!}
