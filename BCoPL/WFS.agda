module BCoPL.WFS where

open import Level
open import Relation.Binary.PropositionalEquality as PropEq

-- definition 2.41
data _∈_ {ℓ} {A : Set ℓ} (x : A) (B : Set ℓ) : Set (suc ℓ) where
  in-eq : A ≡ B → x ∈ B

data _⊆_ {ℓ} (A : Set ℓ) (B : Set ℓ) : Set where
  -- TODO

record Well-Founded-Set (X : Set) (_≺_ : X → X → Set) : Set where
  -- TODO
