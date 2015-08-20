module BCoPL.Induction where

open import Data.Fin renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (to-from)
open import Data.Product using (∃; _,_; _×_)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality

open import BCoPL.Nat hiding (_<_)

-- principal 2.29
-- mathematical induction
inductionℕ : {P : ℕ → Set} → P Z × ((n : ℕ) → P n → P (S n)) → ((n : ℕ) → P n)
inductionℕ (base , step) Z = base
inductionℕ (base , step) (S n) = step n (inductionℕ (base , step) n)

-- principal 2.30
-- course of values induction
-- ref.) http://www.cs.bham.ac.uk/~mhe/papers/msfp2010/MSFP2010/agda/course-of-values.agda
--
cov-inductionℕ : {P : ℕ → Set} → ((k : ℕ) → ((j : Fin k) → P (toℕ j)) → P k) → ((n : ℕ) → P n)
cov-inductionℕ {P} f n = lemma₁ n (lemma₀ (S n))
  where
    lemma₀ : (n : ℕ) → ((k : Fin n) → P (toℕ k))
    lemma₀ = inductionℕ (base , step)
      where
        append : ∀ {P n} → ((i : Fin n) → P (toℕ i)) → P n → (i : Fin (S n)) → P (toℕ i)
        append {P} {Z} s a fzero = a
        append {P} {Z} s a (fsuc ())
        append {P} {S k} s a fzero = s fzero
        append {P} {S k} s a (fsuc j) = append {λ n → P (S n)} {k} (λ i → s (fsuc i)) a j
        base : (i : Fin Z) → P (toℕ i)
        base = λ ()
        step : (n : ℕ) → ((i : Fin n) → P (toℕ i)) → ((i : Fin (S n)) → P (toℕ i))
        step n s = append {P} s (f n s)

    lemma₁ : (n : ℕ) → ((k : Fin (S n)) → P (toℕ k)) → P n
    lemma₁ n s = subst P (to-from n) (s (fromℕ n))
