module BCoPL.Induction where

open import Data.Fin renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (to-from)
open import Data.Product using (∃; _,_; _×_)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality

open import BCoPL.Nat hiding (_<_)

-- principal 2.32(2.29)
-- Peano natural number induction (mathematical induction)
inductionℕ : {P : ℕ → Set} → P Z × ((n : ℕ) → P n → P (S n)) → ((n : ℕ) → P n)
inductionℕ (base , step) Z = base
inductionℕ (base , step) (S n) = step n (inductionℕ (base , step) n)

-- principal 2.30
-- course of values induction
-- ref.) http://www.cs.bham.ac.uk/~mhe/papers/msfp2010/MSFP2010/agda/course-of-values.agda
--
append : {P : ℕ → Set} {n : ℕ} → ((i : Fin n) → P (toℕ i)) → P n → (i : Fin (S n)) → P (toℕ i)
append {P} {Z} s a fzero = a
append {P} {Z} s a (fsuc ())
append {P} {S k} s a fzero = s fzero
append {P} {S k} s a (fsuc j) = append {P ∘ S} {k} (s ∘ fsuc) a j

cov-inductionℕ : {P : ℕ → Set} → ((k : ℕ) → ((j : Fin k) → P (toℕ j)) → P k) → ((n : ℕ) → P n)
cov-inductionℕ {P} f n = lemma₁ n (lemma₀ (S n))
  where
    lemma₀ : (n : ℕ) → ((k : Fin n) → P (toℕ k))
    lemma₀ = inductionℕ (base , step)
      where
        base : (i : Fin Z) → P (toℕ i)
        base = λ ()
        step : (n : ℕ) → ((i : Fin n) → P (toℕ i)) → ((i : Fin (S n)) → P (toℕ i))
        step n s = append {P} s (f n s)

    lemma₁ : (n : ℕ) → ((k : Fin (S n)) → P (toℕ k)) → P n
    lemma₁ n s = subst P (to-from n) (s (fromℕ n))

-- principal 2.32
a×b→ind : {P : ℕ → Set} → P Z × ((n : ℕ) → P n → P (S n)) → ((n : ℕ) → P n)
a×b→ind = inductionℕ
ind→a×b : {P : ℕ → Set} → ((n : ℕ) → P n) → P Z × ((n : ℕ) → P n → P (S n))
ind→a×b {P} f = f Z , (λ n _ → f (S n)) -- proof automatically but why? Plz, stop and think a little.
