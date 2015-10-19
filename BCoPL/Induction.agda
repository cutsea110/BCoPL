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

-- principal 2.33
open import BCoPL.EvalNatExp

induction-Exp : {P : Exp → Set} →
                ((n : ℕ) → P (Nat n)) →
                ((e₁ e₂ : Exp) → P e₁ × P e₂ → P (e₁ ⊕ e₂)) →
                ((e₁ e₂ : Exp) → P e₁ × P e₂ → P (e₁ ⊛ e₂)) →
                ((e : Exp) → P e)
induction-Exp nat plus times (Nat n) = nat n
induction-Exp nat plus times (e₁ ⊕ e₂)
  = plus e₁ e₂ ((induction-Exp nat plus times e₁) , induction-Exp nat plus times e₂)
induction-Exp {P} nat plus times (e₁ ⊛ e₂)
  = times e₁ e₂ ((induction-Exp nat plus times e₁) , (induction-Exp nat plus times e₂))

-- principal 2.37
open import BCoPL.CompareNat1 renaming (_is-less-than_ to _is-less-than1_)

induction-CompareNat1 : {P : ∀ n₁ n₂ → (D : n₁ is-less-than1 n₂) → Set} →
                        (∀ n → P n (S n) (L-Succ {n})) × (∀ n₁ n₂ n₃ →
                                                            (D₁ : n₁ is-less-than1 n₂) →
                                                            (D₂ : n₂ is-less-than1 n₃) →
                                                            P n₁ n₂ D₁ × P n₂ n₃ D₂ →
                                                            P n₁ n₃ (L-Trans {n₁} {n₂} {n₃} D₁ D₂)) →
                        ∀ n₁ n₂ → (D : n₁ is-less-than1 n₂) → P n₁ n₂ D
induction-CompareNat1 (p₁ , p₂) n₁ .(S n₁) (L-Succ .{n₁}) = p₁ n₁
induction-CompareNat1 (p₁ , p₂) n₁ n₂ (L-Trans .{n₁} {n₃} .{n₂} D₁ D₂)
  = p₂ n₁ n₃ n₂ D₁ D₂ (induction-CompareNat1 (p₁ , p₂) n₁ n₃ D₁ , induction-CompareNat1 (p₁ , p₂) n₃ n₂ D₂)

-- principal 2.38
induction-CompareNat1′ : {P : (n₁ n₂ : ℕ) → {D : n₁ is-less-than1 n₂} → Set} →
                        (∀ n → P n (S n) {L-Succ}) × (∀ n₁ n₂ n₃ → ∀ {D₁ D₂} →
                                                        P n₁ n₂ {D₁} × P n₂ n₃ {D₂} → P n₁ n₃ {L-Trans D₁ D₂}) →
                        ∀ n₁ n₂ → {D : n₁ is-less-than1 n₂} → P n₁ n₂ {D}
induction-CompareNat1′ (p₁ , p₂) n₁ .(S n₁) {L-Succ} = p₁ n₁
induction-CompareNat1′ (p₁ , p₂) n₁ n₂ {L-Trans .{n₁} {n₃} .{n₂} D₁ D₂}
  = p₂ n₁ n₃ n₂ (induction-CompareNat1′ (p₁ , p₂) n₁ n₃ , induction-CompareNat1′ (p₁ , p₂) n₃ n₂)

induction-CompareNat1″ : {P : ∀ {n₁ n₂} → (D : n₁ is-less-than1 n₂) → Set} →
                         (∀ {n} → P {n} {S n} L-Succ) × (∀ {n₁ n₂ n₃} → ∀ D₁ D₂ →
                                                           P {n₁} {n₂} D₁ × P {n₂} {n₃} D₂ → P (L-Trans D₁ D₂)) →
                         ∀ {n₁ n₂} → (D : n₁ is-less-than1 n₂) → P D
induction-CompareNat1″ (p₁ , p₂) L-Succ = p₁
induction-CompareNat1″ (p₁ , p₂) (L-Trans D₁ D₂) = p₂ D₁ D₂ ((induction-CompareNat1″ (p₁ , p₂) D₁) , induction-CompareNat1″ (p₁ , p₂) D₂)

-- principal 2.39
open import BCoPL.CompareNat2 renaming (_is-less-than_ to _is-less-than2_)

induction-CompareNat2 :  {P : (n₁ n₂ : ℕ) → (D : n₁ is-less-than2 n₂) → Set} →
                        (∀ n → P Z (S n) (L-Zero {n})) × (∀ n₁ n₂ → (D : n₁ is-less-than2 n₂) →
                                                            P n₁ n₂ D → P (S n₁) (S n₂) (L-SuccSucc D)) →
                        ∀ n₁ n₂ → (D : n₁ is-less-than2 n₂) → P n₁ n₂ D
induction-CompareNat2 (p₁ , p₂) .0 ._ (L-Zero {n}) = p₁ n

induction-CompareNat2 (p₁ , p₂) ._ ._ (L-SuccSucc {n₁} {n₂} D) = p₂ n₁ n₂ D (induction-CompareNat2 (p₁ , p₂) n₁ n₂ D)

induction-CompareNat2′ : {P : (n₁ n₂ : ℕ) → {D : n₁ is-less-than2 n₂} → Set} →
                        (∀ n → P Z (S n) {L-Zero}) × (∀ n₁ n₂ → ∀ {D₁} →
                                                        P n₁ n₂ {D₁} → P (S n₁) (S n₂) {L-SuccSucc D₁}) →
                        ∀ n₁ n₂ → {D : n₁ is-less-than2 n₂} → P n₁ n₂ {D}
induction-CompareNat2′ (p₁ , p₂) .0 ._ {L-Zero {n}} = p₁ n
induction-CompareNat2′ (p₁ , p₂) ._ ._ {L-SuccSucc {n₁} {n₂} D} = p₂ n₁ n₂ (induction-CompareNat2′ (p₁ , p₂) n₁ n₂)

induction-CompareNat2″ : {P : ∀ {n₁ n₂} → (D : n₁ is-less-than2 n₂) → Set} →
                        (∀ {n} → P {Z} {S n} L-Zero) × (∀ {n₁ n₂} → ∀ D → P {n₁} {n₂} D → P {S n₁} {S n₂} (L-SuccSucc D)) →
                        ∀ {n₁ n₂} → (D : n₁ is-less-than2 n₂) → P D
induction-CompareNat2″ (p₁ , p₂) L-Zero = p₁
induction-CompareNat2″ (p₁ , p₂) (L-SuccSucc D) = p₂ D (induction-CompareNat2″ (p₁ , p₂) D)

-- principal 2.40
open import BCoPL.CompareNat3 renaming (_is-less-than_ to _is-less-than3_)

induction-CompareNat3 : {P : (n₁ n₂ : ℕ) → (D : n₁ is-less-than3 n₂) → Set} →
                        (∀ n → P n (S n) (L-Succ {n})) × (∀ n₁ n₂ → (D : n₁ is-less-than3 n₂) →
                                                        P n₁ n₂ D → P n₁ (S n₂) (L-SuccR D)) →
                        ∀ n₁ n₂ → (D : n₁ is-less-than3 n₂) → P n₁ n₂ D
induction-CompareNat3 (p₁ , p₂) n₁ .(S n₁) L-Succ = p₁ n₁
induction-CompareNat3 (p₁ , p₂) n₁ ._ (L-SuccR .{n₁} {n₂} D) = p₂ n₁ n₂ D (induction-CompareNat3 (p₁ , p₂) n₁ n₂ D)

induction-CompareNat3′ : {P : (n₁ n₂ : ℕ) → {D : n₁ is-less-than3 n₂} → Set} →
                        (∀ n → P n (S n) {L-Succ}) × (∀ n₁ n₂ → ∀ {D₁} →
                                                        P n₁ n₂ {D₁} → P n₁ (S n₂) {L-SuccR D₁}) →
                        ∀ n₁ n₂ → {D : n₁ is-less-than3 n₂} → P n₁ n₂ {D}
induction-CompareNat3′ (p₁ , p₂) n₁ .(S n₁) {L-Succ} = p₁ n₁
induction-CompareNat3′ (p₁ , p₂) n₁ ._ {L-SuccR .{n₁} {n₂} D} = p₂ n₁ n₂ (induction-CompareNat3′ (p₁ , p₂) n₁ n₂)

induction-CompareNat3″ : {P : ∀ {n₁ n₂} → (D : n₁ is-less-than3 n₂) → Set} →
                        (∀ {n} → P {n} {S n} L-Succ) × (∀ {n₁ n₂} → ∀ D → P {n₁} {n₂} D → P {n₁} {S n₂} (L-SuccR D)) →
                        ∀ {n₁ n₂} → (D : n₁ is-less-than3 n₂) → P D
induction-CompareNat3″ (p₁ , p₂) L-Succ = p₁
induction-CompareNat3″ (p₁ , p₂) (L-SuccR D) = p₂ D (induction-CompareNat3″ (p₁ , p₂) D)

-- principal 3.3
open import BCoPL.EvalML1 renaming (Exp to Exp′)

induction-EvalML1 : {P : Exp′ → Set} →
                    (∀ n → P (i n)) →
                    (∀ v → P (b v)) →
                    (∀ e₁ e₂ _⊗_ → P e₁ × P e₂ → P (e₁ ⊗ e₂)) →
                    (∀ e₁ e₂ e₃ → P e₁ × P e₂ × P e₃ → P (if e₁ then e₂ else e₃)) →
                    ((e : Exp′) → P e)
induction-EvalML1 = {!!}
