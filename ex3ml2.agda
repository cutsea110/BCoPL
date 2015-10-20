module ex3ml2 where

open import BCoPL.EvalML2
open import Data.Empty using (⊥)

-- excercise 4.1
ex-4-1-1 : ∀ {x y} → {p : x ≢ y} →
         ● ⊱ (x , i (+ 3)) ⊱ (y , i (+ 2)) ⊢ var x ⇓ i (+ 3)
ex-4-1-1 {p = p} = E-Var2 p E-Var1

ex-4-1-2 : ∀ {x y} → {p : x ≢ y} →
         ● ⊱ (x , b true) ⊱ (y , i (+ 4)) ⊢ if var x then var y ⊕ i (+ 1) else var y ⊝ i (+ 1) ⇓ i (+ 5)
ex-4-1-2 {p = p} = E-IfT (E-Var2 p E-Var1) (E-Plus E-Var1 E-Int (B-Plus refl))

ex-4-1-3 : ∀ {x} →
         ● ⊢ ℓet x ≔ i (+ 1) ⊕ i (+ 2) ιn var x ⊛ i (+ 4) ⇓ i (+ 12)
ex-4-1-3 = E-Let (E-Plus E-Int E-Int (B-Plus refl))
                 (E-Times E-Var1 E-Int (B-Times refl))

ex-4-1-4 : ∀ {x y} → {p : x ≢ y} →
         ● ⊢ ℓet x ≔ i (+ 3) ⊛ i (+ 3) ιn ℓet y ≔ i (+ 4) ⊛ var x ιn var x ⊕ var y ⇓ i (+ 45)
ex-4-1-4 {p = p} = E-Let (E-Times E-Int E-Int (B-Times refl))
                         (E-Let (E-Times E-Int E-Var1 (B-Times refl))
                                (E-Plus (E-Var2 p E-Var1) E-Var1 (B-Plus refl)))

ex-4-1-5 : ∀ {x} →
         ● ⊱ (x , i (+ 3)) ⊢ ℓet x ≔ var x ⊛ i (+ 2) ιn var x ⊕ var x ⇓ i (+ 12)
ex-4-1-5 = E-Let (E-Times E-Var1 E-Int (B-Times refl))
                 (E-Plus E-Var1 E-Var1 (B-Plus refl))
