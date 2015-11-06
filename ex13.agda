module ex13 where

open import BCoPL.EvalRefML3

q141 : ● ⊱ ("@l" , i (+ 2)) ╱ ● ⊱ ("x" , ℓ "@l") ⊢ ! (var "x") ⊕ i (+ 3) ⇓ i (+ 5) ╱ ● ⊱ ("@l" , i (+ 2))
q141 = E-Plus (E-Deref (E-Var refl) refl) E-Int (B-Plus refl)
