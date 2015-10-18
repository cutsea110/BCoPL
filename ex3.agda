module ex3 where

open import BCoPL.EvalML1

-- excercise 3.1
ex-3-1-1 : i (+ 3) ⊕ i (+ 5) ⇓ i (+ 8)
ex-3-1-1 = E-Plus E-Int E-Int (B-Plus refl)

ex-3-1-2 : i (+ 8) ⊝ i (+ 2) ⊝ i (+ 3) ⇓ i (+ 3)
ex-3-1-2 = E-Minus (E-Minus E-Int E-Int (B-Minus refl)) E-Int (B-Minus refl)

ex-3-1-3 : (i (+ 4) ⊕ i (+ 5)) ⊛ (i (+ 1) ⊝ i (+ 10)) ⇓ i (-[1+ 80 ])
ex-3-1-3 = E-Times (E-Plus E-Int E-Int (B-Plus refl)) (E-Minus E-Int E-Int (B-Minus refl)) (B-Times refl)

ex-3-1-4 : if i (+ 4) ≺ i (+ 5) then i (+ 2) ⊕ i (+ 3) else i (+ 8) ⊛ i (+ 8) ⇓ i (+ 5)
ex-3-1-4 = E-IfT (E-Lt E-Int E-Int (B-Lt refl)) (E-Plus E-Int E-Int (B-Plus refl))

ex-3-1-5 : i (+ 3) ⊕ (if i (-[1+ 22 ]) ≺ i (-[1+ 1 ]) ⊛ i (+ 8) then i (+ 8) else i (+ 2) ⊕ i (+ 4)) ⇓ i (+ 11)
ex-3-1-5 = E-Plus E-Int (E-IfT (E-Lt E-Int (E-Times E-Int E-Int (B-Times refl)) (B-Lt refl)) E-Int) (B-Plus refl)

ex-3-1-6 : i (+ 3) ⊕ (if i (-[1+ 22 ]) ≺ i (-[1+ 1 ]) ⊛ i (+ 8) then i (+ 8) else i (+ 2)) ⊕ i (+ 4) ⇓ i (+ 15)
ex-3-1-6 = E-Plus (E-Plus E-Int (E-IfT (E-Lt E-Int (E-Times E-Int E-Int (B-Times refl)) (B-Lt refl)) E-Int) (B-Plus refl)) E-Int (B-Plus refl)
