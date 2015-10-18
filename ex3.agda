module ex3 where

open import BCoPL.EvalML1

-- excercise 3.1
ex-3-1-1 : i (+ 3) ⊕ i (+ 5) ⇓ i (+ 8)
ex-3-1-1 = E-PLUS E-INT E-INT (B-PLUS refl)

ex-3-1-2 : i (+ 8) ⊝ i (+ 2) ⊝ i (+ 3) ⇓ i (+ 3)
ex-3-1-2 = E-MINUS (E-MINUS E-INT E-INT (B-MINUS refl)) E-INT (B-MINUS refl)

ex-3-1-3 : (i (+ 4) ⊕ i (+ 5)) ⊛ (i (+ 1) ⊝ i (+ 10)) ⇓ i (-[1+ 80 ])
ex-3-1-3 = E-TIMES (E-PLUS E-INT E-INT (B-PLUS refl)) (E-MINUS E-INT E-INT (B-MINUS refl)) (B-TIMES refl)

ex-3-1-4 : If i (+ 4) ≺ i (+ 5) Then i (+ 2) ⊕ i (+ 3) Else i (+ 8) ⊛ i (+ 8) ⇓ i (+ 5)
ex-3-1-4 = E-IFT (E-LT E-INT E-INT (B-LT refl)) (E-PLUS E-INT E-INT (B-PLUS refl))

ex-3-1-5 : i (+ 3) ⊕ (If i (-[1+ 22 ]) ≺ i (-[1+ 1 ]) ⊛ i (+ 8) Then i (+ 8) Else i (+ 2) ⊕ i (+ 4)) ⇓ i (+ 11)
ex-3-1-5 = E-PLUS E-INT (E-IFT (E-LT E-INT (E-TIMES E-INT E-INT (B-TIMES refl)) (B-LT refl)) E-INT) (B-PLUS refl)

ex-3-1-6 : i (+ 3) ⊕ (If i (-[1+ 22 ]) ≺ i (-[1+ 1 ]) ⊛ i (+ 8) Then i (+ 8) Else i (+ 2)) ⊕ i (+ 4) ⇓ i (+ 15)
ex-3-1-6 = E-PLUS (E-PLUS E-INT (E-IFT (E-LT E-INT (E-TIMES E-INT E-INT (B-TIMES refl)) (B-LT refl)) E-INT) (B-PLUS refl)) E-INT (B-PLUS refl)
