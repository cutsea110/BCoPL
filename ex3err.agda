module ex3err where

open import BCoPL.EvalML1Err

-- excercise 3.3
ex-3-3-1 : i (+ 1) ⊕ b true ⊕ i (+ 2) ⇓ left error+
ex-3-3-1 = E-PlusErrorL (E-PlusBoolR E-Bool)

ex-3-3-2 : if i (+ 2) ⊕ i (+ 3) then i (+ 1) else i (+ 3) ⇓ left error?
ex-3-3-2 = E-IfInt (E-Plus E-Int E-Int (B-Plus refl))

ex-3-3-3 : if i (+ 3) ≺ i (+ 4) then i (+ 1) ≺ b true else i (+ 3) ⊝ b false ⇓ left error<
ex-3-3-3 = E-IfT (E-Lt E-Int E-Int (B-Lt refl)) (E-LtBoolR E-Bool)
