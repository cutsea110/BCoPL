module ex11 where

open import BCoPL.EvalContML1

q124 : i (+ 3) ≫ ⋆ ⇓ i (+ 3)
q124 = E-Int C-Ret

q125 : i (+ 5) ≫ ⟦ i (+ 3) ⊕⋆ ⟧≫ ⋆ ⇓ i (+ 8)
q125 = E-Int (C-Plus (B-Plus refl) C-Ret)

q126 : i (+ 3) ⊕ i (+ 5) ≫ ⋆ ⇓ i (+ 8)
q126 = E-BinOp (E-Int (C-EvalR (E-Int (C-Plus (B-Plus refl) C-Ret))))

q127 : (i (+ 4) ⊕ i (+ 5)) ⊛ (i (+ 1) ⊝ i (+ 10)) ≫ ⋆ ⇓ i -[1+ 80 ]
q127 = E-BinOp (E-BinOp (E-Int (C-EvalR (E-Int (C-Plus (B-Plus refl) (C-EvalR (E-BinOp (E-Int (C-EvalR (E-Int (C-Minus (B-Minus refl) (C-Times (B-Times refl) C-Ret))))))))))))

q128 : if i (+ 4) ≺ i (+ 5) then i (+ 2) ⊕ i (+ 3) else i (+ 8) ⊛ i (+ 8) ≫ ⋆ ⇓ i (+ 5)
q128 = E-If (E-BinOp (E-Int (C-EvalR (E-Int (C-Lt (B-Lt refl) (C-IfT (E-BinOp (E-Int (C-EvalR (E-Int (C-Plus (B-Plus refl) C-Ret)))))))))))
