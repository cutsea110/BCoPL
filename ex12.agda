module ex12 where

open import BCoPL.EvalContML4

q130 : ● ⊢ ℓet "x" ≔ i (+ 1) ⊕ i (+ 2) ιn var "x" ⊛ i (+ 4) ≫ ⋆ ⇓ i (+ 12)
q130 = E-Let (E-BinOp (E-Int (C-EvalR (E-Int (C-Plus (B-Plus refl) (C-LetBody (E-BinOp (E-Var refl (C-EvalR (E-Int (C-Times (B-Times refl) C-Ret)))))))))))

q131 : ● ⊢ ℓet "add1" ≔ fun "x" ⇒ var "x" ⊕ i (+ 1) ιn app (var "add1") (i (+ 3)) ≫ ⋆ ⇓ i (+ 4)
q131 = E-Let (E-Fun (C-LetBody (E-App (E-Var refl (C-EvalArg (E-Int (C-EvalFun (E-BinOp (E-Var refl (C-EvalR (E-Int (C-Plus (B-Plus refl) C-Ret))))))))))))

q132 : ● ⊢ ℓetrec "fact" ≔fun "n" ⇒
                  if var "n" ≺ i (+ 2) then i (+ 1) else var "n" ⊛ app (var "fact") (var "n" ⊝ i (+ 1)) ιn
            app (var "fact") (i (+ 3)) ≫ ⋆ ⇓ i (+ 6)
q132 = E-LetRec (E-App (E-Var refl (C-EvalArg (E-Int (C-EvalFunR (E-If (E-BinOp (E-Var refl (C-EvalR (E-Int (C-Lt (B-Lt refl) (C-IfF (E-BinOp (E-Var refl (C-EvalR (E-App (E-Var refl (C-EvalArg (E-BinOp (E-Var refl (C-EvalR (E-Int (C-Minus (B-Minus refl) (C-EvalFunR (E-If (E-BinOp (E-Var refl (C-EvalR (E-Int (C-Lt (B-Lt refl) (C-IfF (E-BinOp (E-Var refl (C-EvalR (E-App (E-Var refl (C-EvalArg (E-BinOp (E-Var refl (C-EvalR (E-Int (C-Minus (B-Minus refl) (C-EvalFunR (E-If (E-BinOp (E-Var refl (C-EvalR (E-Int (C-Lt (B-Lt refl) (C-IfT (E-Int (C-Times (B-Times refl) (C-Times (B-Times refl) C-Ret)))))))))))))))))))))))))))))))))))))))))))))))))))))

q133 : ● ⊱ ("k" , ⟪ ⟦ i (+ 3) ⊕⋆ ⟧≫ ⋆ ⟫) ⊢ i (+ 1) ⊕ app (var "k") (i (+ 2)) ≫ ⋆ ⇓ i (+ 5)
q133 = E-BinOp (E-Int (C-EvalR (E-App (E-Var refl (C-EvalArg (E-Int (C-EvalFunC (C-Plus (B-Plus refl) C-Ret))))))))
