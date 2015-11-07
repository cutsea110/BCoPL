module ex14 where

open import BCoPL.While

q151 : skip changes ● ⊱ ("s" , i (+ 0)) to ● ⊱ ("s" , i (+ 0))
q151 = C-Skip

q152 : "x" ≔ i (+ 1) changes ● ⊱ ("x" , i (+ 0)) to ● ⊱ ("x" , i (+ 1))
q152 = C-Assign A-Const refl
