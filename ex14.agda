module ex14 where

open import BCoPL.While
open import BCoPL.Show.While

q151 : skip changes ● ⊱ ("s" , i (+ 0)) to ● ⊱ ("s" , i (+ 0))
q151 = C-Skip
{-
skip changes s = 0 to s = 0 by C-Skip {};
-}

q152 : "x" ≔ i (+ 1) changes ● ⊱ ("x" , i (+ 0)) to ● ⊱ ("x" , i (+ 1))
q152 = C-Assign A-Const refl
{-
x:=1 changes x = 0 to x = 1 by C-Assign {
  x = 0 |- 1 evalto 1 by A-Const {};
};
-}

