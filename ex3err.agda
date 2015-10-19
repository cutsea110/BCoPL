module ex3err where

open import BCoPL.EvalML1Err
open import BCoPL.Show.EvalML1Err

-- excercise 3.3
ex-3-3-1 : i (+ 1) ⊕ b true ⊕ i (+ 2) ⇓ left error+
ex-3-3-1 = E-PlusErrorL (E-PlusBoolR E-Bool)
{-
((1 + true) + 2) evalto error by E-PlusErrorL {
  (1 + true) evalto error by E-PlusBoolR {
    true evalto true by E-Bool {};
  };
};
-}
ex-3-3-2 : if i (+ 2) ⊕ i (+ 3) then i (+ 1) else i (+ 3) ⇓ left error?
ex-3-3-2 = E-IfInt (E-Plus E-Int E-Int (B-Plus refl))
{-
if (2 + 3) then 1 else 3 evalto error by E-IfInt {
  (2 + 3) evalto 5 by E-Plus {
    2 evalto 2 by E-Int {};
    3 evalto 3 by E-Int {};
    2 plus 3 is 5 by B-Plus {};
  };
};
-}
ex-3-3-3 : if i (+ 3) ≺ i (+ 4) then i (+ 1) ≺ b true else i (+ 3) ⊝ b false ⇓ left error<
ex-3-3-3 = E-IfTError (E-Lt E-Int E-Int (B-Lt refl) , E-LtBoolR E-Bool)
{-
if (3 < 4) then (1 < true) else (3 - false) evalto error by E-IfTError {
  (3 < 4) evalto true by E-Lt {
    3 evalto 3 by E-Int {};
    4 evalto 4 by E-Int {};
    3 less than 4 is true by B-Lt {};
  };
  (1 < true) evalto error by E-LtBoolR {
    true evalto true by E-Bool {};
  };
};
-}
